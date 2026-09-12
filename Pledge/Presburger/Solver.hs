module Pledge.Presburger.Solver
    ( -- * Solver result
      SolverResult(..)
    , checkPPred
    , isValidUnderHeapInvariant
    ) where

import Control.Exception (try, SomeException)
import Data.List (nub, intercalate)
import qualified Data.Map.Strict as Map
import Data.SBV hiding (Unsatisfiable)
import Pledge.Presburger

-- ── Result type ───────────────────────────────────────────────────────────────

-- | A witness heap maps each address to its concrete integer value.
data SolverResult
    = Satisfied (Map.Map Addr Integer)  -- ^ SAT: a concrete witness heap
    | Unsatisfiable                     -- ^ UNSAT: no heap satisfies the constraints
    | SolverUnknown String              -- ^ solver unavailable or timed out
    deriving (Eq)

instance Show SolverResult where
    show (Satisfied h)
        | Map.null h = "SAT  (no heap variables)"
        | otherwise  = "SAT  heap = { "
                    ++ intercalate ", " [ "h[" ++ show a ++ "] := " ++ show v
                                        | (a, v) <- Map.toList h ]
                    ++ " }"
    show Unsatisfiable       = "UNSAT"
    show (SolverUnknown msg) = "UNKNOWN (" ++ msg ++ ")"

-- ── Address / variable collection ─────────────────────────────────────────────

addrsInValues :: Values -> [Addr]
addrsInValues (ValAt a)  = [a]
addrsInValues (List vs)  = concatMap addrsInValues vs
addrsInValues _          = []

addrsInTerm :: Term -> [Addr]
addrsInTerm (Val v)     = addrsInValues v
addrsInTerm (Add s t)   = addrsInTerm s ++ addrsInTerm t
addrsInTerm (Neg t)     = addrsInTerm t
addrsInTerm (Mul _ t)   = addrsInTerm t

addrsInPred :: Pred -> [Addr]
addrsInPred PTrue        = []
addrsInPred PFalse       = []
addrsInPred (PLt  e1 e2) = addrsInTerm e1 ++ addrsInTerm e2
addrsInPred (PLe  e1 e2) = addrsInTerm e1 ++ addrsInTerm e2
addrsInPred (PEq  e1 e2) = addrsInTerm e1 ++ addrsInTerm e2
addrsInPred (PGt  e1 e2) = addrsInTerm e1 ++ addrsInTerm e2
addrsInPred (PGe  e1 e2) = addrsInTerm e1 ++ addrsInTerm e2
addrsInPred (PNot p)     = addrsInPred p
addrsInPred (PAnd p q)   = addrsInPred p ++ addrsInPred q
addrsInPred (POr  p q)   = addrsInPred p ++ addrsInPred q

-- | Free (non-heap) variable names mentioned in a 'Term' / 'Pred'.
varsInValues :: Values -> [String]
varsInValues (Var x)    = [x]
varsInValues (List vs)  = concatMap varsInValues vs
varsInValues _          = []

varsInTerm :: Term -> [String]
varsInTerm (Val v)     = varsInValues v
varsInTerm (Add s t)   = varsInTerm s ++ varsInTerm t
varsInTerm (Neg t)     = varsInTerm t
varsInTerm (Mul _ t)   = varsInTerm t

varsInPred :: Pred -> [String]
varsInPred PTrue        = []
varsInPred PFalse       = []
varsInPred (PLt  e1 e2) = varsInTerm e1 ++ varsInTerm e2
varsInPred (PLe  e1 e2) = varsInTerm e1 ++ varsInTerm e2
varsInPred (PEq  e1 e2) = varsInTerm e1 ++ varsInTerm e2
varsInPred (PGt  e1 e2) = varsInTerm e1 ++ varsInTerm e2
varsInPred (PGe  e1 e2) = varsInTerm e1 ++ varsInTerm e2
varsInPred (PNot p)     = varsInPred p
varsInPred (PAnd p q)   = varsInPred p ++ varsInPred q
varsInPred (POr  p q)   = varsInPred p ++ varsInPred q

-- ── SBV translation ───────────────────────────────────────────────────────────

-- | Only 'Num', 'ValAt' and 'Var' denote integers; any other 'Values'
-- reaching here (a 'Str', 'Bool', 'Unit' or 'List' used where an arithmetic
-- term was expected) is a modelling error in the caller, not something this
-- solver can make sense of.
valuesToSBV :: Map.Map Addr SInteger -> Map.Map String SInteger -> Values -> SInteger
valuesToSBV _  _  (Num n)   = fromIntegral n
valuesToSBV hv _  (ValAt a) = hv Map.! a
valuesToSBV _  vv (Var x)   = vv Map.! x
valuesToSBV _  _  v         = error ("Presburger.Solver: non-arithmetic value " ++ show v)

termToSBV :: Map.Map Addr SInteger -> Map.Map String SInteger -> Term -> SInteger
termToSBV hv vv (Val v)     = valuesToSBV hv vv v
termToSBV hv vv (Add s t)   = termToSBV hv vv s + termToSBV hv vv t
termToSBV hv vv (Neg t)     = negate (termToSBV hv vv t)
termToSBV hv vv (Mul k t)   = fromIntegral k * termToSBV hv vv t

predToSBV :: Map.Map Addr SInteger -> Map.Map String SInteger -> Pred -> SBool
predToSBV _  _  PTrue        = sTrue
predToSBV _  _  PFalse       = sFalse
predToSBV hv vv (PLt  e1 e2) = termToSBV hv vv e1 .<  termToSBV hv vv e2
predToSBV hv vv (PLe  e1 e2) = termToSBV hv vv e1 .<= termToSBV hv vv e2
predToSBV hv vv (PEq  e1 e2) = termToSBV hv vv e1 .== termToSBV hv vv e2
predToSBV hv vv (PGt  e1 e2) = termToSBV hv vv e1 .>  termToSBV hv vv e2
predToSBV hv vv (PGe  e1 e2) = termToSBV hv vv e1 .>= termToSBV hv vv e2
predToSBV hv vv (PNot p)     = sNot (predToSBV hv vv p)
predToSBV hv vv (PAnd p q)   = predToSBV hv vv p .&& predToSBV hv vv q
predToSBV hv vv (POr  p q)   = predToSBV hv vv p .|| predToSBV hv vv q

-- ── Solver ────────────────────────────────────────────────────────────────────
-- All ValAt references become unbounded integer variables; so does every
-- free 'Var'. Only the heap side is reported back in the witness — a 'Var'
-- is existentially quantified for satisfiability but is not part of the heap.

-- | Check satisfiability of a 'Pred' using an SMT solver.
-- Returns a concrete witness heap on SAT, 'Unsatisfiable' on UNSAT, or
-- 'SolverUnknown' if the solver is unavailable or times out.
checkPPred :: Pred -> IO SolverResult
checkPPred p = do
    let addrs  = nub (addrsInPred p)
        names  = nub (varsInPred p)
        varFor = ("h" ++) . show
    eResult <- try $ sat $ do
        hvars <- mapM (sInteger . varFor) addrs
        vvars <- mapM sInteger names
        let hv = Map.fromList (zip addrs hvars)
            vv = Map.fromList (zip names vvars)
        return (predToSBV hv vv p)
    case eResult of
        Left  (e :: SomeException) -> return (SolverUnknown (show e))
        Right result ->
            if modelExists result
                then do
                    let vals = [ (a, v)
                               | a <- addrs
                               , Just v <- [getModelValue (varFor a) result] ]
                    return (Satisfied (Map.fromList vals))
                else return Unsatisfiable

-- | Is a 'Pred' valid for every heap satisfying the standard domain
-- invariant that heap values are non-negative — i.e.\ does
-- @(⋀_a h[a] ≥ 0) ⟹ p@ hold?  Plain Presburger validity would reject e.g.
-- @h[a] = 0 ∨ h[a] > 0@ (it fails for @h[a] = -1@), even though every
-- reachable heap in this library only ever holds non-negative values
-- (see the 'GuardedRE' module header). Checked via Z3 by testing that the
-- invariant conjoined with @¬p@ is unsatisfiable.
isValidUnderHeapInvariant :: Pred -> IO Bool
isValidUnderHeapInvariant p = do
    let axiom = foldr (PAnd . nonNeg) PTrue (nub (addrsInPred p))
        nonNeg a = PGe (Val (ValAt a)) (Val (Num 0))
    result <- checkPPred (PAnd axiom (PNot p))
    return (result == Unsatisfiable)
