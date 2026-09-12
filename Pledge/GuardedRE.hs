module Pledge.GuardedRE
    ( -- * Type
      GuardedRE
      -- * Construction
    , fromRE
    , fromPPred
      -- * Normalization
    , normalizeGuarded
    , normalizeGuardedSMT
      -- * Derivatives
    , deriveGuarded
      -- * Membership
    , nullableGuarded
    , checkGuarded
    ) where

import Data.List (nub)
import qualified Data.Map.Strict as Map
import Pledge.Core
import Pledge.Event (Event)
import Pledge.Presburger
import Pledge.Presburger.Solver
import Pledge.RE

-- | A disjunction of (Presburger predicate, regular expression) conjuncts,
-- enforcing heap invariants and trace-ordering obligations simultaneously.
--
-- A state @(heap, trace)@ satisfies @GuardedRE@ @gre@ iff there exists some
-- @(p, r)@ in @gre@ such that:
--
-- * @heap  |= p@   (Presburger predicate holds on the heap), and
-- * @trace ∈ L(r)@ (trace is in the language of the RE).
--
-- Within one conjunct the two dimensions are independent: the Presburger
-- predicate is static (not advanced by events), while the RE is advanced by
-- 'deriveGuarded'.  The list itself is what carries disjunction — a plain
-- conjunctive pair @(p, r)@ cannot express a heap-side "or".
type GuardedRE a = [(Pred, RE a)]

-- ── Construction ──────────────────────────────────────────────────────────────

-- | Lift a plain 'RE' into a 'GuardedRE' with no heap constraint (@Pred = PTrue@).
fromRE :: RE a -> GuardedRE a
fromRE r = [(PTrue, r)]

-- | Lift a plain 'Pred' into a 'GuardedRE' with no trace constraint
-- (any trace is accepted: @RE = Σ*@).
fromPPred :: Pred -> GuardedRE a
fromPPred p = [(p, top)]

-- ── Normalization ─────────────────────────────────────────────────────────────

-- | Normalize a 'GuardedRE':
--
--   * simplify every disjunct's predicate ('normalizePred') and RE ('normalize');
--   * drop disjuncts that can never hold — @PFalse@ (unsatisfiable heap guard)
--     or @∅@ (empty trace language) contribute nothing to the disjunction;
--   * merge disjuncts that share an (already-normalized) predicate by taking
--     the union of their REs, since @(p, r1) ∨ (p, r2) = (p, r1 ∪ r2)@;
--   * remove any duplicate disjuncts left over.
--
-- Keeps the list from growing unboundedly under repeated 'concatenation' /
-- 'conjunction' / quotient, whose cross products otherwise never shrink.
normalizeGuarded :: Eq a => GuardedRE a -> GuardedRE a
normalizeGuarded gre =
    nub [ (p, foldr1 (\r1 r2 -> normalize (Or r1 r2)) rs)
        | p <- nub (map fst simplified)
        , let rs = [ r | (p', r) <- simplified, p' == p ]
        ]
  where
    simplified =
        [ (p', r')
        | (p, r) <- gre
        , let p' = normalizePred p
              r' = normalize r
        , p' /= PFalse
        , r' /= Bot
        ]

-- | Like 'normalizeGuarded', but additionally collapses a group of disjuncts
-- that share an (already-normalized) RE when their predicates are jointly
-- exhaustive — e.g.\ a two-way heap split @h[a] = 0 ∨ h[a] > 0@, repeated
-- over every address mentioned, collapses to a single @(PTrue, r)@ disjunct.
--
-- @'normalizeGuarded'@ alone cannot see this: it only merges disjuncts whose
-- predicates are already /syntactically/ equal, whereas here the four
-- combinations of two addresses each split two ways are four distinct
-- predicates whose *disjunction* happens to be exhaustive.  Detecting that
-- needs an SMT call ('isValidUnderHeapInvariant'), hence the 'IO'.
normalizeGuardedSMT :: Eq a => GuardedRE a -> IO (GuardedRE a)
normalizeGuardedSMT gre =
    fmap concat (mapM collapse (groupByRE (normalizeGuarded gre)))
  where
    groupByRE xs =
        [ (r, [ p' | (p', r') <- xs, r' == r ])
        | r <- nub (map snd xs)
        ]

    collapse (r, [p]) = return [(p, r)]
    collapse (r, ps)  = do
        exhaustive <- isValidUnderHeapInvariant (foldr1 POr ps)
        return $ if exhaustive then [(PTrue, r)] else [ (p, r) | p <- ps ]

-- ── Derivatives ───────────────────────────────────────────────────────────────

-- | Advance the trace side of every disjunct by one event.
-- The 'PPred' component of each disjunct is static and is left unchanged.
deriveGuarded :: Eq a => Event a -> GuardedRE a -> GuardedRE a
deriveGuarded e = map (\(p, r) -> (p, normalize (derivative e r)))

-- ── Membership ────────────────────────────────────────────────────────────────

-- | Check whether @(heap, ε)@ satisfies a 'GuardedRE':
-- some disjunct's RE must be nullable and its 'Pred' must be satisfiable
-- under the concrete @heap@ assignment.  Uses Z3 via SBV.
nullableGuarded :: Map.Map Addr Int -> GuardedRE a -> IO Bool
nullableGuarded heap = go
  where
    go [] = return False
    go ((p, r) : rest)
        | not (nullable r) = go rest
        | otherwise = do
            result <- checkPPred (instantiate heap p)
            case result of
                Satisfied _ -> return True
                _           -> go rest

-- Instantiate a Pred by substituting concrete heap values for ValAt.
-- Any address not present in the map is left as a free variable.
instantiate :: Map.Map Addr Int -> Pred -> Pred
instantiate heap = go
  where
    subst (Val (ValAt a)) = Val (maybe (ValAt a) Num (Map.lookup a heap))
    subst (Val v)         = Val v        -- unaffected: not a heap address
    subst (Add e1 e2)     = Add (subst e1) (subst e2)
    subst (Neg e)         = Neg (subst e)
    subst (Mul k e)       = Mul k (subst e)

    go PTrue        = PTrue
    go PFalse       = PFalse
    go (PLt  e1 e2) = PLt  (subst e1) (subst e2)
    go (PLe  e1 e2) = PLe  (subst e1) (subst e2)
    go (PEq  e1 e2) = PEq  (subst e1) (subst e2)
    go (PGt  e1 e2) = PGt  (subst e1) (subst e2)
    go (PGe  e1 e2) = PGe  (subst e1) (subst e2)
    go (PNot q)     = PNot (go q)
    go (PAnd q1 q2) = PAnd (go q1) (go q2)
    go (POr  q1 q2) = POr  (go q1) (go q2)

-- | Check whether @(heap, trace)@ satisfies a 'GuardedRE'.
-- Folds 'deriveGuarded' over the trace and then calls 'nullableGuarded'.
checkGuarded :: Eq a => Map.Map Addr Int -> [Event a] -> GuardedRE a -> IO Bool
checkGuarded heap trace ext =
    nullableGuarded heap (foldl (flip deriveGuarded) ext trace)

-- ── Composable instance ───────────────────────────────────────────────────────
-- Lifts the RE algebra to GuardedRE: each operation is the cross product of
-- disjuncts, combined pairwise with the corresponding RE operation while
-- conjoining the Pred halves.

instance Eq a => Composable (GuardedRE a) where
    concatenation xs ys =
        [ (normalizePred (PAnd p1 p2), normalize (Seq r1 r2))
        | (p1, r1) <- xs, (p2, r2) <- ys
        ]
    conjunction xs ys =
        [ (normalizePred (PAnd p1 p2), normalize (And r1 r2))
        | (p1, r1) <- xs, (p2, r2) <- ys
        ]
    empty         = [(PTrue, Epsilon)]
    universe      = [(PTrue, top)]
    leftQuotient xs ys =
        [ (normalizePred (PAnd p1 p2), normalize (reLeftQuotient r1 r2))
        | (p1, r1) <- xs, (p2, r2) <- ys
        ]
    rightQuotient xs ys =
        [ (normalizePred (PAnd p1 p2), normalize (reRightQuotient r1 r2))
        | (p1, r1) <- xs, (p2, r2) <- ys
        ]
