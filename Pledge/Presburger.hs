-- | Linear-arithmetic terms and predicates over heap values, with a purely
-- structural normaliser (no solver).
module Pledge.Presburger
    ( Addr
    , Values(..)
    , Term(..)
    , Pred(..)
    , normalizePred
    ) where

import Data.List  (nub, delete, sortOn, intercalate)
import Data.Maybe (mapMaybe)

type Addr = Int

data Values
    = Var  String
    | ValAt Addr
    | Num  Int
    | Str  String
    | Bool Bool
    | Unit
    | List [Values]
    deriving (Eq, Ord)

instance Show Values where
    show (Var s)   = s
    show (ValAt a) = "h[" ++ show a ++ "]"
    show (Num n)   = show n
    show (Str s)   = "\"" ++ s ++ "\""
    show (Bool b)  = if b then "true" else "false"
    show Unit      = "()"
    show (List vs) = "[" ++ intercalate ", " (map show vs) ++ "]"

data Term
    = Val Values
    | Add Term Term
    | Neg Term
    | Mul Int Term  -- ^ @k · t@ — multiplication by an integer literal
    deriving (Eq)

instance Show Term where
    show (Val v) = show v
    show (Add t1 t2) = "(" ++ show t1 ++ " + " ++ show t2 ++ ")"
    show (Neg t) = "(-" ++ show t ++ ")"
    show (Mul k t) = "(" ++ show k ++ " * " ++ show t ++ ")"

data Pred
    = PTrue
    | PFalse
    | PLt  Term Term
    | PLe  Term Term
    | PEq  Term Term
    | PGt  Term Term
    | PGe  Term Term
    | PNot Pred
    | PAnd Pred Pred
    | POr  Pred Pred
    deriving (Eq)

instance Show Pred where
    show PTrue        = "true"
    show PFalse       = "false"
    show (PLt  e1 e2) = show e1 ++ " < "  ++ show e2
    show (PLe  e1 e2) = show e1 ++ " <= " ++ show e2
    show (PEq  e1 e2) = show e1 ++ " == " ++ show e2
    show (PGt  e1 e2) = show e1 ++ " > "  ++ show e2
    show (PGe  e1 e2) = show e1 ++ " >= " ++ show e2
    show (PNot p)     = "¬(" ++ show p ++ ")"
    show (PAnd p q)   = "(" ++ show p ++ ") ∧ (" ++ show q ++ ")"
    show (POr  p q)   = "(" ++ show p ++ ") ∨ (" ++ show q ++ ")"

-- | Constant-fold comparisons, drive negation inward (NNF), flatten and
-- deduplicate @∧@/@∨@, and propagate @h[a] == k@ equalities into siblings.
normalizePred :: Pred -> Pred
normalizePred PTrue      = PTrue
normalizePred PFalse     = PFalse
normalizePred (PLt a b)  = ineq True  a b
normalizePred (PLe a b)  = ineq False a b
normalizePred (PGt a b)  = ineq True  b a
normalizePred (PGe a b)  = ineq False b a
normalizePred (PEq a b)  = eqPred a b
normalizePred (PNot p)   = nnfNot (normalizePred p)
normalizePred (PAnd p q) = conj (normalizePred p) (normalizePred q)
normalizePred (POr  p q) = disj (normalizePred p) (normalizePred q)

-- | A term as a constant plus a sorted atom-to-coefficient map.
type TermNF = (Int, [(Values, Int)])

flattenT :: Bool -> Term -> TermNF
flattenT neg (Val (Num n)) = (sign neg * n, [])
flattenT neg (Val v)       = (0, [(v, sign neg)])
flattenT neg (Neg t)       = flattenT (not neg) t
flattenT neg (Add s t)     = addNF (flattenT neg s) (flattenT neg t)
flattenT neg (Mul k t)     =
    let (c, m) = flattenT False t
        s      = sign neg * k
    in canonNF (s * c, [ (v, s * n) | (v, n) <- m ])

sign :: Bool -> Int
sign neg = if neg then -1 else 1

addNF :: TermNF -> TermNF -> TermNF
addNF (c1, m1) (c2, m2) = canonNF (c1 + c2, foldr bump m1 m2)
  where
    bump (v, k) acc = case span ((/= v) . fst) acc of
        (pre, (_, k0) : post) -> pre ++ [ (v, k0 + k) | k0 + k /= 0 ] ++ post
        _                     -> (v, k) : acc

canonNF :: TermNF -> TermNF
canonNF (c, m) = (c, sortOn fst [ p | p@(_, k) <- m, k /= 0 ])

diffNF :: Term -> Term -> TermNF
diffNF a b = addNF (flattenT False a) (flattenT True b)

sides :: TermNF -> (Term, Term)
sides (c, m) = (build pos (max c 0), build neg (max (negate c) 0))
  where
    pos = [ (v, k)        | (v, k) <- m, k > 0 ]
    neg = [ (v, negate k) | (v, k) <- m, k < 0 ]
    build parts k =
        case concatMap (\(v, n) -> replicate n (Val v)) parts
               ++ [ Val (Num k) | k /= 0 ] of
            [] -> Val (Num 0)
            ts -> foldr1 Add ts

ineq :: Bool -> Term -> Term -> Pred
ineq strict a b = case diffNF a b of
    (c, []) -> if test c 0 then PTrue else PFalse
    nf      -> uncurry con (sides nf)
  where
    test = if strict then (<) else (<=)
    con  = if strict then PLt else PLe

eqPred :: Term -> Term -> Pred
eqPred a b = case orientNF (diffNF a b) of
    (0, [])               -> PTrue
    (_, [])               -> PFalse
    (0, [(x, 1), (y, -1)])
        | closed x, closed y -> PFalse
    nf                    -> uncurry PEq (sides nf)
  where
    closed (Var _)   = False
    closed (ValAt _) = False
    closed (List vs) = all closed vs
    closed _         = True

orientNF :: TermNF -> TermNF
orientNF nf@(c, m)
    | leadingNegative = (negate c, [ (v, negate k) | (v, k) <- m ])
    | otherwise       = nf
  where
    leadingNegative = case dropWhile (== 0) (map snd m ++ [c]) of
        k : _ -> k < 0
        []    -> False

nnfNot :: Pred -> Pred
nnfNot PTrue      = PFalse
nnfNot PFalse     = PTrue
nnfNot (PNot p)   = p
nnfNot (PLt a b)  = PLe b a
nnfNot (PLe a b)  = PLt b a
nnfNot (PAnd p q) = disj (nnfNot p) (nnfNot q)
nnfNot (POr  p q) = conj (nnfNot p) (nnfNot q)
nnfNot p          = PNot p

conj :: Pred -> Pred -> Pred
conj a b = reduceAnd (length cs + 1) cs
  where cs = nub (filter (/= PTrue) (flattenAnd a ++ flattenAnd b))

reduceAnd :: Int -> [Pred] -> Pred
reduceAnd fuel cs
    | PFalse `elem` cs || anyComplement cs = PFalse
    | fuel <= 0 || cs' == cs               = rebuild PAnd PTrue (dropAbsorbed flattenOr cs)
    | PFalse `elem` cs'                    = PFalse
    | otherwise                            = reduceAnd (fuel - 1) cs'
  where
    eqs     = mapMaybe asHeapEq cs
    subst c = normalizePred
                (substHeapEqs (maybe eqs (`delete` eqs) (asHeapEq c)) c)
    cs'     = nub (concatMap (filter (/= PTrue) . flattenAnd . subst) cs)

disj :: Pred -> Pred -> Pred
disj a b
    | PTrue `elem` ds || anyComplement ds = PTrue
    | otherwise = rebuild POr PFalse (dropAbsorbed flattenAnd ds)
  where ds = nub (filter (/= PFalse) (flattenOr a ++ flattenOr b))

dropAbsorbed :: (Pred -> [Pred]) -> [Pred] -> [Pred]
dropAbsorbed split cls = filter keep cls
  where
    keep c = case split c of
        parts@(_ : _ : _) -> not (any (`elem` cls) parts)
        _                 -> True

anyComplement :: [Pred] -> Bool
anyComplement xs = or [ negatesTo x == Just y | x <- xs, y <- xs ]

negatesTo :: Pred -> Maybe Pred
negatesTo (PLt a b) = Just (PLe b a)
negatesTo (PLe a b) = Just (PLt b a)
negatesTo (PEq a b) = Just (PNot (PEq a b))
negatesTo (PNot p)  = Just p
negatesTo _         = Nothing

flattenAnd :: Pred -> [Pred]
flattenAnd (PAnd p q) = flattenAnd p ++ flattenAnd q
flattenAnd PTrue      = []
flattenAnd p          = [p]

flattenOr :: Pred -> [Pred]
flattenOr (POr p q) = flattenOr p ++ flattenOr q
flattenOr PFalse    = []
flattenOr p         = [p]

rebuild :: (Pred -> Pred -> Pred) -> Pred -> [Pred] -> Pred
rebuild _  z [] = z
rebuild op _ xs = foldr1 op xs

asHeapEq :: Pred -> Maybe (Addr, Int)
asHeapEq (PEq a b) = case diffNF a b of
    (c, [(ValAt addr,  1)]) -> Just (addr, negate c)
    (c, [(ValAt addr, -1)]) -> Just (addr, c)
    _                       -> Nothing
asHeapEq _ = Nothing

substHeapEqs :: [(Addr, Int)] -> Pred -> Pred
substHeapEqs eqs = onTerms go
  where
    go (Val (ValAt a)) = maybe (Val (ValAt a)) (Val . Num) (lookup a eqs)
    go (Val v)         = Val v
    go (Neg t)         = Neg (go t)
    go (Add s t)       = Add (go s) (go t)
    go (Mul k t)       = Mul k (go t)

onTerms :: (Term -> Term) -> Pred -> Pred
onTerms f = go
  where
    go (PLt a b)  = PLt (f a) (f b)
    go (PLe a b)  = PLe (f a) (f b)
    go (PEq a b)  = PEq (f a) (f b)
    go (PNot p)   = PNot (go p)
    go (PAnd p q) = PAnd (go p) (go q)
    go (POr  p q) = POr  (go p) (go q)
    go p          = p
