module Examples.GuardedRE.BoundedCounter where

import Prelude hiding ((<>))
import Control.Monad (replicateM_)
import Data.List (intercalate)
import Pledge
import Pledge.GuardedRE

-- ── Model ─────────────────────────────────────────────────────────────────────
-- A counter with a compile-time lower bound `lo` and upper bound `hi`.
--
-- The state monad `Counter` below *executes* the counter: `getC`/`putC` thread
-- the concrete value through the computation and never look at the bounds.
--
-- The `Pledge Counter (GuardedRE Term)` layer *enforces* the bounds.  Each
-- primitive reads the concrete counter out of the state monad, so it can emit a
-- Presburger guard over *literals* — `n' ≤ hi`, `n' ≥ lo` — that normalises to
-- `true` or `false` immediately.  A `false` guard collapses its disjunction, and
-- the collapse propagates through composition, turning the whole program's `pre`
-- (or `fut`) into the empty disjunction ⊥.
--
--   Trace constraint (RE):  `start` must precede every `inc` / `dec` / `read`.
--   Heap constraint (Pred): every step keeps `lo ≤ counter ≤ hi`.
--
-- This is the same problem the old version of this file flagged as *outside*
-- what GuardedRE can express.  It was outside only because the counter value
-- lived nowhere: a GuardedRE predicate is static, so `h[a] = 0` from `init` and
-- `h[a] > 0` from `dec` were conjoined into `false`.  Giving the value a home —
-- the state monad — fixes that: the predicate a step emits is already resolved
-- against the concrete value, so no two steps' predicates ever have to co-hold.

-- ── A tiny state monad ────────────────────────────────────────────────────────
-- `Counter` threads one mutable integer through a computation.  Ordinary state
-- monad: `getC` reads it, `putC` writes it, `modifyC` maps over it.

newtype Counter a = Counter { runCounter :: Int -> (a, Int) }

instance Functor Counter where
    fmap f (Counter g) = Counter $ \s -> let (a, s') = g s in (f a, s')

instance Applicative Counter where
    pure x = Counter (x,)
    Counter f <*> Counter g = Counter $ \s ->
        let (h, s')  = f s
            (a, s'') = g s'
        in (h a, s'')

instance Monad Counter where
    Counter g >>= k = Counter $ \s -> let (a, s') = g s in runCounter (k a) s'

getC :: Counter Int
getC = Counter $ \s -> (s, s)

putC :: Int -> Counter ()
putC n = Counter $ const ((), n)

modifyC :: (Int -> Int) -> Counter ()
modifyC f = Counter $ \s -> ((), f s)

-- ── Bounds and alphabet ───────────────────────────────────────────────────────

data Bounds = Bounds { lo :: Int, hi :: Int }

startE, readE :: Event Values
startE = Atom "start" (List [])
readE  = Atom "read"  (List [])

incE, decE :: Int -> Event Values
incE v = Atom "inc" (List [Num v])
decE v = Atom "dec" (List [Num v])

-- `lo ≤ v ≤ hi`, as a predicate over the (already concrete) new value.
inRange :: Bounds -> Int -> Pred
inRange b v = PAnd (PGe (Val (Num v)) (Val (Num (lo b)))) (PLe (Val (Num v)) (Val (Num (hi b))))

type CProg a = Pledge Counter (GuardedRE Values) a

-- ── Primitives ────────────────────────────────────────────────────────────────

-- Open a session.  Emits `start`; constrains nothing.
start :: CProg ()
start = Pledge $ pure
    ( ()
    , fromRE universe                 -- pre:  none
    , fromRE (Single startE)          -- post: the `start` event
    , fromRE universe                 -- fut:  none
    )

-- Increment.  The state monad performs the update unconditionally; the pre's
-- heap half is `n' ≤ hi` (over the concrete `n'`), its trace half is
-- `previously start`.  The fut records the end-state invariant `lo ≤ n' ≤ hi`.
increment :: Bounds -> CProg ()
increment b = Pledge $ do
    n <- getC
    let n' = n + 1
    putC n'
    pure ( ()
         , [ (PLe (Val (Num n')) (Val (Num (hi b))), previously startE) ]   -- pre
         , fromRE (Single (incE n'))                            -- post
         , [ (inRange b n', universe) ]                         -- fut
         )

-- Decrement.  Mirror image: the heap half of the pre is `n' ≥ lo`.
decrement :: Bounds -> CProg ()
decrement b = Pledge $ do
    n <- getC
    let n' = n - 1
    putC n'
    pure ( ()
         , [ (PGe (Val (Num n')) (Val (Num (lo b))), previously startE) ]   -- pre
         , fromRE (Single (decE n'))                            -- post
         , [ (inRange b n', universe) ]                         -- fut
         )

-- Read the counter out.  Requires a prior `start`; imposes no bound.
readCounter :: CProg Int
readCounter = Pledge $ do
    n <- getC
    pure ( n
         , fromRE (previously startE)     -- pre:  session opened
         , fromRE (Single readE)          -- post: the `read` event
         , fromRE universe                -- fut:  none
         )

-- ── Checking ──────────────────────────────────────────────────────────────────

-- Is a GuardedRE met by the empty preceding / following trace?  True iff, after
-- normalisation, some disjunct survives (its predicate is satisfiable) with a
-- nullable RE.  Every predicate we build here is over literals, so
-- 'normalizeGuarded' has already reduced it to `true` or dropped it — no solver
-- call is needed.
metByEmpty :: GuardedRE Values -> Bool
metByEmpty = any (nullable . snd) . normalizeGuarded

data Verdict = OK | Violation deriving (Eq, Show)

check :: String -> Int -> CProg a -> IO ()
check name s0 prog = do
    let ((_, preC, postC, futC), sFinal) = runCounter (runPledge prog) s0
        verdict | not (metByEmpty preC) = Violation   -- an unmet precondition
                | not (metByEmpty futC) = Violation   -- an out-of-range end state
                | otherwise             = OK
    putStrLn $ "=== " ++ name ++ " ==="
    putStrLn $ "final counter : " ++ show sFinal
    putStrLn $ "pre           : " ++ showG preC
    putStrLn $ "post          : " ++ showG postC
    putStrLn $ "fut           : " ++ showG futC
    putStrLn $ "verdict       : " ++ show verdict
    putStrLn ""
  where
    showG gre = case normalizeGuarded gre of
        [] -> "⊥ (no disjunct — constraint unsatisfiable)"
        ds -> intercalate "  ∨  "
                [ "[" ++ show p ++ "] " ++ show (normalize r) | (p, r) <- ds ]

-- ── Programs ──────────────────────────────────────────────────────────────────

b3 :: Bounds
b3 = Bounds 0 3

-- Good: the value stays inside 0..3 at every step.
withinBounds :: CProg Int
withinBounds = do
    start
    increment b3
    increment b3
    decrement b3
    readCounter

-- Bad: upper bound 2, but three increments push the value to 3.  The third
-- step's pre predicate `3 ≤ 2` is `false`, collapsing `pre` to ⊥.
overflow :: CProg ()
overflow = do
    let b = Bounds 0 2
    start
    increment b
    increment b
    increment b

-- Bad: a decrement takes the value to -1, below the lower bound 0.
underflow :: CProg ()
underflow = do
    start
    decrement b3

-- Good: fill to the ceiling and drain back to the floor, bound = n.
fillAndDrain :: Int -> CProg Int
fillAndDrain n = do
    let b = Bounds 0 n
    start
    replicateM_ n (increment b)
    replicateM_ n (decrement b)
    readCounter

-- Bad: operate without opening a session — the trace pre `previously start`
-- is not nullable, so `pre` is unmet by the empty preceding trace.
noStart :: CProg ()
noStart = increment b3

main :: IO ()
main = do
    check "withinBounds"     0 withinBounds
    check "overflow (bad)"   0 overflow
    check "underflow (bad)"  0 underflow
    check "fillAndDrain 3"   0 (fillAndDrain 3)
    check "noStart (bad)"    0 noStart
