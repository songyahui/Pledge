module Examples.UnitTest.PresburgerTest where

import Prelude hiding ((<>))
import Data.IORef
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Pledge.Presburger
import Pledge.Presburger.Solver

-- ── Helpers ───────────────────────────────────────────────────────────────────

-- Report pass/fail; increment counter; crash on first failure so the culprit is visible.
check :: IORef Int -> String -> Bool -> IO ()
check counter name result = do
    modifyIORef' counter (+1)
    case result of
        True  -> putStrLn $ "  PASS  " ++ name
        False -> error    $ "\n  FAIL  " ++ name

isSat :: SolverResult -> Bool
isSat (Satisfied _) = True
isSat _             = False

isUnsat :: SolverResult -> Bool
isUnsat Unsatisfiable = True
isUnsat _             = False

-- ── checkPPred ────────────────────────────────────────────────────────────────

test_checkPPred :: IORef Int -> IO ()
test_checkPPred counter = do
    putStrLn "\n── checkPPred ───────────────────────────────────────────────────"

    -- PTrue has no variables and is trivially satisfiable
    r0 <- checkPPred PTrue
    check counter "PTrue is SAT with empty heap" (r0 == Satisfied Map.empty)

    -- h[0] = 3  (equality with a literal)
    r1 <- checkPPred (PEq (Val (ValAt 0)) (Val (Num 3)))
    check counter "h[0] = 3 is SAT" (isSat r1)
    case r1 of
        Satisfied h -> check counter "h[0] = 3 witness value is 3"
                            (Map.lookup 0 h == Just 3)
        _           -> return ()

    -- h[0] < h[0]  (strict self-comparison — always false)
    r2 <- checkPPred (PLt (Val (ValAt 0)) (Val (ValAt 0)))
    check counter "h[0] < h[0] is UNSAT" (isUnsat r2)

    -- h[0] > 0 ∧ h[0] < 0  (contradictory bounds)
    r3 <- checkPPred (PAnd (PGt (Val (ValAt 0)) (Val (Num 0))) (PLt (Val (ValAt 0)) (Val (Num 0))))
    check counter "h[0] > 0 ∧ h[0] < 0 is UNSAT" (isUnsat r3)

    -- h[0] >= 5 ∧ h[0] <= 5  (forces h[0] = 5)
    r4 <- checkPPred (PAnd (PGe (Val (ValAt 0)) (Val (Num 5))) (PLe (Val (ValAt 0)) (Val (Num 5))))
    check counter "h[0] >= 5 ∧ h[0] <= 5 is SAT" (isSat r4)
    case r4 of
        Satisfied h -> check counter "h[0] >= 5 ∧ h[0] <= 5 witness is 5"
                            (Map.lookup 0 h == Just 5)
        _           -> return ()

    -- ¬(h[0] = h[0])  (negation of a tautology — always false)
    r5 <- checkPPred (PNot (PEq (Val (ValAt 0)) (Val (ValAt 0))))
    check counter "¬(h[0] = h[0]) is UNSAT" (isUnsat r5)

    -- h[0] + h[1] = 10 ∧ h[0] = 3  (two-variable system)
    r6 <- checkPPred (PAnd (PEq (Add (Val (ValAt 0)) (Val (ValAt 1))) (Val (Num 10)))
                           (PEq (Val (ValAt 0)) (Val (Num 3))))
    check counter "h[0] + h[1] = 10 ∧ h[0] = 3 is SAT" (isSat r6)
    case r6 of
        Satisfied h -> check counter "two-variable witness: h[1] = 7"
                            (Map.lookup 1 h == Just 7)
        _           -> return ()

    -- 2 * h[0] = 7  (no integer solution)
    r7 <- checkPPred (PEq (Mul 2 (Val (ValAt 0))) (Val (Num 7)))
    check counter "2*h[0] = 7 is UNSAT" (isUnsat r7)

-- ── Entry point ───────────────────────────────────────────────────────────────

main :: IO ()
main = do
    counter <- newIORef (0 :: Int)
    test_checkPPred counter
    n <- readIORef counter
    putStrLn $ "\n" ++ show n ++ " tests passed."
