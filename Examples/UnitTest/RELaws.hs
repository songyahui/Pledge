-- | QuickCheck tests for the 'Composable' laws on @RE Values@.
-- Run as part of the @pledge-main@ executable (see @Examples\/Main.hs@).
module Examples.UnitTest.RELaws where

import Prelude hiding ((<>))
import Control.Monad (replicateM, when)
import Data.IORef
import System.Exit (exitFailure)
import Test.QuickCheck
import Pledge

-- ── Fixed alphabet ─────────────────────────────────────────────────────────────

-- | Small fixed alphabet used for language-equality testing and RE generation.
testAlph :: [Event Values]
testAlph = [Atom "a" (List []), Atom "b" (List []), Atom "c" (List [])]

-- ── Language equality ──────────────────────────────────────────────────────────

-- | Test two REs for language equality over all words up to length 3.
-- Structural 'Eq' is insufficient: @Seq (Seq a b) c /= Seq a (Seq b c)@
-- structurally, but the two accept the same language.
langEq :: RE Values -> RE Values -> Bool
langEq r1 r2 = all (\w -> run r1 w == run r2 w) testWords
  where
    testWords    = concatMap (`replicateM` testAlph) [0 .. 3]
    run r []     = nullable r
    run r (e:es) = run (normalize (derivative e r)) es

-- ── Arbitrary instance ─────────────────────────────────────────────────────────

instance Arbitrary (RE Values) where
    arbitrary = sized genRE
      where
        genRE 0 = oneof [pure Bot, pure Epsilon, pure top, Single <$> elements testAlph]
        genRE n = oneof
            [ pure Bot
            , pure Epsilon
            , pure top
            , Single <$> elements testAlph
            , Seq  <$> genRE h <*> genRE h
            , Or   <$> genRE h <*> genRE h
            , And  <$> genRE h <*> genRE h
            , Star <$> genRE (n - 1)
            , Not  <$> genRE (n - 1)
            ]
          where h = n `div` 2
    shrink Bot         = []
    shrink Epsilon     = [Bot]
    shrink (Single _)  = [Bot, Epsilon]
    shrink (Not r)     = r : map Not  (shrink r)
    shrink (Star r)    = [Epsilon, r] ++ map Star (shrink r)
    shrink (Seq r1 r2) = [r1, r2] ++ [Seq r1' r2  | r1' <- shrink r1]
                                   ++ [Seq r1  r2' | r2' <- shrink r2]
    shrink (Or  r1 r2) = [r1, r2] ++ [Or  r1' r2  | r1' <- shrink r1]
                                   ++ [Or  r1  r2' | r2' <- shrink r2]
    shrink (And r1 r2) = [r1, r2] ++ [And r1' r2  | r1' <- shrink r1]
                                   ++ [And r1  r2' | r2' <- shrink r2]

-- ── Properties ─────────────────────────────────────────────────────────────────

-- | @(·)@ is associative: @(x · y) · z = x · (y · z)@.
prop_concat_assoc :: RE Values -> RE Values -> RE Values -> Property
prop_concat_assoc x y z =
    counterexample
        (  "LHS: " ++ show ((x · y) · z)
        ++ "\nRHS: " ++ show (x · (y · z))
        )
        (langEq ((x · y) · z) (x · (y · z)))

-- | @'empty'@ is a left identity for @(·)@: @empty · x = x@.
prop_concat_left_id :: RE Values -> Bool
prop_concat_left_id x = langEq (empty · x) x

-- | @'empty'@ is a right identity for @(·)@: @x · empty = x@.
prop_concat_right_id :: RE Values -> Bool
prop_concat_right_id x = langEq (x · empty) x

-- | @('⊓')@ is associative.
prop_conj_assoc :: RE Values -> RE Values -> RE Values -> Bool
prop_conj_assoc x y z = langEq ((x ⊓ y) ⊓ z) (x ⊓ (y ⊓ z))

-- | @('⊓')@ is commutative.
prop_conj_comm :: RE Values -> RE Values -> Bool
prop_conj_comm x y = langEq (x ⊓ y) (y ⊓ x)

-- | @'universe'@ is the identity for @('⊓')@: @universe ⊓ x = x@.
prop_conj_id :: RE Values -> Bool
prop_conj_id x = langEq (universe ⊓ x) x

-- | @'empty'@ is the right zero for @('∖')@: @x ∖ empty = x@.
prop_sub_right_zero :: RE Values -> Bool
prop_sub_right_zero x = langEq (x ∖ empty) x

-- | @'universe'@ is stable under left-quotient: @universe ∖ x = universe@ —
-- but only when @x@ is satisfiable (@L(x) ≠ ∅@): quotienting by the empty
-- language is vacuous (@universe ∖ Bot = Bot@, not @universe@), not universal.
-- See @Formalization\/REComposableLaws.lean@, §L2 (@re_L2_not_equality@).
prop_sub_universe :: RE Values -> Property
prop_sub_universe x =
    not (langEq x Bot) ==>
        let u :: RE Values = universe
        in counterexample
            (  "x:   " ++ show x
            ++ "\nLHS: " ++ show (u ∖ x)
            ++ "\nRHS: " ++ show u
            )
            (langEq (u ∖ x) u)

-- | Sequential distribution of @('∖')@: @x ∖ (a · b) = (x ∖ a) ∖ b@.
prop_sub_seq_dist :: RE Values -> RE Values -> RE Values -> Bool
prop_sub_seq_dist x a b = langEq (x ∖ (a · b)) ((x ∖ a) ∖ b)

-- | A generator for REs guaranteed to denote at most one word: 'Bot' (zero),
-- 'Epsilon' or a single event (one each). Used as the divisor in
-- 'prop_sub_conj_dist' below.
genSubsingleton :: Gen (RE Values)
genSubsingleton = oneof [pure Bot, pure Epsilon, Single <$> elements testAlph]

-- | @('∖')@ distributes over @('⊓')@: @(a ⊓ b) ∖ c = (a ∖ c) ⊓ (b ∖ c)@ —
-- but only when the divisor @c@ denotes at most one word. With a branching
-- divisor (e.g.\ @c = universe@) the left side requires a *single* word of
-- @c@ to extend into both @a@ and @b@, while the right side allows a
-- *different* word for each — strictly weaker.
-- See @Formalization\/REComposableLaws.lean@, §L4 (@re_L4_not_equality@ /
-- @re_L4_of_subsingleton@).
prop_sub_conj_dist :: RE Values -> RE Values -> Property
prop_sub_conj_dist a b =
    forAll genSubsingleton $ \c ->
        langEq ((a ⊓ b) ∖ c) ((a ∖ c) ⊓ (b ∖ c))

-- ── Test runner ────────────────────────────────────────────────────────────────

-- | Run one property, print its label, and record whether it failed.
-- Plain 'quickCheck' always returns @()@ regardless of outcome, which is why
-- @cabal test@ used to report PASS even with falsified properties below —
-- this checks 'isSuccess' instead and lets 'main' fail the process for real.
runProp :: Testable prop => IORef Bool -> String -> prop -> IO ()
runProp failedRef label prop = do
    putStrLn label
    result <- quickCheckResult prop
    if isSuccess result then return () else writeIORef failedRef True

main :: IO ()
main = do
    putStrLn "── RE Composable law tests (QuickCheck) ─────────────────────"
    failed <- newIORef False
    runProp failed "-- (·) associativity"     prop_concat_assoc
    runProp failed "-- (·) left identity"     prop_concat_left_id
    runProp failed "-- (·) right identity"    prop_concat_right_id
    runProp failed "-- (⊓) associativity"     prop_conj_assoc
    runProp failed "-- (⊓) commutativity"     prop_conj_comm
    runProp failed "-- (⊓) identity"          prop_conj_id
    runProp failed "-- (∖) right zero"        prop_sub_right_zero
    runProp failed "-- (∖) universe residual" prop_sub_universe
    runProp failed "-- (∖) sequential dist."  prop_sub_seq_dist
    runProp failed "-- (∖) conjunction dist." prop_sub_conj_dist
    anyFailed <- readIORef failed
    when anyFailed exitFailure
