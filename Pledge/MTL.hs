module Pledge.MTL
    ( Interval(..)
    , within
    , exactly
    , atLeast
    , fromTo
    , intervalSteps
    , MTL(..)
    , mtlToSingleStep
    , mtlToRe
    , reptSeq
    , sigmaPow
    , atMostSeq
    , finallyWithin
    , neverWithin
    , globallyWithin
    , printOfPledgeMTL
    ) where

import Data.Maybe (fromMaybe)
import Pledge.Core
import Pledge.Event (Event(..))
import Pledge.RE

data Interval = Interval Int (Maybe Int)
    deriving (Eq)

instance Show Interval where
    show (Interval lo Nothing)  = "[" ++ show lo ++ ",∞)"
    show (Interval lo (Just b)) = "[" ++ show lo ++ "," ++ show b ++ "]"

within :: Int -> Interval
within n = Interval 0 (Just n)

exactly :: Int -> Interval
exactly n = Interval n (Just n)

atLeast :: Int -> Interval
atLeast n = Interval n Nothing

fromTo :: Int -> Int -> Interval
fromTo lo hi = Interval lo (Just hi)

intervalSteps :: Interval -> Maybe (Either Int [Int])
intervalSteps (Interval lo hi)
    | lo < 0    = Nothing
    | otherwise = case hi of
        Nothing -> Just (Left lo)
        Just b  -> Just (Right [lo .. b])

reptSeq :: RE t -> Int -> RE t
reptSeq _ n | n <= 0 = Epsilon
reptSeq r n          = Seq r (reptSeq r (n - 1))

sigmaPow :: Int -> RE t
sigmaPow = reptSeq (Single Wildcard)

atMostSeq :: RE t -> Int -> RE t
atMostSeq r n = foldr Or Bot [ reptSeq r k | k <- [0 .. max 0 n] ]

data MTL t
    = MTLTrue
    | MTLFalse
    | MTLAtom     (Event t)
    | MTLNot      (MTL t)
    | MTLAnd      (MTL t) (MTL t)
    | MTLOr       (MTL t) (MTL t)
    | MTLNext     (MTL t)
    | MTLUntil    Interval (MTL t) (MTL t)
    | MTLFinally  Interval (MTL t)
    | MTLGlobally Interval (MTL t)
    | MTLFromRE   (RE t)
    deriving (Eq)

instance (Show t, Eq t) => Show (MTL t) where
    show MTLTrue             = "⊤"
    show MTLFalse            = "⊥"
    show (MTLAtom e)         = show e
    show (MTLNot l)          = "¬" ++ show l
    show (MTLAnd l1 l2)      = "(" ++ show l1 ++ " ∧ " ++ show l2 ++ ")"
    show (MTLOr  l1 l2)      = "(" ++ show l1 ++ " ∨ " ++ show l2 ++ ")"
    show (MTLNext l)         = "X " ++ show l
    show (MTLUntil i l1 l2)  = "(" ++ show l1 ++ " U_" ++ show i ++ " " ++ show l2 ++ ")"
    show (MTLFinally i l)    = "F_" ++ show i ++ " " ++ show l
    show (MTLGlobally i l)   = "G_" ++ show i ++ " " ++ show l
    show (MTLFromRE r)       = maybe ("[RE: " ++ show r ++ "]") show (reToMtl r)

reToMtl :: Eq t => RE t -> Maybe (MTL t)
reToMtl Bot                                 = Just MTLFalse
reToMtl r | r == top                        = Just MTLTrue
reToMtl (Single e)                          = Just (MTLAtom e)
reToMtl (Seq (Single Wildcard) r)           = MTLNext <$> reToMtl r
reToMtl (Seq r1 r2) | r1 == top             = MTLFinally (atLeast 0) <$> reToMtl r2
reToMtl (Not (Seq r1 (Not r2))) | r1 == top = MTLGlobally (atLeast 0) <$> reToMtl r2
reToMtl (Seq (Star r1) r2)                  = MTLUntil (atLeast 0) <$> reToMtl r1 <*> reToMtl r2
reToMtl (Not r)                             = MTLNot <$> reToMtl r
reToMtl (And r1 r2)                         = MTLAnd <$> reToMtl r1 <*> reToMtl r2
reToMtl (Or  r1 r2)                         = MTLOr  <$> reToMtl r1 <*> reToMtl r2
reToMtl _                                   = Nothing

mtlToSingleStep :: MTL t -> Maybe (RE t)
mtlToSingleStep MTLTrue        = Just (Single Wildcard)
mtlToSingleStep MTLFalse       = Just Bot
mtlToSingleStep (MTLAtom e)    = Just (Single e)
mtlToSingleStep (MTLNot p)     = And (Single Wildcard) . Not <$> mtlToSingleStep p
mtlToSingleStep (MTLAnd p q)   = And <$> mtlToSingleStep p <*> mtlToSingleStep q
mtlToSingleStep (MTLOr  p q)   = Or  <$> mtlToSingleStep p <*> mtlToSingleStep q
mtlToSingleStep _              = Nothing

mtlToRe :: Eq t => MTL t -> Maybe (RE t)
mtlToRe MTLTrue           = Just top
mtlToRe MTLFalse          = Just Bot
mtlToRe (MTLAtom e)       = Just (Single e)
mtlToRe (MTLNot p)        = Not <$> mtlToRe p
mtlToRe (MTLAnd p q)      = And <$> mtlToRe p <*> mtlToRe q
mtlToRe (MTLOr  p q)      = Or  <$> mtlToRe p <*> mtlToRe q
mtlToRe (MTLNext p)       = Seq (Single Wildcard) <$> mtlToRe p
mtlToRe (MTLFinally i p)  = do
    ks <- intervalSteps i
    r  <- mtlToRe p
    pure $ case ks of
        Left  a  -> Seq (sigmaPow a) (Seq top r)
        Right xs -> foldr Or Bot [ Seq (sigmaPow k) r | k <- xs ]
mtlToRe (MTLGlobally i p) = do
    ks <- intervalSteps i
    s  <- mtlToSingleStep p
    let violate = Seq (And (Single Wildcard) (Not s)) top
    pure . Not $ case ks of
        Left  a  -> Seq (sigmaPow a) (Seq top violate)
        Right xs -> foldr Or Bot [ Seq (sigmaPow k) violate | k <- xs ]
mtlToRe (MTLUntil i p q)  = do
    ks <- intervalSteps i
    s  <- mtlToSingleStep p
    r  <- mtlToRe q
    pure $ case ks of
        Left  a  -> Seq (reptSeq s a) (Seq (Star s) r)
        Right xs -> foldr Or Bot [ Seq (reptSeq s k) r | k <- xs ]
mtlToRe (MTLFromRE r)     = Just r

toRE :: Eq t => MTL t -> RE t
toRE = fromMaybe Bot . mtlToRe

instance Eq t => Composable (MTL t) where
    concatenation l1 l2 = MTLFromRE (concatenation (toRE l1) (toRE l2))
    conjunction         = MTLAnd
    empty               = MTLFromRE empty
    universe            = MTLTrue
    leftQuotient  l1 l2 = MTLFromRE (leftQuotient  (toRE l1) (toRE l2))
    rightQuotient l1 l2 = MTLFromRE (rightQuotient (toRE l1) (toRE l2))

finallyWithin :: Int -> Event t -> MTL t
finallyWithin n ev = MTLFinally (within n) (MTLFromRE (Seq (Single ev) top))

neverWithin :: Int -> Event t -> MTL t
neverWithin n ev = MTLNot (MTLFinally (fromTo 0 (n - 1)) (MTLFromRE (Seq (Single ev) top)))

globallyWithin :: Int -> Event t -> MTL t
globallyWithin n ev = MTLGlobally (fromTo 0 (n - 1)) (MTLAtom ev)

printOfPledgeMTL :: (Show a, Show t, Eq t)
                 => String -> Pledge IO (MTL t) a -> IO a
printOfPledgeMTL name prog = do
    PledgeResult r preC postC futC <- inspect prog
    putStrLn $ "=== " ++ name ++ " ==="
    putStrLn $ "Ret:    " ++ show r
    putStrLn $ "Pre:    " ++ showComp preC
    putStrLn $ "Post:   " ++ showComp postC
    putStrLn $ "Future: " ++ showComp futC
    return r
  where
    showComp c = maybe "<no RE translation>" (show . normalize) (mtlToRe c)
