module Pledge.LTL
    ( LTL(..)
    , ltlToRe
    ) where

import Pledge.Core
import Pledge.Event
import Pledge.RE

-- | Linear Temporal Logic over finite traces; translate to 'RE' with 'ltlToRe'.
data LTL t
    = LTLTrue
    | LTLFalse
    | LTLAtom     (Event t)
    | LTLNot      (LTL t)
    | LTLAnd      (LTL t) (LTL t)
    | LTLOr       (LTL t) (LTL t)
    | LTLNext     (LTL t)          -- ^ @X φ@
    | LTLUntil    (LTL t) (LTL t)  -- ^ @φ U ψ@
    | LTLFinally  (LTL t)          -- ^ @F φ@
    | LTLGlobally (LTL t)          -- ^ @G φ@
    | LTLFromRE   (RE t)           -- ^ opaque 'RE', produced by the 'Composable' instance

instance (Show t, Eq t) => Show (LTL t) where
    show LTLTrue            = "⊤"
    show LTLFalse           = "⊥"
    show (LTLAtom e)        = show e
    show (LTLNot l)         = "¬" ++ show l
    show (LTLAnd l1 l2)     = "(" ++ show l1 ++ " ∧ " ++ show l2 ++ ")"
    show (LTLOr  l1 l2)     = "(" ++ show l1 ++ " ∨ " ++ show l2 ++ ")"
    show (LTLNext l)        = "X " ++ show l
    show (LTLUntil l1 l2)   = "(" ++ show l1 ++ " U " ++ show l2 ++ ")"
    show (LTLFinally l)     = "F " ++ show l
    show (LTLGlobally l)    = "G " ++ show l
    show (LTLFromRE r)      = maybe ("[RE: " ++ show r ++ "]") show (reToLtl r)

-- | Translate an 'LTL' formula to 'RE'.
ltlToRe :: LTL t -> RE t
ltlToRe LTLTrue            = top
ltlToRe LTLFalse           = Bot
ltlToRe (LTLAtom e)        = Single e
ltlToRe (LTLNot l)         = Not (ltlToRe l)
ltlToRe (LTLAnd l1 l2)     = And (ltlToRe l1) (ltlToRe l2)
ltlToRe (LTLOr  l1 l2)     = Or  (ltlToRe l1) (ltlToRe l2)
ltlToRe (LTLNext l)        = Seq (Single Wildcard) (ltlToRe l)
ltlToRe (LTLUntil l1 l2)   =
    let reR1 = ltlToRe l1 in
    Seq (Star reR1) (ltlToRe l2)
ltlToRe (LTLFinally l)     = Seq top (ltlToRe l)
ltlToRe (LTLGlobally l)    = Not (Seq top (Not (ltlToRe l)))
ltlToRe (LTLFromRE r)      = r

-- | Best-effort inverse of 'ltlToRe': recognise the exact RE shapes
-- 'ltlToRe' produces and rebuild the 'LTL' constructor that made them.
-- @top@ (@= 'Not' 'Bot'@) isn't a data constructor, so it can't be matched
-- as a pattern — each shape that contains it is checked with an @==@ guard
-- instead. 'Nothing' means @r@ falls outside that recognised fragment;
-- 'LTLFromRE' is then the honest representation.
reToLtl :: Eq t => RE t -> Maybe (LTL t)
reToLtl Bot                              = Just LTLFalse
reToLtl r | r == top                     = Just LTLTrue
reToLtl (Single e)                       = Just (LTLAtom e)
reToLtl (Seq (Single Wildcard) r)        = LTLNext <$> reToLtl r
reToLtl (Seq r1 r2) | r1 == top          = LTLFinally <$> reToLtl r2
reToLtl (Not (Seq r1 (Not r2))) | r1 == top = LTLGlobally <$> reToLtl r2
reToLtl (Seq (Star r1) r2)               = LTLUntil <$> reToLtl r1 <*> reToLtl r2
reToLtl (Not r)                          = LTLNot <$> reToLtl r
reToLtl (And r1 r2)                      = LTLAnd <$> reToLtl r1 <*> reToLtl r2
reToLtl (Or  r1 r2)                      = LTLOr  <$> reToLtl r1 <*> reToLtl r2
reToLtl _                                = Nothing  -- not expressible in LTL

-- | 'concatenation', 'empty' and the quotients have no LTL syntax, so they
-- round-trip through 'RE' via 'ltlToRe' and wrap back up as 'LTLFromRE'.
instance Eq t => Composable (LTL t) where
    concatenation l1 l2 = LTLFromRE (concatenation (ltlToRe l1) (ltlToRe l2))
    conjunction         = LTLAnd
    empty               = LTLFromRE empty
    universe            = LTLTrue
    leftQuotient  l1 l2 = LTLFromRE (leftQuotient  (ltlToRe l1) (ltlToRe l2))
    rightQuotient l1 l2 = LTLFromRE (rightQuotient (ltlToRe l1) (ltlToRe l2))
