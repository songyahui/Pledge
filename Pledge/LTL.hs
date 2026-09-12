module Pledge.LTL
    ( -- * LTL
      LTL(..)
    , toSingleStep
    , ltlToRe
    ) where

import Pledge.Event
import Pledge.RE

-- | Linear Temporal Logic formulae over finite traces.
-- Use 'ltlToRe' to translate to 'RE'; no automaton construction is required.
data LTL t
    = LTLTrue
    | LTLFalse
    | LTLAtom     (Event t)
    | LTLNot      (LTL t)
    | LTLAnd      (LTL t) (LTL t)
    | LTLOr       (LTL t) (LTL t)
    | LTLNext     (LTL t)          -- ^ @X φ@  strong next
    | LTLUntil    (LTL t) (LTL t) -- ^ @φ U ψ@
    | LTLFinally  (LTL t)          -- ^ @F φ ≜ ⊤ U φ ≡ Σ* · ⟦φ⟧@
    | LTLGlobally (LTL t)          -- ^ @G φ ≜ ¬F¬φ ≡ ¬(Σ* · ¬⟦φ⟧)@


-- ── Single-step projection ────────────────────────────────────────────────────
-- toSingleStep l: the RE for a single event satisfying l at the current step.
-- This is the correct building block for LTLUntil:
--   ⟦φ U ψ⟧  =  toSingleStep(φ)* · ⟦ψ⟧
--
-- Using ltlToRe l1 directly would be wrong: ⟦l1⟧ may contain words of
-- length > 1 (e.g. LTLNext, LTLFinally), so Star ⟦l1⟧ iterates over
-- multi-event matches rather than individual steps.
--
-- Well-defined for propositional l (Boolean combinations of LTLAtom).
-- For temporal operators inside the Until left-hand side (LTLNext, LTLFinally,
-- LTLGlobally, nested LTLUntil) there is no single-step projection; Bot is
-- returned as a conservative error signal that makes the enclosing Until
-- unsatisfiable, surfacing the limitation rather than silently mis-specifying.
--
-- The LTLNot case intersects with Single Wildcard (Σ^1) to keep the result
-- length-1: bare Not (toSingleStep l) would include ε and multi-event words.

-- Returns Nothing for temporal operators (LTLNext, LTLUntil, LTLFinally,
-- LTLGlobally), which have no single-step projection.
toSingleStep :: LTL t -> Maybe (RE t)
toSingleStep LTLTrue         = Just (Single Wildcard)               -- any single event
toSingleStep LTLFalse        = Just Bot                             -- no event satisfies False
toSingleStep (LTLAtom e)     = Just (Single e)                      -- exactly event e
toSingleStep (LTLNot l)      = And (Single Wildcard) . Not          -- Σ^1 ∩ ¬step(l)
                                   <$> toSingleStep l
toSingleStep (LTLAnd l1 l2)  = And <$> toSingleStep l1 <*> toSingleStep l2
toSingleStep (LTLOr  l1 l2)  = Or  <$> toSingleStep l1 <*> toSingleStep l2
toSingleStep _               = Nothing  -- temporal operators not representable as a single step


-- | Algebraic translation @LTLf → RE@.  No automaton construction is needed;
-- complement is handled by the 'Not' constructor directly.
-- Returns 'Nothing' when 'LTLUntil'\'s left-hand side contains a temporal
-- operator with no single-step projection (see 'toSingleStep').
ltlToRe :: LTL t -> Maybe (RE t)
ltlToRe LTLTrue            = Just top                         -- ¬∅  = Σ*
ltlToRe LTLFalse           = Just Bot                              -- ∅
ltlToRe (LTLAtom e)        = Just (Single e)
ltlToRe (LTLNot l)         = Not <$> ltlToRe l                  -- ¬⟦l⟧
ltlToRe (LTLAnd l1 l2)     = And <$> ltlToRe l1 <*> ltlToRe l2  -- ⟦l1⟧ ∩ ⟦l2⟧
ltlToRe (LTLOr  l1 l2)     = Or  <$> ltlToRe l1 <*> ltlToRe l2  -- ⟦l1⟧ ∪ ⟦l2⟧
ltlToRe (LTLNext l)        = Seq (Single Wildcard) <$> ltlToRe l   -- Σ · ⟦l⟧
ltlToRe (LTLUntil l1 l2)   = Seq . Star <$> toSingleStep l1          -- step(l1)* · ⟦l2⟧
                                           <*> ltlToRe l2
ltlToRe (LTLFinally l)     = Seq top <$> ltlToRe l            -- Σ* · ⟦l⟧
ltlToRe (LTLGlobally l)    = Not . Seq top . Not                 -- ¬(Σ* · ¬⟦l⟧)
                                   <$> ltlToRe l
