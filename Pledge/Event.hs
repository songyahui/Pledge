-- | Events and the pattern language matched against them.
module Pledge.Event
    ( Event(..)
    , subsumesEvent
    ) where

data Event t
    = Atom String t
    | Usage t
    | Wildcard
    deriving (Eq)

instance Show t => Show (Event t) where
    show (Atom name arg) = name ++ "(" ++ show arg ++ ")"
    show (Usage arg)     = "use(" ++ show arg ++ ")"
    show Wildcard        = "_"

-- | Does the concrete event @e@ match the pattern @p@?
--
-- Negation no longer lives at the event level (see 'Pledge.RE.Not'): a
-- pattern here only ever asserts a positive match, so this is a plain
-- structural comparison plus the 'Wildcard' catch-all.
subsumesEvent :: Eq t => Event t -> Event t -> Bool
subsumesEvent _            Wildcard     = True
subsumesEvent (Atom n1 a1) (Atom n2 a2) = n1 == n2 && a1 == a2
subsumesEvent (Usage a1)   (Usage a2)   = a1 == a2
subsumesEvent _            _            = False
