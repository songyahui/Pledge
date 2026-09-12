module Pledge.RE
    ( -- * Regular expressions
      RE(..)
    , top
    , globally
    , finally
    , never
    , noUntil
    , previously
      -- * Membership / derivatives
    , nullable
    , atoms
    , firstWith
    , first
    , derivative
    , antiDeriv
    , reLeftQuotient
    , reRightQuotient
    , normalize
      -- * Display helper
    , printOfPledgeRE
    ) where

import Prelude hiding ((<>))
import Data.List (union, nub)
import Pledge.Core
import Pledge.Event

-- | Extended regular expressions over a typed event alphabet.
--
-- The type parameter @t@ is the payload type of 'Event'; the concrete type
-- used throughout the library is 'Term'.  Complement ('Not') is a first-class
-- constructor — no DFA construction is required because the Brzozowski
-- derivative commutes with complement: @∂_a(¬r) = ¬(∂_a(r))@.
data RE t
    = Bot              -- ^ ∅  — empty language
    | Epsilon          -- ^ ε  — empty word
    | Single (Event t) -- ^ {e} — single-event language ('Wildcard' matches anything)
    | Seq  (RE t) (RE t) -- ^ r₁ · r₂ — concatenation
    | Or   (RE t) (RE t) -- ^ r₁ ∪ r₂ — union
    | And  (RE t) (RE t) -- ^ r₁ ∩ r₂ — intersection
    | Star (RE t)        -- ^ r*  — Kleene star
    | Not  (RE t)        -- ^ ¬r  — complement (handled algebraically)

instance (Eq t) => Eq (RE t) where
    Bot == Bot = True
    Epsilon == Epsilon = True
    Single e1 == Single e2 = e1 == e2
    Seq r1a r2a == Seq r1b r2b = r1a == r1b && r2a == r2b
    Or r1a r2a == Or r1b r2b = r1a == r1b && r2a == r2b
    And r1a r2a == And r1b r2b = r1a == r1b && r2a == r2b
    Star r1 == Star r2 = r1 == r2
    Not r1 == Not r2 = r1 == r2
    _ == _ = False

instance (Show t) => Show (RE t) where
    show Bot         = "∅"
    show Epsilon     = "ε"
    show (Single e)  = show e
    -- top: ¬∅ = Σ*
    show (Not Bot)   = "Σ*"
    -- finally: Σ* · ev · Σ*  →  F(ev)
    show (Seq (Not Bot) (Seq (Single ev) (Not Bot))) =
        "F(" ++ show ev ++ ")"
    -- never: ¬F(ev)
    show (Not (Seq (Not Bot) (Seq (Single ev) (Not Bot)))) =
        "¬F(" ++ show ev ++ ")"
    -- noUntil(e, g): ¬((Σ\{g})* · e · Σ*)
    show (Not (Seq (Star (And (Single Wildcard) (Not (Single g)))) (Seq (Single e) (Not Bot)))) =
        "noUntil(" ++ show e ++ ", " ++ show g ++ ")"
    -- general cases
    show (Seq r1 r2) = show r1 ++ " · " ++ show r2
    show (Or  r1 r2) = "(" ++ show r1 ++ ") ∨ (" ++ show r2 ++ ")"
    show (And r1 r2) = "(" ++ show r1 ++ ") ∧ (" ++ show r2 ++ ")"
    show (Star r)    = "(" ++ show r ++ ")*"
    show (Not r)     = "¬(" ++ show r ++ ")"

-- | @Σ*@ — the universal language, complement of the empty language (@¬∅@).
top :: RE t
top = Not Bot

-- | @□ev@ — @ev@ must occur at every step: @ev*@.
globally :: Event t -> RE t
globally ev = Star (Single ev)

-- | @◇ev@ — @ev@ must occur at some future step: @Σ* · ev · Σ*@.
-- Use in @fut@ slots to express a deferred obligation.
finally :: Event t -> RE t
finally ev = Seq top (Seq (Single ev) top)

-- | @¬◇ev@ — @ev@ must /never/ occur: @¬(Σ* · ev · Σ*)@.
never :: Event t -> RE t
never ev = Not (finally ev)

-- | @noUntil e g@ — @e@ must not occur before @g@: @¬((Σ∖{g})* · e · Σ*)@.
-- Once @g@ has occurred, @e@ is unrestricted.
noUntil :: Event t -> Event t -> RE t
noUntil e g = Not (Seq (Star (And (Single Wildcard) (Not (Single g)))) (Seq (Single e) top))

-- | @previously ev@ is the past-facing alias for 'finally'.
-- Use it as a /pre/-condition to assert that @ev@ occurred somewhere in
-- the preceding trace.  The underlying RE is @Σ* · ev · Σ*@, identical to
-- @finally ev@: the name exists purely to signal intent at the call site —
-- write @previously ev@ in @pre@ slots and @finally ev@ in @fut@ slots.
previously :: Event t -> RE t
previously = finally

-- | @ν(r)@: returns @True@ iff @ε ∈ L(r)@ (the empty word is accepted).
nullable :: RE t -> Bool
nullable Bot          = False
nullable Epsilon      = True
nullable (Single _)   = False
nullable (Seq r1 r2)  = nullable r1 && nullable r2
nullable (Or  r1 r2)  = nullable r1 || nullable r2
nullable (And r1 r2)  = nullable r1 && nullable r2
nullable (Star _)     = True
nullable (Not r)      = not (nullable r)   -- ν(¬r) = ¬ν(r)

-- | Collect all concrete (non-'Wildcard') events mentioned in an 'RE'.
-- Forms the effective alphabet for complement unfolding in 'firstWith'.
atoms :: Eq t => RE t -> [Event t]
atoms Bot               = []
atoms Epsilon           = []
atoms (Single Wildcard) = []
atoms (Single e)        = [e]
atoms (Seq r1 r2)       = atoms r1 `union` atoms r2
atoms (Or  r1 r2)       = atoms r1 `union` atoms r2
atoms (And r1 r2)       = atoms r1 `union` atoms r2
atoms (Star r)          = atoms r
atoms (Not r)           = atoms r

-- | Events from @alph@ that can begin a word in @L(r)@.
-- For @Not r@: @e ∈ first(¬r)@ iff @∂_e(r) ≠ Σ*@, checked for every
-- event in the supplied alphabet.
firstWith :: Eq t => [Event t] -> RE t -> [Event t]
firstWith _    Bot               = []
firstWith _    Epsilon           = []
firstWith _    (Single e)        = [e]
firstWith alph (Seq r1 r2)
    | nullable r1                = firstWith alph r1 `union` firstWith alph r2
    | otherwise                  = firstWith alph r1
firstWith alph (Or  r1 r2)      = firstWith alph r1 `union` firstWith alph r2
firstWith alph (And r1 r2)      = nub [ e
                                      | e1 <- firstWith alph r1
                                      , e2 <- firstWith alph r2
                                      , e  <- maybe [] pure (meetEvent e1 e2) ]
firstWith alph (Star r)         = firstWith alph r
firstWith alph (Not r)          = [e | e <- alph, not (isTotal (normalize (derivative e r)))]
  where
    isTotal (Not Bot) = True
    isTotal _         = False

-- | Convenience wrapper around 'firstWith' that uses the events in @r@
-- itself as the alphabet.
first :: Eq t => RE t -> [Event t]
first r = firstWith (atoms r) r

meetEvent :: Eq t => Event t -> Event t -> Maybe (Event t)
meetEvent Wildcard e        = Just e
meetEvent e        Wildcard = Just e
meetEvent x y | x == y      = Just x
              | otherwise   = Nothing

-- | Brzozowski derivative @∂_e(r)@: the RE for all continuations after event @e@.
-- Key law for complement: @∂_a(¬r) = ¬(∂_a(r))@ — no DFA construction needed.
derivative :: Eq t => Event t -> RE t -> RE t
derivative _ Bot          = Bot
derivative _ Epsilon      = Bot
derivative e (Single p)   = if subsumesEvent e p then Epsilon else Bot
derivative e (Seq r1 r2)
    | nullable r1           = Or (Seq (derivative e r1) r2) (derivative e r2)
    | otherwise             = Seq (derivative e r1) r2
derivative e (Or  r1 r2)  = Or  (derivative e r1) (derivative e r2)
derivative e (And r1 r2)  = And (derivative e r1) (derivative e r2)
derivative e (Star r)     = Seq (derivative e r) (Star r)
derivative e (Not r)      = Not (derivative e r)   -- ∂_a(¬r) = ¬(∂_a(r))

-- | Antimirov partial derivatives @∂_e^A(r)@: a list of REs whose language
-- /union/ equals @L(∂_e(r))@.  Compared to the single Brzozowski derivative,
-- Antimirov splitting keeps individual terms smaller:
--
-- * @Or@ distributes into a union of smaller residuals.
-- * @Seq@ factors out the tail @r2@: @{t · r2 | t ∈ ∂_e^A(r1)}@, plus
--   the partial derivatives of @r2@ directly when @r1@ is nullable.
-- * @Star@ unfolds one step: @{t · r* | t ∈ ∂_e^A(r)}@.
-- * @And@ and @Not@ fall back to the unique Brzozowski derivative (singleton list).
antiDeriv :: Eq t => Event t -> RE t -> [RE t]
antiDeriv _ Bot           = []
antiDeriv _ Epsilon       = []
antiDeriv e (Single p)
    | subsumesEvent e p   = [Epsilon]
    | otherwise           = []
antiDeriv e (Or  r1 r2)   = nub (antiDeriv e r1 ++ antiDeriv e r2)
antiDeriv e (Seq r1 r2)   =
    let left  = map (\t -> normalize (Seq t r2)) (antiDeriv e r1)
        right = if nullable r1 then antiDeriv e r2 else []
    in nub (left ++ right)
antiDeriv e (Star r)      = map (\t -> normalize (Seq t (Star r))) (antiDeriv e r)
antiDeriv e (And r1 r2)   = [normalize (And (derivative e r1) (derivative e r2))]
antiDeriv e (Not r)       = [normalize (Not (derivative e r))]

-- ── ACI-equality (for cycle detection) ────────────────────────────────────────

-- Flatten an 'Or'-chain into its list of alternatives; likewise for 'And'.
-- The elements are never themselves 'Or' (resp. 'And') at the top level.
orTerms, andTerms :: RE t -> [RE t]
orTerms  (Or  r1 r2) = orTerms  r1 ++ orTerms  r2
orTerms  r           = [r]
andTerms (And r1 r2) = andTerms r1 ++ andTerms r2
andTerms r           = [r]

-- Set equality under a supplied element equality (quadratic; the lists are
-- the alternatives of a single Or/And node, so they stay short).
sameSetBy :: (a -> a -> Bool) -> [a] -> [a] -> Bool
sameSetBy eq xs ys = all (\x -> any (eq x) ys) xs
                  && all (\y -> any (eq y) xs) ys

-- | Structural equality modulo associativity, commutativity and idempotence
-- of 'Or' and 'And'.
--
-- Brzozowski's finiteness result — an 'RE' has finitely many distinct
-- derivatives — holds only /modulo ACI/, so 'reLeftQuotient' must use this
-- rather than the derived 'Eq' to recognise a repeated state.  With derived
-- 'Eq', @Or a (Or b a)@ and @Or b a@ count as different states and the
-- traversal below need not terminate.
aciEq :: Eq t => RE t -> RE t -> Bool
aciEq Bot         Bot         = True
aciEq Epsilon     Epsilon     = True
aciEq (Single e1) (Single e2) = e1 == e2
aciEq (Seq  a b)  (Seq  c d)  = aciEq a c && aciEq b d
aciEq (Star a)    (Star b)    = aciEq a b
aciEq (Not  a)    (Not  b)    = aciEq a b
aciEq r@(Or  _ _) s@(Or  _ _) = sameSetBy aciEq (orTerms  r) (orTerms  s)
aciEq r@(And _ _) s@(And _ _) = sameSetBy aciEq (andTerms r) (andTerms s)
aciEq _           _           = False

-- ── Left-quotient ─────────────────────────────────────────────────────────────

-- | Left-quotient @r1 \\ r2@: the residual obligation in @r2@ after any
-- trace described by @r1@, i.e.\ the language
-- @{ w | ∃u ∈ L(r1). u·w ∈ L(r2) }@.
--
-- Note this is a quotient by a whole /language/, not by a single event.
-- It satisfies the recurrence
--
-- @
--   r1 \\ r2  =  (if ν(r1) then r2 else ∅)  ∪  ⋃_e (∂_e r1) \\ (∂_e r2)
-- @
--
-- whose first summand contributes @r2@ whenever @ε ∈ L(r1)@.  The
-- derivative of @r2@ is taken as the full Antimirov set @∂_e^A(r2)@ rather
-- than the single Brzozowski step, which keeps intermediate terms smaller;
-- the result language is unchanged because @⋃ L(∂_e^A(r2)) = L(∂_e(r2))@.
--
-- The recurrence is solved by a worklist traversal of the reachable pairs
-- @(∂_w r1, ∂_w^A r2)@, accumulating the residual of every pair whose first
-- component is nullable.  A pair already seen (up to 'aciEq') contributes
-- nothing new and is dropped, which is what makes the traversal terminate:
-- both components range over finite sets modulo ACI (Brzozowski for @r1@,
-- Antimirov for @r2@), so the product is finite.  Without that check the
-- traversal diverges for any divisor whose derivative does not shrink —
-- @Σ*@ and any starred language being the common cases.
reLeftQuotient :: Eq t => RE t -> RE t -> RE t
reLeftQuotient Epsilon r2 = r2
reLeftQuotient r1 r2 = normalize (go [(r1, r2)] [] Bot)
  where
    go []             _    acc = acc
    go ((p, q):queue) seen acc
        | any (samePair (p, q)) seen = go queue seen acc
        | otherwise                  = go (nexts ++ queue) ((p, q) : seen) acc'
      where
        -- ε ∈ L(p) means the whole of q is still owed along this branch.
        acc' | nullable p = Or q acc
             | otherwise  = acc
        -- Combined alphabet, so complement is unfolded over the events
        -- mentioned by either side.  'Wildcard' is included as the
        -- representative of Σ minus those events: without it a pair naming
        -- no concrete atom (@Σ*@, @¬ε@, …) would have an empty alphabet and
        -- no successors at all, silently yielding ∅.
        alph  = Wildcard : (atoms p `union` atoms q)
        -- A 'Wildcard' first-event of the divisor stands for /every/ event,
        -- including the concrete atoms named by the dividend; expand it so
        -- those specific continuations of @q@ are explored too.
        expand Wildcard = alph
        expand e        = [e]
        nexts = [ (normalize (derivative e p), q')
                | e0 <- firstWith alph p
                , e  <- expand e0
                , q' <- antiDeriv e q
                ]

    samePair (p1, q1) (p2, q2) = aciEq p1 p2 && aciEq q1 q2

-- Reverse an RE: revRE(r) accepts exactly {w^R | w ∈ L(r)}.
revRE :: RE t -> RE t
revRE Bot           = Bot
revRE Epsilon       = Epsilon
revRE (Single e)    = Single e
revRE (Seq r1 r2)   = Seq (revRE r2) (revRE r1)
revRE (Or  r1 r2)   = Or  (revRE r1) (revRE r2)
revRE (And r1 r2)   = And (revRE r1) (revRE r2)
revRE (Star r)      = Star (revRE r)
revRE (Not r)       = Not (revRE r)

-- | Right-quotient @r2 ∕ r1@: the residual of @r2@ with @r1@ stripped from
-- the right.  Computed via reversal: @r2 ∕ r1 = rev(rev(r2) ∖ rev(r1))@.
reRightQuotient :: Eq t => RE t -> RE t -> RE t
reRightQuotient r1 r2 = revRE (reLeftQuotient (revRE r1) (revRE r2))

-- ── Composable RE instance ────────────────────────────────────────────────────

instance Eq t => Composable (RE t) where
    concatenation = Seq
    conjunction   = And
    empty         = Epsilon
    universe      = top
    leftQuotient  = reLeftQuotient
    rightQuotient = reRightQuotient

-- | Simplify an 'RE' using algebraic identities and De Morgan laws.
--
-- Key reductions: @∅ · r = ∅@, @ε · r = r@, @r ∪ r = r@, @¬¬r = r@,
-- @¬(r₁ ∨ r₂) = ¬r₁ ∧ ¬r₂@, @∅* = ε@, @ε* = ε@.
-- Does /not/ call 'derivative' internally, so it is always terminating.
normalize :: Eq t => RE t -> RE t
normalize r = case r of
    Seq r1 r2 -> case (normalize r1, normalize r2) of
        (Bot, _)      -> Bot
        (_, Bot)      -> Bot
        (Epsilon, r') -> r'
        (r', Epsilon) -> r'
        -- Σ*·r = Σ* when ε ∈ L(r):  Σ* ⊆ Σ*·r (take ε from r) and
        -- Σ*·r ⊆ Σ*, so the two are equal.  Symmetrically for r·Σ*.
        -- Without this a fully discharged residual such as
        -- Σ*·(a·Σ* ∨ ε) stays syntactically distinct from Σ*, and a
        -- structural @== universe@ discharge check reports a violation
        -- for a program that has in fact met every obligation.
        (r1', r2')
            | isTop r1', nullable r2' -> top
            | isTop r2', nullable r1' -> top
        (r1', r2')    -> Seq r1' r2'

    Or r1 r2 -> case (normalize r1, normalize r2) of
        (Bot, r')        -> r'
        (r', Bot)        -> r'
        (r1', r2')
            | r1' == r2'  -> r1'
            | isTop r1'  -> top
            | isTop r2'  -> top
        (r1', r2')       -> Or r1' r2'

    And r1 r2 -> case (normalize r1, normalize r2) of
        (Bot, _)         -> Bot
        (_, Bot)         -> Bot
        (r1', r2')
            | r1' == r2'  -> r1'
            | isTop r1'  -> r2'
            | isTop r2'  -> r1'
        (Epsilon, r')    -> if nullable r' then Epsilon else Bot
        (r', Epsilon)    -> if nullable r' then Epsilon else Bot
        (r1', r2')       -> And r1' r2'

    -- Complement: involution + De Morgan laws
    Not r1 -> case normalize r1 of
        Not r'       -> r'                                    -- ¬¬r = r
        Or  r1' r2'  -> normalize (And (Not r1') (Not r2'))  -- De Morgan
        And r1' r2'  -> normalize (Or  (Not r1') (Not r2'))  -- De Morgan
        Bot          -> top                              -- ¬∅  = Σ*
        r' | isTop r' -> Bot                                -- ¬Σ* = ∅
        r'             -> Not r'

    Star r1 -> case normalize r1 of
        Bot     -> Epsilon   -- ∅* = ε
        Epsilon -> Epsilon   -- ε* = ε
        r'      -> Star r'

    _ -> r
  where
    isTop (Not Bot) = True
    isTop _         = False

-- | Run a 'Pledge' action once, print the four components, and return the
-- result.  Uses 'inspect' so the underlying @IO@ action executes exactly once.
printOfPledgeRE :: forall t a. (Show a, Show t, Eq t) => String -> Pledge IO (RE t) a -> IO a
printOfPledgeRE name prog = do
    PledgeResult r preC postC futC <- inspect prog
    putStrLn $ "=== " ++ name ++ " ==="
    putStrLn $ "Ret:    " ++ show r
    putStrLn $ "Pre:    " ++ show (normalize preC)
    putStrLn $ "Post:   " ++ show (normalize postC)
    putStrLn $ "Future: " ++ show (normalize futC)
    return r
