{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
module Examples.RE.Shadow where

import Prelude hiding ((<>))
import Data.IORef

-- Pledge spec monad — qualified to avoid clash with the 'Effectful' module
import qualified Pledge as F
import Pledge (universe, RE, normalize, finally, previously, noUntil)

-- effectful library: real effect handlers
import Effectful
import Effectful.Dispatch.Dynamic (send, interpret, EffectHandler)
import Effectful.State.Static.Local (State, get, modify, runState)
import Effectful.Error.Static (Error, throwError, runErrorNoCallStack)

-- ── 0. Intro: effectful basics (State + Error) ────────────────────────────

program :: (State Int :> es, Error String :> es) => Eff es Int
program = do
    n <- get @Int
    if n < 0
        then throwError "negative!"
        else modify @Int (+1) >> get @Int

runProgram :: IO ()
runProgram = do
    result <- runEff
        . runErrorNoCallStack @String
        . runState @Int 5
        $ program
    print result   -- Right (6, 6)

-- ── 1. FileSystem effect ──────────────────────────────────────────────────
-- Declare a FileSystem effect as a GADT.  Operations are sent via `send`
-- and discharged by a handler.

data FileSystem :: Effect where
    FsOpen  :: FilePath -> FileSystem m ()
    FsRead  :: FilePath -> FileSystem m String
    FsClose :: FilePath -> FileSystem m ()

type instance DispatchOf FileSystem = Dynamic

-- Smart constructors
fsOpen  :: FileSystem :> es => FilePath -> Eff es ()
fsOpen  = send . FsOpen

fsRead  :: FileSystem :> es => FilePath -> Eff es String
fsRead  = send . FsRead

fsClose :: FileSystem :> es => FilePath -> Eff es ()
fsClose = send . FsClose

-- ── 2. Handler ────────────────────────────────────────────────────────────
-- Interpret FileSystem into IOE: each command appends to an IORef trace
-- and fsRead returns a simulated string.

fsHandler :: IORef [String] -> EffectHandler FileSystem '[IOE]
fsHandler ref _ cmd = case cmd of
    FsOpen  path -> liftIO $ modifyIORef ref (++ ["open("  ++ path ++ ")"])
    FsRead  path -> liftIO $ do
        modifyIORef ref (++ ["read(" ++ path ++ ")"])
        return "file-contents"
    FsClose path -> liftIO $ modifyIORef ref (++ ["close(" ++ path ++ ")"])

-- ── 3. Shadow type ────────────────────────────────────────────────────────
-- A Shadow pairs the RE specification (F.Pledge IO (RE Values) a, checked
-- statically by Pledge) with a real Eff '[FileSystem, IOE] a program
-- (run by the effect handler at runtime).

data Shadow a = Shadow
    { spec :: F.Pledge IO (F.RE F.Values) a
    , impl :: Eff '[FileSystem, IOE] a
    }

-- Run the handler side; returns the result and the event trace.
runShadow :: Shadow a -> IO (a, [String])
runShadow s = do
    ref <- newIORef []
    result <- runEff . interpret (fsHandler ref) $ impl s
    trace  <- readIORef ref
    return (result, trace)

instance Functor Shadow where
    fmap f (Shadow sp ef) = Shadow (fmap f sp) (fmap f ef)

instance Applicative Shadow where
    pure x = Shadow (pure x) (pure x)
    Shadow spf eff <*> Shadow spx efx = Shadow (spf <*> spx) (eff <*> efx)

-- >>= threads spec and handler monads fully independently.
instance Monad Shadow where
    return = pure
    Shadow sp ef >>= f = Shadow (sp >>= spec . f) (ef >>= impl . f)

-- ── 4. Spec primitives ────────────────────────────────────────────────────
-- For each Eff operation, an F.Pledge IO (RE Values) value carrying the RE contract.

specOpen :: FilePath -> F.Pledge IO (F.RE F.Values) ()
specOpen path = F.Pledge $ return
    ((), universe,
     F.Single (F.Atom "open" (F.List [F.Str path])),
     finally (F.Atom "close" (F.List [F.Str path])))

-- Preconditions use 'previously' (Σ*·e·Σ*), not 'Single'.  A 'Single'
-- precondition constrains only the /immediately preceding/ event, and such a
-- condition does not survive composition: in @p >>= q@ the precondition is
-- @pre p ⊓ (pre q ∕ post p)@, and once @pre q@ is discharged by @post p@ the
-- right operand collapses to ε, whose intersection with the non-nullable
-- @pre p@ is ∅.  So a chain of Single-preconditions reports a violation for a
-- program that is in fact correct.  Preconditions must be properties of the
-- whole preceding trace.
specRead :: FilePath -> F.Pledge IO (F.RE F.Values) String
specRead path = F.Pledge $ return
    ("",  -- placeholder: spec models protocol, not content
     previously (F.Atom "open" (F.List [F.Str path])),
     F.Single (F.Atom "read" (F.List [F.Str path])),
     universe)

specClose :: FilePath -> F.Pledge IO (F.RE F.Values) ()
specClose path = F.Pledge $ return
    ((), previously (F.Atom "open" (F.List [F.Str path])),
     F.Single (F.Atom "close" (F.List [F.Str path])),
     universe)

-- ── 5. Shadow operations ──────────────────────────────────────────────────
-- Bundle the spec primitive with the Eff send into a single Shadow action.

shOpen  :: FilePath -> Shadow ()
shOpen  path = Shadow (specOpen  path) (fsOpen  path)

shRead  :: FilePath -> Shadow String
shRead  path = Shadow (specRead  path) (fsRead  path)

shClose :: FilePath -> Shadow ()
shClose path = Shadow (specClose path) (fsClose path)

-- ── 6. Example programs ───────────────────────────────────────────────────

-- Good: open → read → close.  Spec: future = ε.
goodFile :: Shadow String
goodFile = do
    shOpen "data.txt"
    contents <- shRead "data.txt"
    shClose "data.txt"
    return contents

-- Bad: open two files, close only one.  Spec: future = F(close("b.txt")).
leakedHandle :: Shadow ()
leakedHandle = do
    shOpen "a.txt"
    shClose "a.txt"
    shOpen "b.txt"   -- future: close("b.txt") never discharged

-- Bad: read before open — spec pre = Bot (precondition violated).
readBeforeOpen :: Shadow String
readBeforeOpen = shRead "secret.txt"

-- Good: open, read twice, close.  Spec: future = ε.
doubleRead :: Shadow (String, String)
doubleRead = do
    shOpen "log.txt"
    c1 <- shRead "log.txt"
    c2 <- shRead "log.txt"
    shClose "log.txt"
    return (c1, c2)

-- ── Display helpers ───────────────────────────────────────────────────────

printSpec :: Show a => String -> Shadow a -> IO ()
printSpec name s = do
    (ret, preC, postC, futC) <- F.runPledge (spec s)
    putStrLn $ "=== " ++ name ++ " ==="
    putStrLn $ "Pre:    " ++ show (normalize preC)
    putStrLn $ "Post:   " ++ show (normalize postC)
    putStrLn $ "Ret:    " ++ show ret
    putStrLn $ "Future: " ++ show (normalize futC)
    putStrLn ""

runAndShow :: Show a => String -> Shadow a -> IO ()
runAndShow label s = do
    (val, trace) <- runShadow s
    putStrLn $ "=== " ++ label ++ " ==="
    putStrLn $ "Ret:   " ++ show val
    putStrLn $ "Trace: " ++ show trace
    putStrLn ""

-- ── Main ──────────────────────────────────────────────────────────────────

main :: IO ()
main = do
    -- 0. Basic effectful: State + Error
    putStrLn "── 0. effectful: State + Error ──"
    runProgram
    putStrLn ""

    printSpec "goodFile"       goodFile
    runAndShow "goodFile"       goodFile

    printSpec "leakedHandle"   leakedHandle
    runAndShow "leakedHandle"   leakedHandle

    printSpec "readBeforeOpen" readBeforeOpen
    runAndShow "readBeforeOpen" readBeforeOpen

    printSpec "doubleRead"     doubleRead
    runAndShow "doubleRead"     doubleRead
