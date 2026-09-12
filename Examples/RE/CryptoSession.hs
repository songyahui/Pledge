module Examples.RE.CryptoSession where
import Prelude hiding ((<>))
import Pledge

initSession :: String -> Pledge IO (RE Values) ()
initSession sid = Pledge $ return
    ((), universe,
     Single (Atom "initSession" (List [Str sid])),
     finally (Atom "finalizeSession" (List [Str sid])))

finalizeSession :: String -> Pledge IO (RE Values) ()
finalizeSession sid = Pledge $ return
    ((), universe, Single (Atom "finalizeSession" (List [Str sid])), universe)

-- Nonce must be consumed exactly once (use-once enforcement via future)
generateNonce :: Int -> Pledge IO (RE Values) ()
generateNonce nid = Pledge $ return
    ((), universe,
     Single (Atom "generateNonce" (List [Num nid])),
     finally (Atom "consumeNonce" (List [Num nid])))

-- Precondition: nonce must have just been generated
consumeNonce :: Int -> Pledge IO (RE Values) ()
consumeNonce nid = Pledge $ return
    ((), previously (Atom "generateNonce" (List [Num nid])),
     Single (Atom "consumeNonce" (List [Num nid])),
     universe)

encrypt :: String -> String -> Pledge IO (RE Values) ()
encrypt sid msg = Pledge $ return
    ((), universe,
     Single (Atom "encrypt" (List [Str sid, Str msg])),
     universe)

-- Good: session opened, nonce generated and consumed, session closed
goodHandshake :: Pledge IO (RE Values) ()
goodHandshake = do
    initSession "sess-1"
    generateNonce 42
    consumeNonce 42
    encrypt "sess-1" "hello"
    finalizeSession "sess-1"

-- Bad: nonce generated but never consumed (replay attack risk) — future remains
nonceLeak :: Pledge IO (RE Values) ()
nonceLeak = do
    initSession "sess-2"
    generateNonce 99
    encrypt "sess-2" "secret"
    finalizeSession "sess-2"

-- Bad: session never finalized — future remains
unclosedSession :: Pledge IO (RE Values) ()
unclosedSession = do
    initSession "sess-3"
    generateNonce 7
    consumeNonce 7
    encrypt "sess-3" "data"

printResult :: String -> Pledge IO (RE Values) () -> IO ()
printResult name prog = do
    (_, preC, postC, futC) <- runPledge prog
    putStrLn $ "=== " ++ name ++ " ==="
    putStrLn $ "Pre:    " ++ show (normalize preC)
    putStrLn $ "Post:   " ++ show (normalize postC)
    putStrLn $ "Future: " ++ show (normalize futC)
    putStrLn ""

main :: IO ()
main = do
    printResult "goodHandshake"   goodHandshake
    printResult "nonceLeak"       nonceLeak
    printResult "unclosedSession" unclosedSession
