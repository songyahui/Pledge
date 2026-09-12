module Examples.RE.NetworkProtocol where
import Prelude hiding ((<>))
import Pledge

-- TCP-like three-way handshake modelled as effectful steps.

sendSYN :: Pledge IO (RE Values) ()
sendSYN = Pledge $ return
    ((), universe,
     Single (Atom "sendSYN" (List [])),
     finally (Atom "recvSYNACK" (List [])))

-- Precondition: sendSYN must have just occurred
recvSYNACK :: Pledge IO (RE Values) ()
recvSYNACK = Pledge $ return
    ((), previously (Atom "sendSYN" (List [])),
     Single (Atom "recvSYNACK" (List [])),
     finally (Atom "sendACK" (List [])))

-- Precondition: recvSYNACK must have just occurred
sendACK :: Pledge IO (RE Values) ()
sendACK = Pledge $ return
    ((), previously (Atom "recvSYNACK" (List [])),
     Single (Atom "sendACK" (List [])),
     universe)

sendData :: String -> Pledge IO (RE Values) ()
sendData payload = Pledge $ return
    ((), universe, Single (Atom "sendData" (List [Str payload])), universe)

sendFIN :: Pledge IO (RE Values) ()
sendFIN = Pledge $ return
    ((), universe,
     Single (Atom "sendFIN" (List [])),
     finally (Atom "recvFINACK" (List [])))

recvFINACK :: Pledge IO (RE Values) ()
recvFINACK = Pledge $ return
    ((), universe, Single (Atom "recvFINACK" (List [])), universe)

-- Good: complete handshake, data, teardown — all preconditions met, no future pending
fullSession :: Pledge IO (RE Values) ()
fullSession = do
    sendSYN
    recvSYNACK
    sendACK
    sendData "GET / HTTP/1.1"
    sendFIN
    recvFINACK

-- Bad: SYN sent but handshake never completed — future pending
stalledHandshake :: Pledge IO (RE Values) ()
stalledHandshake = do
    sendSYN

-- Bad: recvSYNACK called without sendSYN — precondition violated
outOfOrder :: Pledge IO (RE Values) ()
outOfOrder = do
    recvSYNACK
    sendACK

-- Bad: connection never torn down — future pending
teardownMissed :: Pledge IO (RE Values) ()
teardownMissed = do
    sendSYN
    recvSYNACK
    sendACK
    sendData "payload"
    sendFIN
    -- missing recvFINACK

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
    printResult "fullSession"      fullSession
    printResult "stalledHandshake" stalledHandshake
    printResult "outOfOrder"       outOfOrder
    printResult "teardownMissed"   teardownMissed
