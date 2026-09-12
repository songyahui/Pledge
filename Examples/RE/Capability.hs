module Examples.RE.Capability where
import Prelude hiding ((<>))
import Pledge

requestToken :: String -> Pledge IO (RE Values) ()
requestToken user = Pledge $ return
    ((), universe,
     Single (Atom "requestToken" (List [Str user])),
     finally (Atom "revokeToken" (List [Str user])))

useToken :: String -> String -> Pledge IO (RE Values) ()
useToken user resource = Pledge $ return
    ((), universe,
     Single (Atom "accessResource" (List [Str user, Str resource])),
     universe)

-- Precondition: a token must have just been requested for this user
revokeToken :: String -> Pledge IO (RE Values) ()
revokeToken user = Pledge $ return
    ((), previously (Atom "requestToken" (List [Str user])),
     Single (Atom "revokeToken" (List [Str user])),
     universe)

escalate :: String -> Pledge IO (RE Values) ()
escalate role = Pledge $ return
    ((), universe,
     Single (Atom "escalate" (List [Str role])),
     finally (Atom "deescalate" (List [Str role])))

deescalate :: String -> Pledge IO (RE Values) ()
deescalate role = Pledge $ return
    ((), previously (Atom "escalate" (List [Str role])),
     Single (Atom "deescalate" (List [Str role])),
     universe)

-- Good: token acquired and immediately revoked
properTokenUse :: Pledge IO (RE Values) ()
properTokenUse = do
    requestToken "alice"
    revokeToken "alice"

-- Good: privilege escalated and dropped
safeEscalation :: Pledge IO (RE Values) ()
safeEscalation = do
    escalate "admin"
    deescalate "admin"

-- Bad: token never revoked — future obligation remains
tokenLeak :: Pledge IO (RE Values) ()
tokenLeak = do
    requestToken "mallory"
    useToken "mallory" "/secrets"

-- Bad: privilege escalated but never dropped — future remains
privilegeLeak :: Pledge IO (RE Values) ()
privilegeLeak = do
    escalate "admin"
    useToken "system" "/root"

-- Bad: revokeToken without requestToken — precondition violated
revokeWithoutRequest :: Pledge IO (RE Values) ()
revokeWithoutRequest = revokeToken "eve"

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
    printResult "properTokenUse"       properTokenUse
    printResult "safeEscalation"       safeEscalation
    printResult "tokenLeak"            tokenLeak
    printResult "privilegeLeak"        privilegeLeak
    printResult "revokeWithoutRequest" revokeWithoutRequest
