module Examples.RE.Transaction where
import Prelude hiding ((<>))
import Pledge

-- Begin a transaction: future = eventually commit or rollback
beginTx :: Pledge IO (RE Values) ()
beginTx = Pledge $ return
    ((), universe,
     Single (Atom "beginTx" (List [])),
     Or (finally (Atom "commit" (List []))) (finally (Atom "rollback" (List []))))

dbWrite :: String -> Int -> Pledge IO (RE Values) ()
dbWrite key val = Pledge $ return
    ((), universe,
     Single (Atom "write" (List [Str key, Num val])),
     universe)

-- Precondition: a transaction must have been begun somewhere earlier.
--
-- Two things this deliberately does /not/ say.  It is 'previously', not
-- 'Single': a commit may be separated from its beginTx by arbitrary writes.
-- And it does not try to require "at least one write": an event pattern is
-- either 'Wildcard' (matching /any/ event) or an 'Atom' matching its payload
-- exactly, so @Atom "write" (List [])@ matches only a write with /no/
-- arguments -- never @dbWrite "balance" 100@.  There is currently no way to
-- write "a write with any arguments"; see Feedback/revision-todo.md.
commit :: Pledge IO (RE Values) ()
commit = Pledge $ return
    ((), previously (Atom "beginTx" (List [])),
     Single (Atom "commit" (List [])),
     universe)

rollback :: Pledge IO (RE Values) ()
rollback = Pledge $ return
    ((), universe, Single (Atom "rollback" (List [])), universe)

-- Good: begin, write, commit
committedTx :: Pledge IO (RE Values) ()
committedTx = do
    beginTx
    dbWrite "balance" 100
    commit

-- Good: begin, write, rollback
rolledBackTx :: Pledge IO (RE Values) ()
rolledBackTx = do
    beginTx
    dbWrite "balance" 100
    rollback

-- Bad: begin and write but no commit or rollback — future obligation remains
openTx :: Pledge IO (RE Values) ()
openTx = do
    beginTx
    dbWrite "balance" 100

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
    printResult "committedTx"  committedTx
    printResult "rolledBackTx" rolledBackTx
    printResult "openTx"       openTx
