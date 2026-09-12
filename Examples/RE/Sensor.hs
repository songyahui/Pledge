module Examples.RE.Sensor where
import Prelude hiding ((<>))
import Pledge

sensorInit :: Int -> Pledge IO (RE Values) ()
sensorInit sid = Pledge $ return
    ((), universe,
     Single (Atom "sensorInit" (List [Num sid])),
     finally (Atom "sensorSleep" (List [Num sid])))

sensorRead :: Int -> Pledge IO (RE Values) ()
sensorRead sid = Pledge $ return
    ((), Or (previously (Atom "sensorInit" (List [Num sid])))
            (previously (Atom "sensorRead" (List [Num sid]))),
     Single (Atom "sensorRead" (List [Num sid])),
     universe)

-- Precondition: sensor must have been initialised or read before sleeping
sensorSleep :: Int -> Pledge IO (RE Values) ()
sensorSleep sid = Pledge $ return
    ((), Or (previously (Atom "sensorInit" (List [Num sid])))
            (previously (Atom "sensorRead" (List [Num sid]))),
     Single (Atom "sensorSleep" (List [Num sid])),
     universe)

motorOn :: Int -> Pledge IO (RE Values) ()
motorOn mid = Pledge $ return
    ((), universe,
     Single (Atom "motorOn" (List [Num mid])),
     finally (Atom "motorOff" (List [Num mid])))

motorOff :: Int -> Pledge IO (RE Values) ()
motorOff mid = Pledge $ return
    ((), previously (Atom "motorOn" (List [Num mid])),
     Single (Atom "motorOff" (List [Num mid])),
     universe)

actuate :: String -> Int -> Pledge IO (RE Values) ()
actuate device level = Pledge $ return
    ((), universe,
     Single (Atom "actuate" (List [Str device, Num level])),
     universe)

-- Good: init, read, sleep
safeSensorCycle :: Pledge IO (RE Values) ()
safeSensorCycle = do
    sensorInit 1
    sensorRead 1
    sensorSleep 1

-- Good: motor on, actuate, motor off
safeMotorCycle :: Pledge IO (RE Values) ()
safeMotorCycle = do
    motorOn 1
    actuate "pump" 80
    motorOff 1

-- Bad: sensor 2 never slept — future pending
sensorLeftOn :: Pledge IO (RE Values) ()
sensorLeftOn = do
    sensorInit 1
    sensorSleep 1
    sensorInit 2
    sensorRead 2
    -- sensorSleep 2 missing

-- Bad: motor left running — future pending
motorLeftRunning :: Pledge IO (RE Values) ()
motorLeftRunning = do
    motorOn 3
    actuate "fan" 50

-- Bad: sensorRead without init — precondition violated
readWithoutInit :: Pledge IO (RE Values) ()
readWithoutInit = sensorRead 5

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
    printResult "safeSensorCycle"  safeSensorCycle
    printResult "safeMotorCycle"   safeMotorCycle
    printResult "sensorLeftOn"     sensorLeftOn
    printResult "motorLeftRunning" motorLeftRunning
    printResult "readWithoutInit"  readWithoutInit
