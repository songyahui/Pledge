import qualified Examples.UnitTest.PledgeTest as PledgeTest
import qualified Examples.UnitTest.PresburgerTest as PresburgerTest
import qualified Examples.UnitTest.RELaws as RELaws
import qualified Examples.RE.Memory          as REMemory
import qualified Examples.RE.FileHandle      as REFileHandle
import qualified Examples.RE.Mutex           as REMutex
import qualified Examples.RE.Transaction     as RETransaction
import qualified Examples.RE.CryptoSession   as RECryptoSession
import qualified Examples.RE.NetworkProtocol as RENetworkProtocol
import qualified Examples.RE.Capability      as RECapability
import qualified Examples.RE.Sensor          as RESensor
import qualified Examples.RE.Shadow          as REShadow
import qualified Examples.GuardedRE.Memory         as ExtREMemory
import qualified Examples.GuardedRE.BoundedCounter as ExtREBoundedCounter

section :: String -> IO ()
section title = putStrLn $ "\n── " ++ title ++ " " ++ replicate (50 - length title) '─'

main :: IO ()
main = do
    section "0. Unit Tests"
    PledgeTest.main
    PresburgerTest.main
    RELaws.main

    section "RE 1. Memory Management (malloc/free)"
    REMemory.main

    section "RE 2. File Handle Lifecycle"
    REFileHandle.main

    section "RE 3. Mutex / Lock Lifecycle"
    REMutex.main

    section "RE 4. Database Transactions"
    RETransaction.main

    section "RE 5. Cryptographic Sessions & Nonces"
    RECryptoSession.main

    section "RE 6. Network Protocol (TCP-like)"
    RENetworkProtocol.main

    section "RE 7. Capability / Token Lifecycle"
    RECapability.main

    section "RE 8. Sensor / Actuator (IoT)"
    RESensor.main

    section "RE 9. Shadow Approach (spec alongside IO)"
    REShadow.main

    section "ExtRE 1. Memory Management (heap liveness + trace ordering)"
    ExtREMemory.main

    section "ExtRE 2. Bounded Counter (arithmetic bounds + protocol)"
    ExtREBoundedCounter.main
