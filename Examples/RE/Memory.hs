module Examples.RE.Memory where
import Prelude hiding ((<>))
import Pledge
import System.Random

-- free requires that malloc was the immediately preceding post-event.
-- For interleaved mallocs use `pre = universe` and rely on `future` instead.

type RETerm = (RE Values)

malloc :: Pledge IO (RE Values) Addr
malloc = Pledge $ do
    addr <- randomRIO (0, 5)
    return (addr,
            universe,
            if addr > 0 then Single (Atom "malloc" (List [Num addr])) else Epsilon,
            if addr > 0 then finally (Atom "free" (List [Num addr]))
                        else never (Usage (List [Num addr])))

free :: Addr -> Pledge IO (RE Values) ()
-- noUntil free malloc: free(addr) must not occur again until malloc(addr)
-- happens first.  This prevents double-free while allowing re-allocation:
--   free → free          is forbidden  (double-free, no malloc in between)
--   free → malloc → free is allowed    (re-allocation is valid)
free addr = Pledge $ return
    ((),
     if addr > 0 then previously (Atom "malloc" (List [Num addr])) else universe,
     Single (Atom "free" (List [Num addr])),
     if addr > 0 then noUntil (Atom "free" (List [Num addr]))
                              (Atom "malloc" (List [Num addr]))
                 else universe
    )

-- Good: malloc uses the returned address to parameterise the free obligation.
-- Demonstrates data-dependent future: future = \a -> finally(free(a)).
mallocFreeByReturnedAddr :: Pledge IO (RE Values) ()
mallocFreeByReturnedAddr = do
    addr :: Addr <- malloc
    free addr

-- Good: two sequential malloc/free pairs — each obligation is discharged in turn.
mallocFreeSequential :: Pledge IO RETerm ()
mallocFreeSequential = do
    addr1 <- malloc
    addr2 <- malloc
    free addr1
    free addr2

-- Good: malloc and free every address in a loop.
loopAllFreed :: Int -> [Pledge IO RETerm ()]
loopAllFreed n = replicate n eachRun
    where
    eachRun :: Pledge IO RETerm ()
    eachRun = do
        addr <- malloc
        free addr

-- Bad: malloc 1 and 2, only free 1 — future obligation for address 2 remains.
missingFree :: Pledge IO RETerm Addr
missingFree = (malloc >>= free) >> malloc

-- Bad: free without a preceding malloc — precondition violated (pre = Bot).
freeWithoutMalloc :: Pledge IO RETerm ()
freeWithoutMalloc = free 1

-- Bad: allocate via malloc, free the wrong address.
-- future of (malloc 1) evaluates to finally(free(1));
-- free 2 does not discharge it, so finally(free(1)) remains.
wrongAddrFree :: Pledge IO RETerm ()
wrongAddrFree = malloc >>= \n -> free (n+1)

-- Bad: free the same address twice immediately.
-- After the first free, future = noUntil(free(1), malloc(1)).
-- The second free posts free(1) before any malloc(1), so the future becomes ∅.
doubleFreeImmediate :: Pledge IO RETerm ()
doubleFreeImmediate = malloc >>= \n -> free n >> free n

-- Bad: double-free with intervening work between the two frees.
-- The noUntil(free(1), malloc(1)) future set by the first free is still active
-- when the second free arrives, regardless of what happens in between.
doubleFreeWithWork :: Pledge IO RETerm ()
doubleFreeWithWork = do
    addr1 <- malloc
    addr2 <- malloc
    free addr1
    free addr2
    free addr1

-- Bad: leak combined with double-free in the same program.
-- addr 2 is never freed (leak) and addr 1 is freed twice (double-free).
-- Both violations are captured: future carries ∅ from the double-free.
leakAndDoubleFree :: Pledge IO RETerm ()
leakAndDoubleFree = do
    addr1 <- malloc
    _ <- malloc
    free addr1
    free addr1

-- Good: reallocate the same address after freeing it.
-- After free 1: future = noUntil(free(1), malloc(1)).
-- malloc 1 resets the guard (derivative w.r.t. malloc(1) = Σ*).
-- malloc 1 also imposes finally(free(1)), which the second free discharges.
mallocFreeReallocFree :: Pledge IO RETerm ()
mallocFreeReallocFree = (malloc >>= free) >> (malloc >>= free)

-- Good: allocate and return the address without freeing.
-- ret = 1; future = finally(free(1)) — obligation visible in the residual.
allocReturnAddr :: Pledge IO RETerm Addr
allocReturnAddr = malloc

-- Bad: allocate two addresses and return both — neither obligation is discharged.
-- ret = (1, 2); future = finally(free(1)) ∧ finally(free(2)).
allocTwoReturnPair :: Pledge IO RETerm (Addr, Addr)
allocTwoReturnPair = (,) <$> malloc <*> malloc


main :: IO ()
main = do
    printOfPledgeRE "mallocFreeByReturnedAddr" mallocFreeByReturnedAddr
    printOfPledgeRE "mallocFreeSequential"     mallocFreeSequential
    mapM_ (printOfPledgeRE "loopAllFreed 3")   (loopAllFreed 3)
    printOfPledgeRE "missingFree"              missingFree
    printOfPledgeRE "freeWithoutMalloc"        freeWithoutMalloc
    printOfPledgeRE "wrongAddrFree"            wrongAddrFree
    printOfPledgeRE "doubleFreeImmediate"      doubleFreeImmediate
    printOfPledgeRE "doubleFreeWithWork"       doubleFreeWithWork
    printOfPledgeRE "leakAndDoubleFree"        leakAndDoubleFree
    printOfPledgeRE "mallocFreeReallocFree"    mallocFreeReallocFree
    printOfPledgeRE "allocReturnAddr"          allocReturnAddr
    printOfPledgeRE "allocTwoReturnPair"       allocTwoReturnPair
    return ()