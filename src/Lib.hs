module Lib where
import Control.Parallel.Strategies
-- import Control.Monad.Trans.State.Strict
import Control.Monad.Trans.State.Lazy

import Unbound.Generics.LocallyNameless
-- import Control.Monad.State.Class


runPar :: [FreshM a] -> FreshM [a]
-- runPar ms = sequence ms -- non parallell
runPar ms = FreshMT $ do
    (k,i) <- get
    let n = fromIntegral $ length ms
    let ps = zipWith ($) [flip runState (k+r,i*n) . unFreshMT | r<-[0..n-1]] ms
              `using` parList rpar
    let (as,ss) = unzip ps
    put (maximum (map fst ss), i)
    return (as `using` parList rseq)

-- runParT :: ... => [FreshMT m a] -> FreshMT m [a]
-- runParT ms = sequence ms -- non parallel
runParT :: Monad m => (m (a, (Integer, Integer)) -> (a, (Integer, Integer))) -> [FreshMT m a] -> FreshMT m [a]
runParT runM ms = FreshMT $ do
    (k,i) <- get
    let n = fromIntegral $ length ms
    let ps = zipWith ($) [runM . flip runStateT (k+r,i*n) . unFreshMT | r<-[0..n-1]] ms
              `using` parList rpar
    let (as,ss) = unzip ps
    put (maximum (map fst ss), i)
    return (as `using` parList rseq)




{-
newId :: Monad m => StateT (Int, Int) m Int
newId = do { (k,i) <- get; put (k+i,i); return k }

runParallel :: [State (Int, Int) a] -> State (Int, Int) [a]
runParallel ms = do
    (k,i) <- get
    let n = length ms
    let ps = zipWith ($) [flip runState (k+r,i*n) | r<-[0..n-1]] ms
              `using` parList rpar
    let (as,ss) = unzip ps
    put (maximum (map fst ss), i)
    return (as `using` parList rseq)

runParallelT :: Monad m => (m (a,(Int,Int)) -> (a,(Int,Int))) ->
    [StateT (Int, Int) m a] -> StateT (Int, Int) m [a]
runParallelT runM ms = do
    (k,i) <- get
    let n = length ms
    let ps = zipWith ($) [runM . flip runStateT (k+r,i*n) | r<-[0..n-1]] ms
              `using` parList rpar
    let (as,ss) = unzip ps
    put (maximum (map fst ss), i)
    return as
-}