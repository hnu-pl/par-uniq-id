module Lib
    ( newId
    , runParallel
    , runParallelT
    ) where

import Control.Parallel.Strategies
import Control.Monad.Trans.State.Strict

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
    return as

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

