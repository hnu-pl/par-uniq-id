{-# LANGUAGE NoMonomorphismRestriction #-}
module Main where

import Lib

import Control.Parallel.Strategies
-- import Data.List
import Control.Monad.Trans.State.Strict
import Control.Monad
import Data.Functor.Identity

qsort [] = []
qsort [y] = [y]
qsort (y:ys) = xs ++ y : zs
    where (xs,zs) = ([x | x<-ys, x<=y], [z | z<-ys, z> y]) `using` parTuple2 rpar rpar
    -- where (xs,zs) = partition (<= y) ys `using` parTuple2 rpar rpar

n = 50000000

{-}
main :: IO ()
main = do
    let x = last . qsort $ [n,n-2..2]++[1,3..n-1]
    case x == x of True -> return ()
-}

type Nm = String
data Expr
    = Var Nm
    | Lam Nm Expr
    | App Expr Expr
    deriving Show

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

main = print $ runParallel
    [ sequence [newId]
    , sequence [newId, newId, newId]
    , sequence [newId, newId]
    ] `runState` (0,1)

-- >>> runParallel (sequence <$> [ [newId], [newId, newId, newId], [newId, newId] ]) `runState` (0,1)
-- ([[0],[1,4,7],[2,5]],(11,1))
