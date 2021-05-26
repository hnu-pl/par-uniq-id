{-# LANGUAGE NoMonomorphismRestriction #-}
module Main where

import Lib

import Control.Parallel.Strategies
-- import Data.List
import Control.Monad.Trans.State.Strict

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

runParallel ms = do
    (k,i) <- get
    let n = length ms
    let ps = zipWith ($) [flip runState (k+r,i*n) | r<-[0..n-1]] ms
              `using` parList rpar
    put (1 + maximum (map (fst . snd) ps), i)
    return $ map fst ps
 
{-
  do ...
     [r1,,r2,k3] <- runParallel [t1, t2, t3]
     -- [(k1,r1),(k2,r2),(k3,r3)] <- runParallel' [t1, t2, t3]
     -- [r1,k2,,r3] <- runParallel' [t1, t2, t3]
        상태를 max[k1,k2,k3]+1 세팅을 해주면
     ...
-}

main = print $ runParallel
    [ sequence [newId]
    , sequence [newId, newId, newId]
    , sequence [newId, newId]
    , sequence [newId, newId, newId, newId]
    ] `runState` (0,1)