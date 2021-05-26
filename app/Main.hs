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

main :: IO ()
main = do
    let x = last . qsort $ [n,n-2..2]++[1,3..n-1]
    case x == x of True -> return ()


type Nm = String
data Expr
    = Var Nm
    | Lam Nm Expr
    | App Expr Expr
    deriving Show

{-
k를 1씩 증가 그러니까 이번엔 k를 사용하고 다음번에는 (k+1,1) 이런 식으로 진행
(k,1)

이러다 3개로 나눠서 병렬로 돌리려면

(k,3), (k+1,3), (k+2,3) 으로 나눠서 진행

일반적으로 k를 i씩 증가 그러니까 이번엔 k를 사용하고 다음번엔 (k+i,i) 이런 식으로
(k,i)

이러다 n개로 나눠서 돌리면
(k,i*n), (k+1,i*n), ..., (k+n-1,i*n)
-}

newId :: Monad m => StateT (Int, Int) m Int
newId = do { (k,i) <- get; put (k+i,i); return k }

runParListWithId ms = zipWith (>>) fs ms `using` parList rpar 
    where
      fs = [ modify (\(k,i) -> (k+r,i*n)) | r <- [0..n-1] ] 
      n = length ms

{-
  do ...
     [r1,,r2,k3] <- runParallel [t1, t2, t3]
     -- [(k1,r1),(k2,r2),(k3,r3)] <- runParallel' [t1, t2, t3]
     -- [r1,k2,,r3] <- runParallel' [t1, t2, t3]
        상태를 max[k1,k2,k3]+1 세팅을 해주면
     ...
-}