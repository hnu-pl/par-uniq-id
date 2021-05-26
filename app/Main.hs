{-# LANGUAGE NoMonomorphismRestriction #-}
module Main where

import Lib

import Control.Parallel.Strategies
import Control.Monad.Trans.State.Strict
import Control.Monad
import Data.List
import System.Environment

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


-- main = print example1

example1 = runParallel
    [ sequence [newId]
    , sequence [newId, newId, newId]
    , sequence [newId, newId]
    ] `runState` (0,1)

-- >>> runParallel (sequence <$> [ [newId], [newId, newId, newId], [newId, newId] ]) `runState` (0,1)
-- ([[0],[1,4,7],[2,5]],(10,1))

bench n m = flip runState (0,1) . runParallel $
    replicate n (foldl1 (>>) $ replicate m newId)

main = do
    a0:a1:_ <- getArgs
    let n = read a0 :: Int
        m = read a1 :: Int
    putStrLn $ " bench "++show n++" "++show m
    print $ bench n m 

{-
stack run -- 8 2000000 +RTS -s -N1
stack run -- 8 2000000 +RTS -s -N2
stack run -- 8 2000000 +RTS -s -N3
stack run -- 8 2000000 +RTS -s -N4
stack run -- 8 2000000 +RTS -s -N5
stack run -- 8 2000000 +RTS -s -N6
stack run -- 8 2000000 +RTS -s -N7
stack run -- 8 2000000 +RTS -s -N8
-}