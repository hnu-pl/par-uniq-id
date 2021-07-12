{-# LANGUAGE NoMonomorphismRestriction #-}
module Main where

import Lib

import Control.Concurrent.MVar.Strict

import Control.Parallel.Strategies
import Control.Monad.Trans.State.Strict
import Control.Monad
import Data.List
import System.Environment

import qualified Control.Monad.Parallel as MP

import Unbound.Generics.LocallyNameless

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
    = Const Int          -- n
    | Plus Expr Expr     -- e + e
    | Less Expr Expr     -- e < e
    | If Expr Expr Expr  -- if e e1 e0
    | App Expr Expr      -- e e
    | Var Nm             -- x
    | Lam Nm Expr        -- \x.e
    | VarS Nm            -- ?x
    | LamS Nm Expr       -- \?x.e
    | AppS Expr Expr     -- e e
    | LetS Nm Expr Expr  -- letS f = \?x.\?y. ... in e
    deriving Show
    -- TODO Unbound 기반으로 바꿔야 할지도


type Env a = [(Nm,a)]
data Sem v = Val v | Cl (Env (Sem v)) Expr
    deriving Show

type Val = Sem Int


lookup' x env = v where Just v = lookup x env

eval :: Env Val -> Expr -> Sem Int
eval env (Const i)     = Val i
eval env (Plus e1 e2)  = 
    case (eval env e1 , eval env e2) of
        (Val n1, Val n2)     -> Val (n1+n2)
        (_ , _)              -> error ""
eval env (Less e1 e2)  = 
    case (eval env e1 , eval env e2) of
        (Val n1, Val n2)     -> if n1<n2 then Val 0 else Val 1
        (_ , _)              -> error ""
eval env (If e1 e2 e3) = 
    case (eval env e1) of
        (Val 0)              -> eval env e2
        (Val _)              -> eval env e3
        (_)                  -> error ""
eval env (App e1 e2)   = eval ((x,e2'):env1) e
    where 
        Cl env1 (Lam x e)    = eval env e1
        e2'                  = eval env e2
eval env (Var x)       = lookup' x env
eval env v@(Lam x e)   = Cl env v
eval env (VarS x)      = undefined 
eval env v@(LamS x e)  = undefined
eval env (AppS e1 e2)  = undefined
eval env (LetS x e1 e2)= undefined

-- type ValS = Sem Expr
-- expand :: Env ValS -> ValS Expr
-- expand _ _ = undefined

{-
let a = 10
let b = 7 
letS F ?x ?y =
       let a = ?x * 2 in
       let b = ?y * 3 in
       a + b   ## 의도는 F ?x ?y 는 대략 ?x*2 + ?y*3
in F b a

===> let a = b * 2 in
     let b = a * 3
-}

main = do
    print bench1

-- main = print example1

{-
example1 = runParallel
    [ sequence [newId]
    , sequence [newId, newId, newId]
    , sequence [newId, newId]
    ] `runState` (0,1)

-- >>> runParallel (sequence <$> [ [newId], [newId, newId, newId], [newId, newId] ]) `runState` (0,1)
-- ([[0],[1,4,7],[2,5]],(10,1))

bench1 n m = flip runState (0,1) . runParallel $
    replicate n (foldl1 (>>) $ replicate m newId)

main = do
    a0:a1:a2:_ <- getArgs
    let k = read a0 :: Int
        n = read a1 :: Int
        m = read a2 :: Int
    case k of
        1 -> do
            putStrLn $ " bench1 "++show n++" "++show m
            print $ bench1 n m 
        2 -> do
            putStrLn $ " bench2 "++show n++" "++show m
            print =<< bench2 n m 


newIdMVar :: MVar Int -> IO Int
newIdMVar c = modifyMVar c (\n -> return (n+1,n))

bench2 n m = do
    c <- newMVar (0 :: Int)
    let new = newIdMVar c
    print . maximum =<< MP.replicateM n (foldl1 (>>) $ replicate m new)

{-
stack run -- 1 8 2000000 +RTS -s -N1
stack run -- 1 8 2000000 +RTS -s -N2
stack run -- 1 8 2000000 +RTS -s -N3
stack run -- 1 8 2000000 +RTS -s -N4
stack run -- 1 8 2000000 +RTS -s -N5
stack run -- 1 8 2000000 +RTS -s -N6
stack run -- 1 8 2000000 +RTS -s -N7
stack run -- 1 8 2000000 +RTS -s -N8
-}

{-
stack run -- 2 8 100000 +RTS -s -N1
stack run -- 2 8 100000 +RTS -s -N2
stack run -- 2 8 100000 +RTS -s -N3
stack run -- 2 8 100000 +RTS -s -N4
stack run -- 2 8 100000 +RTS -s -N5
stack run -- 2 8 100000 +RTS -s -N6
stack run -- 2 8 100000 +RTS -s -N7
stack run -- 2 8 100000 +RTS -s -N8
-}

-}