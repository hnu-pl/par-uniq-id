{-# LANGUAGE NoMonomorphismRestriction, DeriveGeneric, MultiParamTypeClasses #-}
module Main where

import Lib

import Control.Concurrent.MVar.Strict

import Control.Parallel.Strategies
import Control.Monad.Trans.State.Strict
import Control.Monad
import Data.List
import System.Environment

import qualified Control.Monad.Parallel as MP

import GHC.Generics
import Data.Typeable
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

type Nm = Name Expr
data Expr
    = Const Int                          -- n
    | Var Nm                             -- x
    | Plus Expr Expr                     -- e1 + e2
    | Less Expr Expr                     -- e1 < e2
    | If Expr Expr Expr                  -- if e e1 e0
    | Lam (Bind Nm Expr)                 -- \x.e
    | App Expr Expr                      -- e e
    | LamS (Bind Nm Expr)                -- \?x.e
    | LetS (Bind (Nm, Embed Expr) Expr)  -- letS f = \?x.\?y. ... in e
    deriving (Show, Generic, Typeable)
    -- TODO Unbound 기반으로 바꿔야 할지도

instance Alpha Expr
instance Subst Expr Expr where
  isvar (Var  x) = Just (SubstName x)
  isvar _     = Nothing

type SEnv = [(Nm,Expr)]

expand :: Fresh m => SEnv -> Expr -> m Expr
expand _   e@(Const n)   = return e
expand env e@(Var x)     =
    case lookup x env of
        Just e1 -> return e1
        Nothing -> return e 
expand env (Plus e1 e2)  = do -- TODO constant folding?
    e1' <- expand env e1
    e2' <- expand env e2
    return $ Plus e1' e2'
expand env (Less e1 e2)  = do -- TODO constant folding?
    e1' <- expand env e1
    e2' <- expand env e2
    return $ Less e1' e2'
expand env (If e e1 e0)  = do -- TODO constant folding?
    e'  <- expand env e
    e1' <- expand env e1
    e0' <- expand env e0
    return $ If e' e1' e0'
expand env (Lam b)       = do
    (x,e) <- unbind b
    e' <- expand env e
    return $ Lam (bind x e')
expand env (App e1 e2)   = do
    e1' <- expand env e1
    e2' <- expand env e2
    case e1' of
        LamS b -> do (x,e) <- unbind b
                     return $ subst x e2' e
        e1'    -> return $ App e1' e2'
expand env e@(LamS b) = do
    (x,e) <- unbind b
    e' <- expand env e
    return $ LamS (bind x e')
expand env (LetS b) = do
    ((f,Embed e1), e) <- unbind b -- letS f = e1 in e
    e1' <- expand env e1
    expand ((f,e1'):env) e

lamS x = LamS . bind x

e99 = LetS . bind (gt, embed (lamS x . lamS y $ Less _y _x)) $
      LetS . bind (eq, embed (lamS x . lamS y $ Less (Plus (Less _x _y) (_gt _x _y)) (Const 1))) $
      App (App (Var eq) (Const 4)) (Const 3)
    where
        gt = s2n "gt"
        eq = s2n "eq"
        x = s2n "?x"
        y = s2n "?y"
        _gt a b = App (Var gt) a `App` b
        _eq a b = App (Var eq) a `App` b
        _x = Var x
        _y = Var y

-- >>> runFreshM (expand [] e99)
-- Less (Plus (Less (Const 4) (Const 3)) (Less (Const 3) (Const 4))) (Const 1)
    
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
