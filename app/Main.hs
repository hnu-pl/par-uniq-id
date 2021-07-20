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

import GHC.Generics ( Generic )
import Data.Typeable ( Typeable )
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
    = Const Int              -- n
    | Var Nm                 -- x
    | Plus Expr Expr         -- e1 + e2
    | Less Expr Expr         -- e1 < e2
    | If Expr Expr Expr      -- if e e1 e0
    | Lam (Bind Nm Expr)     -- \x.e
    | App Expr Expr          -- e e
    | LamS (Bind Nm Expr)    -- \?x.e
    | LetS (Bind (Nm, Embed Expr) Expr)           -- letS f = \?x.\?y. ... in e
    | LetRecS (Bind (Rec (Nm, Embed Expr)) Expr)  -- letrecS f = \?x.\?y. ... in e
    deriving (Show, Generic, Typeable)

instance Alpha Expr
instance Subst Expr Expr where
  isvar (Var  x) = Just (SubstName x)
  isvar _     = Nothing

type SEnv = [(Nm,Expr)]

cfold1 (Plus (Const 0)  e2        ) = e2
cfold1 (Plus e1         (Const 0) ) = e1
cfold1 (Plus (Const n1) (Const n2)) = Const (n1 + n2)
cfold1 (Less (Const n1) (Const n2))
                        | n1 < n2   = Const 1
                        | otherwise = Const 0
cfold1 (If (Const 0) e1 e0) = e0
cfold1 (If (Const _) e1 e0) = e1
cfold1 e = e

expand :: Fresh m => SEnv -> Expr -> m Expr
expand _   e@(Const n)   = return e
expand env e@(Var x)     =
    case lookup x env of
        Just e1 -> return e1
        Nothing -> return e 
expand env (Plus e1 e2)  = do
    e1' <- expand env e1
    e2' <- expand env e2
    return . cfold1 $ Plus e1' e2'
expand env (Less e1 e2)  = do
    e1' <- expand env e1
    e2' <- expand env e2
    return . cfold1 $ Less e1' e2'
expand env (If e e1 e0)  = do
    e'  <- expand env e
    e1' <- expand env e1
    e0' <- expand env e0
    return . cfold1 $ If e' e1' e0'
expand env (Lam b)       = do
    (x,e) <- unbind b
    e' <- expand env e
    return $ Lam (bind x e')
expand env (App e1 e2)   = do
    e1' <- expand env e1
    e2' <- expand env e2
    case e1' of
        LamS b -> do (x,e) <- unbind b
                     expand env (subst x e2' e)
        e1'    -> return $ App e1' e2'
expand env e@(LamS b) = return e
expand env (LetS b) = do
    ((f,Embed e1), e) <- unbind b -- letS f = e1 in e
    e1' <- expand env e1
    expand ((f,e1'):env) e
expand env (LetRecS b) = do
    (r, e) <- unbind b -- letS f = e1 in e
    let (f,Embed e1) = unrec r
    e1' <- expand ((f,e1):env) e1
    expand ((f,e1'):env) e

lamS x = LamS . bind x
letS f body = LetS . bind (f, embed body)
letrecS f body = LetRecS . bind (rec (f, embed body))

e99 = letS gt ( lamS x . lamS y $ Less _y _x ) $
      letS eq ( lamS x . lamS y $ Less (Less _x _y `Plus` _gt _x _y) _1 ) $
      _eq _u _v 
    where
        gt = s2n "gt"
        eq = s2n "eq"
        x = s2n "?x"
        y = s2n "?y"
        _gt a b = Var gt `App` a `App` b
        _eq a b = Var eq `App` a `App` b
        _x = Var x
        _y = Var y
        u = s2n "u"
        v = s2n "v"
        _u = Var u
        _v = Var v
        _1 = Const 1

e98 = letS gt ( lamS x . lamS y $ Less _y _x ) $
      letS eq ( lamS x . lamS y $ Less (Plus (Less _x _y) (_gt _x _y)) (Const 1) ) $
      letrecS mul ( lamS x . lamS y $
                    If (Less _y _1) _0
                                    (_x `Plus` _mul _x (Plus _y (Const (-1)))) ) $
      _mul _u _5
    where
        gt = s2n "gt"
        eq = s2n "eq"
        mul = s2n "mul" -- 양수끼리 곱셈만 고려
        x = s2n "?x"
        y = s2n "?y"
        _gt a b = Var gt `App` a `App` b
        _eq a b = Var eq `App` a `App` b
        _mul a b = Var mul `App` a `App` b
        _x = Var x
        _y = Var y
        u = s2n "u"
        v = s2n "v"
        _u = Var u
        _v = Var v
        _0 = Const 0
        _1 = Const 1
        _5 = Const 5

-- >>> runFreshM (expand [] e99)
-- Less (Plus (Less (Var u) (Var v)) (Less (Var v) (Var u))) (Const 1)

-- >>> runFreshM (expand [] e98)
-- Plus (Var u) (Plus (Var u) (Plus (Var u) (Plus (Var u) (Var u))))



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
