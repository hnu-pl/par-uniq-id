{-# LANGUAGE NoMonomorphismRestriction, DeriveGeneric, MultiParamTypeClasses #-}
module Main where

import Lib

import Control.Concurrent.MVar.Strict

import Control.Parallel.Strategies
import Control.Monad.Trans.State.Strict
import Control.Monad
import Control.Monad.Fail
import Data.List
import System.Environment

import qualified Control.Monad.Parallel as MP

import GHC.Generics ( Generic )
import Data.Typeable ( Typeable )
import Unbound.Generics.LocallyNameless
import Unbound.Generics.LocallyNameless.Internal.Fold

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
    = Const Integer          -- n
    | Var Nm                 -- x
    | Plus Expr Expr         -- e1 + e2
    | Mult Expr Expr         -- e1 * e2
    | Div  Expr Expr         -- e1 / e2
    | Less Expr Expr         -- e1 < e2
    | If Expr Expr Expr      -- if e e1 e0
    | Lam (Bind Nm Expr)     -- \x.e
    | LetRec (Bind (Rec (Nm, Embed Expr)) Expr)  -- letrecS f = e1 in e2
    | App Expr Expr          -- e e
    | Brk Expr               -- <e>
    | Esc Expr               -- ~e 
    | Run Expr               -- !e
    deriving (Show, Generic, Typeable)

instance Alpha Expr
instance Subst Expr Expr where
  isvar (Var  x) = Just (SubstName x)
  isvar _     = Nothing

eval k e  | k < 0    = fail $ show e++" at impossible (negative) level "++show k
eval _ e@(Const n)   = return e
eval 0 e@(Var x)     = fail $ show x++" at level 0"
eval k e@(Var x)     = return e
eval 0 (Plus e1 e2)  = do
    Const n1 <- eval 0 e1
    Const n2 <- eval 0 e2
    return $ Const (n1 + n2)
eval 0 (Mult e1 e2)  = do
    Const n1 <- eval 0 e1
    Const n2 <- eval 0 e2
    return $ Const (n1 * n2)
eval 0 (Div e1 e2)  = do
    Const n1 <- eval 0 e1
    Const n2 <- eval 0 e2
    return $ Const (n1 `div` n2)
eval 0 (Less e1 e2)  = do
    Const n1 <- eval 0 e1
    Const n2 <- eval 0 e2
    return $ Const (if n1 < n2 then 1 else 0)
eval k (Plus e1 e2)  = Plus <$> eval k e1 <*> eval k e2
eval k (Mult e1 e2)  = Mult <$> eval k e1 <*> eval k e2
eval k (Div  e1 e2)  = Div  <$> eval k e1 <*> eval k e2
eval k (Less e1 e2)  = Less <$> eval k e1 <*> eval k e2
eval 0 (If e e1 e0)  = do
    Const n <- eval 0 e
    if n==0 then eval 0 e0 else eval 0 e1
eval k (If e e1 e0)  = If <$> eval k e <*> eval k e1 <*> eval k e0
eval 0 e@(Lam _)     = return e
eval k e@(Lam b)     = do
    (x,e) <- unbind b
    e' <- eval k e
    return $ Lam (bind x e')
eval 0 (App e1 e2)   = do
    Lam b <- eval 0 e1
    e2' <- eval 0 e2
    (x,e) <- unbind b
    eval 0 $ subst x e2' e
eval k (App e1 e2)  = App <$> eval k e1 <*> eval k e2
eval 0 e@(LetRec b)  = do
    (r,e2) <- unbind b
    let (f,Embed e1) = unrec r
    let e1' = subst f (LetRec (bind (rec(f, embed e1)) (Var f))) e1
    eval 0 $ subst f e1' e2
eval k e@(LetRec b)  = do
    (r,e2) <- unbind b
    let (f,Embed e1) = unrec r
    e1' <- eval k e1
    e2' <- eval k e2
    return $ LetRec (bind (rec(f, embed e1')) e2')
eval k (Brk e)  = Brk <$> eval (k+1) e
eval 0 (Esc e)  = error $ show e++" cannot escape at level 0"
eval 1 (Esc e)  = do
    Brk e' <- eval 0 e
    return e'
eval k (Esc e)  = Esc <$> eval (k-1) e
eval 0 (Run e)  = do
    Brk e' <- eval 0 e
    eval 0 e'
eval k (Run e)  = Run <$> eval k e

lam x = Lam . bind x
letrec f body = LetRec . bind (rec (f, embed body))



e01 = Run $ Brk _1
    where 
        _1 = Const 1

-- >>> runFreshMT (eval 0 e01)
-- Const 1


e02 = Run $ Brk (Esc (Brk _1))
    where 
        _1 = Const 1

-- >>> runFreshMT (eval 0 e02)
-- Const 1

e03 = Run . Brk $ Esc(Brk _1) `Less` Esc(Brk _1)
    where 
        _1 = Const 1
        _2 = Const 2

-- >>> runFreshMT (eval 0 e03)
-- Const 0


e99 = letrec gt -- \x y . < ~y < ~x >
             ( lam x . lam y . Brk $ Esc _y `Less` Esc _x ) $
      letrec eq -- \x y . < (~x < ~y) + ~(gt _x _y) < 1 >
             ( lam x . lam y . Brk $ Less (Less (Esc _x) (Esc _y) `Plus` Esc(_gt _x _y)) _1 ) $
      Run $ _eq (Brk _1) (Brk _2)
    where
        gt = s2n "gt"
        eq = s2n "eq"
        x = s2n "x"
        y = s2n "y"
        _gt a b = Var gt `App` a `App` b
        _eq a b = Var eq `App` a `App` b
        _x = Var x
        _y = Var y
        u = s2n "u"
        v = s2n "v"
        _u = Var u
        _v = Var v
        _1 = Const 1
        _2 = Const 2


-- >>> runFreshMT (eval 0 e99)
-- Const 0




-- >>> runFreshMT (eval 0 e98)
-- Brk (Mult (Var u) (App (Lam (<z19> Mult (Var 0@0) (Var 0@0))) (App (Lam (<z28> Mult (Var 0@0) (Var 0@0))) (Mult (Var u) (Const 1)))))

e98 = letrec gt -- \x y . y < x
             ( lam x . lam y $ _y `Less` _x ) $
      letrec eq -- \x y . (x < y) + (gt x y) < 1
             ( lam x . lam y $ Less (Less _x _y `Plus` _gt _x _y) _1 ) $
      letrec evn -- \x . < \y . eq y <~y / 2 * 2> ) >
             ( lam x $ _eq _x (Mult (Div _x _2) _2) ) $
      letrec exp {- \x y -> if (y < 1)
                              then < 1 >
                              else if (evn y)
                                then < (\x -> x*x) ~(exp x (y/2)) >
                                else < x * ~(exp x (y + -1)) >
                  -}
             ( lam x . lam y $ -- x는 코드(문법트리) y는 그냥 값이 넘어오고
                    If (Less _y _1) (Brk _1) $
                    If (_evn _y)  (Brk (lam z (Mult _z _z) `App` Esc(_exp _x (Div _y _2)))) $
                                  (Brk (Esc _x `Mult` Esc(_exp _x (Plus _y (Const (-1))))))
                                              ) $
      _exp (Brk _u) _5
    where
        gt = s2n "gt"
        eq = s2n "eq"
        exp = s2n "exp" -- 음수가 아닌 거듭제곱만 고려
        evn = s2n "evn" -- 음수가 아닌 거듭제곱만 고려
        x = s2n "x"
        y = s2n "y"
        z = s2n "z"
        _gt a b = Var gt `App` a `App` b
        _eq a b = Var eq `App` a `App` b
        _exp a b = Var exp `App` a `App` b
        _evn a = Var evn `App` a
        _x = Var x
        _y = Var y
        _z = Var z
        u = s2n "u"
        v = s2n "v"
        _u = Var u
        _v = Var v
        [_0,_1,_2,_3,_4,_5] = Const <$> [0..5]


-- >>> runFreshMT (eval 0 (e97 3))
-- Brk (Plus (Plus (Plus (Const 1) (Mult (Var u) (Const 1))) (App (Lam (<z23> Mult (Var 0@0) (Var 0@0))) (Mult (Var u) (Const 1)))) (Mult (Var u) (App (Lam (<z50> Mult (Var 0@0) (Var 0@0))) (Mult (Var u) (Const 1)))))

e97 n = letrec gt -- \x y . y < x
             ( lam x . lam y $ _y `Less` _x ) $
      letrec eq -- \x y . (x < y) + (gt x y) < 1
             ( lam x . lam y $ Less (Less _x _y `Plus` _gt _x _y) _1 ) $
      letrec evn -- \x . < \y . eq y <~y / 2 * 2> ) >
             ( lam x $ _eq _x (Mult (Div _x _2) _2) ) $
      letrec exp {- \x y -> if (y < 1)
                              then < 1 >
                              else if (evn y)
                                then < (\x -> x*x) ~(exp x (y/2)) >
                                else < x * ~(exp x (y + -1)) >
                  -}
             ( lam x . lam y $ -- x는 코드(문법트리) y는 그냥 값이 넘어오고
                    If (Less _y _1) (Brk _1) $
                    If (_evn _y)  (Brk (lam z (Mult _z _z) `App` Esc(_exp _x (Div _y _2)))) $
                                   Brk (Esc _x `Mult` Esc(_exp _x (Plus _y (Const (-1))))) 
                                              ) $
      Brk ( foldl1 Plus [Esc(_exp (Brk _u) (Const i)) | i<-[0..n]] ) -- < ~(exp u 0) + ~(exp u 1) + ... + ~(exp u n) >
    where
        gt = s2n "gt"
        eq = s2n "eq"
        exp = s2n "exp" -- 음수가 아닌 거듭제곱만 고려
        evn = s2n "evn" -- 음수가 아닌 거듭제곱만 고려
        x = s2n "x"
        y = s2n "y"
        z = s2n "z"
        _gt a b = Var gt `App` a `App` b
        _eq a b = Var eq `App` a `App` b
        _exp a b = Var exp `App` a `App` b
        _evn a = Var evn `App` a
        _x = Var x
        _y = Var y
        _z = Var z
        u = s2n "u"
        v = s2n "v"
        _u = Var u
        _v = Var v
        [_0,_1,_2,_3,_4,_5] = Const <$> [0..5]


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

example1 = runPar (sequence <$> [ [fresh(s2n "x")], [fresh(s2n "x"), fresh(s2n "x"), fresh(s2n "x")], [fresh(s2n "x"), fresh(s2n "x")] ])

bench1 :: Int -> Int -> [Name a]
bench1 n m = runFreshM . runPar $ replicate n (foldl1 (>>) $ replicate m (fresh(s2n "x")))

{-
-- x1^m + x2^m + ... + xn^m
bench2 n m = runFreshM $ do
    vs <- replicateM (fromIntegral n) (fresh $ s2n "v")
    expand [] (e96 vs n m)
-}

main = do
    a0:a1:a2:_ <- getArgs
    let k = read a0 :: Int
        n = read a1 :: Integer
        m = read a2 :: Integer
    case k of
        1 -> do
            putStrLn $ " bench1 "++show n++" "++show m
            print $ bench1 (fromIntegral n) (fromIntegral m)
{-}
        2 -> do
            putStrLn $ " bench2 "++show n++" "++show m
            let e2 = bench2 n m -- u^(n^m) 을 expand
            print $ length (toListOf fv e2 :: [Nm]) -- u^(n^m) 을 expand
-}



{-
newIdMVar :: MVar Int -> IO Int
newIdMVar c = modifyMVar c (\n -> return (n+1,n))
bench2 n m = do
    c <- newMVar (0 :: Int)
    let new = newIdMVar c
    print . maximum =<< MP.replicateM n (foldl1 (>>) $ replicate m new)

-}
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

