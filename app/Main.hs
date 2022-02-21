{-# LANGUAGE NoMonomorphismRestriction, DeriveGeneric, MultiParamTypeClasses #-}
module Main where

import Lib

import Control.Concurrent.MVar.Strict

import Control.Parallel.Strategies
import Control.Monad.Trans.State.Strict
import Control.Monad
import Control.Monad.Fail
import Control.Monad.Trans.Identity
import Data.List
import System.Environment

import qualified Control.Monad.Parallel as MP

import GHC.Generics ( Generic )
import Data.Typeable ( Typeable )
import Unbound.Generics.LocallyNameless
import Unbound.Generics.LocallyNameless.Internal.Fold
import Data.Functor.Identity (Identity(runIdentity))

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
eval k (Plus e1 e2)  = do
    e1' <- eval k e1
    e2' <- eval k e2
    return $ Plus e1' e2'
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

instance MonadFail Identity where -- 그냥 Identity를 MonadFail로 만들면 됨 예전 방식이긴 하지만 ...
    fail = error

ev runM k e  | k < 0    = fail $ show e++" at impossible (negative) level "++show k
ev runM _ e@(Const n)   = return e
ev runM 0 e@(Var x)     = fail $ show x++" at level 0"
ev runM k e@(Var x)     = return e
ev runM 0 (Plus e1 e2)  = do
    [Const n1, Const n2] <- runParT runM $ ev runM 0 <$> [e1, e2]
    return $ Const (n1 + n2)
ev runM 0 (Mult e1 e2)  = do
    [Const n1, Const n2] <- runParT runM $ ev runM 0 <$> [e1, e2]
    return $ Const (n1 * n2)
ev runM 0 (Div e1 e2)  = do
    [Const n1, Const n2] <- runParT runM $ ev runM 0 <$> [e1, e2]
    return $ Const (n1 `div` n2)
ev runM 0 (Less e1 e2)  = do
    [Const n1, Const n2] <- runParT runM $ ev runM 0 <$> [e1, e2]
    return $ Const (if n1 < n2 then 1 else 0)
ev runM k (Plus e1 e2)  = do
    [e1', e2'] <- runParT runM $ ev runM k <$> [e1, e2]
    return $ Plus e1' e2'
ev runM k (Mult e1 e2)  = do
    [e1', e2'] <- runParT runM $ ev runM k <$> [e1, e2]
    return $ Mult e1' e2'
ev runM k (Div  e1 e2)  = do
    [e1', e2'] <- runPar $ ev runM k <$> [e1, e2]
    return $ Div  e1' e2'
ev runM k (Less e1 e2)  = do
    [e1', e2'] <- runPar $ ev runM k <$> [e1, e2]
    return $ Less e1' e2'
ev runM 0 (If e e1 e0)  = do
    Const n <- ev runM 0 e
    if n==0 then ev runM 0 e0 else ev runM 0 e1
ev runM k (If e e1 e0)  = do
    [e', e1', e0'] <- runPar $ ev runM k <$> [e0, e1, e0]
    return $ If e' e1' e0'
ev runM 0 e@(Lam _)     = return e
ev runM k e@(Lam b)     = do
    (x,e) <- unbind b
    e' <- ev runM k e
    return $ Lam (bind x e')
ev runM 0 (App e1 e2)   = do
    Lam b <- ev runM 0 e1
    e2' <- ev runM 0 e2
    (x,e) <- unbind b
    ev runM 0 $ subst x e2' e
ev runM k (App e1 e2)  = do
    [e1', e2'] <- runPar $ ev runM k <$> [e1, e2]
    return $ App e1' e2'
ev runM 0 e@(LetRec b)  = do
    (r,e2) <- unbind b
    let (f,Embed e1) = unrec r
    let e1' = subst f (LetRec (bind (rec(f, embed e1)) (Var f))) e1
    ev runM 0 $ subst f e1' e2
ev runM k e@(LetRec b)  = do
    (r,e2) <- unbind b
    let (f,Embed e1) = unrec r
    [e1', e2'] <- runPar $ ev runM k <$> [e1, e2]
    return $ LetRec (bind (rec(f, embed e1')) e2')
ev runM k (Brk e)  = Brk <$> ev runM (k+1) e
ev runM 0 (Esc e)  = error $ show e++" cannot escape at level 0"
ev runM 1 (Esc e)  = do
    Brk e' <- ev runM 0 e
    return e'
ev runM k (Esc e)  = Esc <$> ev runM (k-1) e
ev runM 0 (Run e)  = do
    Brk e' <- ev runM 0 e
    ev runM 0 e'
ev runM k (Run e)  = Run <$> ev runM k e


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

-- >>> runFreshMT (ev runIdentity 0 e99)
-- Identity (Const 0)

-- >>> runIdentity $ runFreshMT (ev runIdentity 0 e99)
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

e96 n = letrec gt -- \x y . y < x
             ( lam x . lam y $ _y `Less` _x ) $
        letrec eq -- \x y . (x < y) + (gt x y) < 1
             ( lam x . lam y $ Less (Less _x _y `Plus` _gt _x _y) _1 ) $
        letrec fib {- \x y -> if (y == 1)
                        then < 1 >
                        else if (y == 0)
                            then < 0 >
                            else < ~(fib (y-1)) + ~(fib (y-2)) >
                    -}
             ( lam x. lam y $
                    If (_eq _y _2 ) (Brk _1) $
                    If (_eq _y _1 ) (Brk _1) $
                    If (_eq _y _0 ) (Brk _0) $
                                     Brk ( Esc(_fib _x (Plus _y  (Const (-1)))) `Plus` Esc(_fib _x (Plus _y (Const (-2))) ))
                                     ) $ 
        Brk (foldl1 Plus [Esc(_fib (Brk _u) (Const i)) | i<-[0..n]])
    where
        gt = s2n "gt"
        eq = s2n "eq"
        fib = s2n "fib" -- 음수가 아닌 거듭제곱만 고려
        x = s2n "x"
        y = s2n "y"
        _gt a b = Var gt `App` a `App` b
        _eq a b = Var eq `App` a `App` b
        _fib a b = Var fib `App` a `App` b
        _x = Var x
        _y = Var y
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

-- x^0 + x^1 + x^2 + ... + x^n 확장/실행, x=2로
bench2 n = runFreshM $ eval 0 (Run . Brk $ lam u (Esc $ e97 n) `App` Const 2)
    where
        u = s2n "u"

-- fib test
bench22 n = runFreshM $ eval 0 (Run . Brk $ lam u (Esc $ e96 n) `App` Const 0)
    where
        u = s2n "u"

-- x^0 + x^1 + x^2 + ... + x^n 병렬 확장/실행, x=2로
bench3 n = runM . runFreshMT $ ev runM 0 (Run . Brk $ lam u (Esc $ e97 n) `App` Const 2)
    where
        u = s2n "u"
        runM = runIdentity


bench32 n = runM . runFreshMT $ ev runM 0 (Run . Brk $ lam u (Esc $ e96 n) `App` Const 0)
    where
        u = s2n "u"
        runM = runIdentity        


main = do
    a0:a1:a2:_ <- getArgs
    let k = read a0 :: Int
        n = read a1 :: Integer
        m = read a2 :: Integer -- bench2, bench3에서는 쓰지 않지만 안넘기면 에러니까 그냥 0같은 거 넘겨면됨
    case k of
        1 -> do
            putStrLn $ " bench1 "++show n++" "++show m
            print $ bench1 (fromIntegral n) (fromIntegral m)
        2 -> do
            putStrLn $ " bench2 "++show n
            print $ bench2 n
        3 -> do
            putStrLn $ " bench3 "++show n
            print $ bench3 n
        22 -> do
            putStrLn $ " bench22 "++show n
            print $ bench22 n
        32 -> do
            putStrLn $ " bench32 "++show n
            print $ bench22 n

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

{-

kyagrd@kyalu:~/github/hnu-pl/par-uniq-id$ stack run -- 2 2000 0 +RTS -s -N4
 bench2 2000
Const 229626139054850904846566640235536396804463540417739040095528547365153252278474062771331897263301253983689192927797492554689423792172611066285186271233330637078259978290624560001377558296480089742857853980126972489563230927292776727894634052080932707941809993116324797617889259211246623299072328443940665362688337817968917011204758969615828117801869553000858005433413251661044016264472562583522535766634413197990792836254043559716808084319706366503081778867804183841109915567179344078320163914433261165510760851167452031056697572838864109017830551567765250350871057601645685541635930907524369702298058751
   8,167,155,648 bytes allocated in the heap
     146,417,504 bytes copied during GC
       7,123,640 bytes maximum residency (15 sample(s))
         373,320 bytes maximum slop
               6 MB total memory in use (0 MB lost due to fragmentation)

                                     Tot time (elapsed)  Avg pause  Max pause
  Gen  0      7770 colls,  7770 par    1.052s   0.197s     0.0000s    0.0004s
  Gen  1        15 colls,    14 par    0.051s   0.015s     0.0010s    0.0019s

  Parallel GC work balance: 27.41% (serial 0%, perfect 100%)

  TASKS: 10 (1 bound, 9 peak workers (9 total), using -N4)

  SPARKS: 0 (0 converted, 0 overflowed, 0 dud, 0 GC'd, 0 fizzled)

  INIT    time    0.001s  (  0.000s elapsed)
  MUT     time    1.224s  (  1.351s elapsed)
  GC      time    1.103s  (  0.212s elapsed)
  EXIT    time    0.001s  (  0.007s elapsed)
  Total   time    2.328s  (  1.570s elapsed)

  Alloc rate    6,672,387,404 bytes per MUT second

  Productivity  52.6% of total user, 86.0% of total elapsed

kyagrd@kyalu:~/github/hnu-pl/par-uniq-id$ stack run -- 3 2000 0 +RTS -s -N4
 bench3 2000
Const 229626139054850904846566640235536396804463540417739040095528547365153252278474062771331897263301253983689192927797492554689423792172611066285186271233330637078259978290624560001377558296480089742857853980126972489563230927292776727894634052080932707941809993116324797617889259211246623299072328443940665362688337817968917011204758969615828117801869553000858005433413251661044016264472562583522535766634413197990792836254043559716808084319706366503081778867804183841109915567179344078320163914433261165510760851167452031056697572838864109017830551567765250350871057601645685541635930907524369702298058751
   9,463,963,616 bytes allocated in the heap
     400,410,504 bytes copied during GC
      19,385,728 bytes maximum residency (18 sample(s))
         492,160 bytes maximum slop
              18 MB total memory in use (0 MB lost due to fragmentation)

                                     Tot time (elapsed)  Avg pause  Max pause
  Gen  0      2360 colls,  2360 par    1.623s   0.178s     0.0001s    0.0008s
  Gen  1        18 colls,    17 par    0.142s   0.038s     0.0021s    0.0045s

  Parallel GC work balance: 89.01% (serial 0%, perfect 100%)

  TASKS: 10 (1 bound, 9 peak workers (9 total), using -N4)

  SPARKS: 2010517 (67243 converted, 351330 overflowed, 0 dud, 299032 GC'd, 1292912 fizzled)

  INIT    time    0.001s  (  0.000s elapsed)
  MUT     time    0.654s  (  0.406s elapsed)
  GC      time    1.764s  (  0.217s elapsed)
  EXIT    time    0.000s  (  0.008s elapsed)
  Total   time    2.419s  (  0.630s elapsed)

  Alloc rate    14,475,319,082 bytes per MUT second

  Productivity  27.0% of total user, 64.3% of total elapsed



-}