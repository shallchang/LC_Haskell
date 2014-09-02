module Main where

import Prelude hiding (readList)
import Control.Applicative

main = do
      --input <- reader
      --let context = (context_builder input [])
      --putStrLn(context_to_string context)
      
      putStrLn "Please input a term"
      term <- getLine
      let recorder = ['A'..'Z']
      
      let new_term = to_term term
      
      putStrLn("-------------------------------------------------")
      let ((p, tp), _) = ppc new_term recorder 
      --let (sub, pre) = eval_type new_term context
      putStrLn(tostring new_term ++ "      " ++  context_to_string p ++ " |- "++ tostring new_term ++ ":" ++ pretostring tp)
      
      recur_eval new_term
      

xgc = do
      putStrLn "Please input a term"
      term <- getLine
      let recorder = ['A'..'Z']
     
      let new_term = to_term term
      

      putStrLn("-------------------------------------------------")
      let ((p, tp), _) = ppc new_term recorder 
      --let (sub, pre) = eval_type new_term context
      putStrLn(tostring new_term ++ "      " ++  context_to_string p ++ " |- "++ tostring new_term ++ ":" ++ pretostring tp)
      
      recur_evalxgc new_term
    


--Type assignment data types

data Type = TP Type Type | TVar [Char]
            deriving (Show, Eq)
            
type Predicate = Type
type Context = [Statement]
type Statement = (Subject, Predicate)

type Subject = Term

type Derivation = (Context, [Statement], Statement)

type PPc = (Context, Type)

data TSub = Sub (Type, Type) | So (TSub, TSub)
            deriving (Show, Eq)




{-|
  Type parser
-}

reader :: IO [String]
reader = do
          putStrLn "type in statements!" 
          l <- getLine
          if head l == '.' then return []
           else (l :) <$> reader


--predicate to string
pretostring :: Predicate -> String
pretostring (TP x y) = "(" ++ pretostring x ++ "->" ++ pretostring y ++ ")"
pretostring (TVar (x:xs)) | xs == [] = [x]
                          | otherwise = [x] ++  "->" ++ (pretostring (TVar xs))                         
                                      
                   


--statement to string
stat_to_string :: Statement -> String
stat_to_string (x, y) = (tostring x) ++ ":" ++ (pretostring y)

--context to string
context_to_string :: Context -> String
context_to_string (x:xs) | xs == [] =  stat_to_string x
                         | otherwise = stat_to_string x ++ ", " ++ context_to_string xs
context_to_string [] = []

 
 

{-|
  Type assignment mechanism
-}
 
 
--derivation rules

drules :: [Derivation] -> Statement
--rules I
drules ((context, (Var x, TVar (pre1:[])):[], (m, TVar (pre2:[]))):[]) = ((Abs x m), TP (TVar [pre1]) (TVar [pre2]))
--rule E
drules ((context1, [], (m1, TVar [a, b]) ):[(context2, [], (m2, TVar [a2]))]) | (context1 == context2 && a == a2) =  ((App m1 m2), TVar [b])



--evaluate a term and the type

eval_type :: Term -> Context -> Statement
eval_type (App (App x y) t) context = drules ((context, [], (s1, p1)):[(context, [], (s2, p2))])
                                          where (s1, p1) = eval_type (App x y) context
                                                (s2, p2) = eval_type t context
eval_type (App (Abs x y) t) context = drules ((context, [], (s1, p1)):[(context, [], (s2, p2))])
                                          where (s1, p1) = eval_type (Abs x y) context
                                                (s2, p2) = eval_type t context
eval_type (App (Var x) t) context = drules ((context, [], (s1, p1)):[(context, [], (s2, p2))])
                                          where (s1, p1) = search (Var x) context
                                                (s2, p2) = eval_type t context 
eval_type (Var x) context = search (Var x) context
eval_type (Abs x t) context = drules ((context, (s1, p1):[], (s2, p2)):[])
                                where (s1, p1) = search (Var x) context
                                      (s2, p2) = eval_type t context


--type substitution

type_subs :: TSub -> Type -> Type
type_subs (Sub((TVar [f]), c)) (TVar [x]) | [x] == [f] = c   
                                          | otherwise = TVar [x]
type_subs (Sub((TVar [f]), c)) (TP a b) = TP (type_subs (Sub((TVar [f]), c)) a) (type_subs (Sub((TVar [f]), c)) b)
type_subs (So (s1, s2))  x = so (So (s1, s2)) x


--So
so :: TSub -> Type -> Type
so (So(s1, s2)) a = type_subs s1 (type_subs s2 a)



--context substitution
context_sub :: TSub -> Context -> Context
context_sub (Sub (s, t)) ((x, y):[]) = [(x, (type_subs (Sub(s, t)) y))]
context_sub (Sub (s, t)) ((x, y):cx) = (x, (type_subs (Sub(s, t)) y)):(context_sub  (Sub (s, t)) cx)
context_sub (So (s1, s2)) ((x, y):[]) = [(x, (type_subs (So(s1, s2)) y))]
context_sub (So (s1, s2)) ((x, y):cx) = (x, (so (So(s1, s2)) y)):(context_sub  (So (s1, s2)) cx)
context_sub _ [] = []



--Robinson's Unification Algorithm

unify :: Type -> Type -> TSub
unify (TVar [x]) (TVar [y]) = Sub (TVar [x], TVar [y])
unify (TVar [x]) (TP a b)   | not (occur (TVar [x]) a) && not (occur (TVar [x]) b) = Sub (TVar [x], TP a b)
                            | otherwise = Sub (TVar "A", TVar "A")
unify (TP a b) (TVar [x]) = unify (TVar [x]) (TP a b)
unify (TP a b) (TP c d) = So (s2, s1)
                          where s1 = unify a c
                                s2 = unify (type_subs s1 b) (type_subs s1 d)



--context unification
unify_contexts :: Context-> Context -> TSub
unify_contexts ((x, a):g0) g1 | pre /= (TVar []) = So (s2, s1)
                              | otherwise = unify_contexts g0 g1
                                           where (_, pre) = search x g1
                                                 s1 = unify a pre
                                                 s2 = unify_contexts (context_sub s1 g0) (context_sub s1 g1)                                                 
                                                 
unify_contexts [] _ = Sub (TVar "A",  TVar "A")



search :: Term -> Context -> Statement
search t ((s, p):cx) | t == s = (s, p)
                     | otherwise = search t cx  
search _ [] = (Var ' ', TVar [])                    



contains :: Term -> Context -> Bool
contains t ((s, _):[]) | t == s = True
                       | otherwise = False
contains t ((s, _):cx) | t == s = True
                       | otherwise = contains t cx
contains _ [] = False                       

                       
                       
--PRINCIPAL PAIR ALGORITHM

ppc :: Term -> [Char] -> (PPc, [Char])
ppc (Var x) r = (([(Var x, f)], f), tl)
                where (f, tl) = fresh r
ppc (Abs x y) r | contains (Var x) pi = ((removeItem (Var x, a) pi, (TP a p)), tl1)       
                | otherwise = ((pi, (TP f p)), tl1)
                             where (f, tl) = fresh r
                                   ((pi, p), tl1) = ppc y tl
                                   (_, a) = search (Var x) pi
                                   
ppc (App m n) r = ((context_sub s2 (context_sub s1 (pi1++pi2)), type_subs s2 (type_subs s1 f)), tl2)
                  where (f, tl) = fresh r
                        ((pi1, p1), tl1)= ppc m tl
                        ((pi2, p2), tl2)= ppc n tl1
                        s1 = unify p1 (TP p2 f)
                        s2 = unify_contexts (context_sub s1 pi1) (context_sub s1 pi2)


--get a fresh type from the recorder

fresh :: [Char] -> (Type, [Char])
fresh x = (TVar [(head x)], tail x)


--check whether a single type variable occurs in another type

occur :: Type -> Type -> Bool
occur (TVar [x]) (TP a b) = occur (TVar [x]) a  || occur (TVar [x]) b 
occur (TVar [x]) (TVar (a:ax)) | x == a = True
                               | otherwise = occur (TVar [x]) (TVar ax)
occur _ (TVar []) = False


recur_eval :: Term -> IO()
recur_eval t | evalnormal t == t = putStrLn("")
             | otherwise = do
                         let recorder = ['A'..'Z']
                         let ((p, tp), _) = ppc term recorder
                         putStrLn("==> "++ tostring term++ "      " ++  context_to_string p ++ " |- "++ tostring term ++ ":" ++ pretostring tp)
                         recur_eval term
                           where term = evalnormal t


recur_evalxgc :: Term -> IO()
recur_evalxgc t | evalxgc t == t = putStrLn("")
                | otherwise = do
                         putStrLn("==> "++ tostring term)
                         recur_evalxgc term
                           where term = evalxgc t


to_term ::[Char] -> Term
to_term (a:exp) | a == '/' = to_abs exp
to_term [a] = to_var [a]
to_term exp = to_app exp

to_var ::[Char] -> Term
to_var [a] = Var a


to_abs ::[Char] -> Term
to_abs ('.' :rest) = if tail rest == [] then to_var rest
                     else to_app rest
to_abs (a:rest) = Abs a (to_abs rest)

to_app ::[Char] -> Term
to_app exp = App (to_term lhs)(to_term rhs)
             where (lhs, rhs) = div_sub exp
       
             
div_sub :: [Char] -> ([Char], [Char])
div_sub expr | last expr == ')' && last lhs == ')' && head (tail expr) == '/'
               = (to_expr lhs, rhs)  
             |   last expr == ')'
               = (lhs, rhs)         
             | head (tail expr) == '/' && last (init expr) == ')' 
               = (to_expr (init expr), [last expr])
             | otherwise = (init expr, [last expr])
      where (lhs, rhs) = split (init expr) [] 1


to_expr :: [Char] -> [Char]
to_expr ex | last ex == ')' && lhs == [] = rhs         
           | otherwise = ex
  where (lhs, rhs) = split (init ex) [] 1

split :: [Char] -> [Char] -> Integer -> ([Char], [Char])
split left right n 
         |  n == 1 && last left == '('  = (new_left, right)                    
         |  last left == '(' = split new_left new_right (n-1)       
         |  last left == ')' = split new_left new_right (n+1)     
         |  otherwise = split new_left new_right n           
  where new_left = init left
        new_right = (last left : right)





--lambda calculus

data Expression = Constant Integer 
                |Plus Expression Expression
                 
evaluate :: Expression -> Integer
evaluate (Constant l) = l
evaluate (Plus exp0 exp1) = 
      evaluate exp0 + evaluate exp1



type Name = Char  
 
data Term = Var Name | Abs Name Term | App Term Term | XSub Term Term Term
            deriving (Show, Eq)

          
--type Res = ReaderT Env (Either String) Value


--remove an element from a list

removeItem :: Eq a => a -> [a] -> [a]
removeItem _ [] = []
removeItem x (y:xs) = if x == y then removeItem x xs
                  else y:(removeItem x xs)

--the set of free variables of a lambda term

freevar :: Term -> [Term]
freevar (Var x) = (Var x):[]
freevar (App x y) = (freevar x) ++ (freevar y)
freevar (Abs y m) = if (Var y) `elem` (freevar m) then removeItem (Var y) (freevar m)
                            else (freevar m)
freevar (XSub m from to) = (removeItem from (freevar m)) ++ (freevar to) 
 
--normal order

evalnormal :: Term -> Term
evalnormal (Var x) = Var x
evalnormal (Abs x t) = (Abs x (evalnormal t))
evalnormal (App (Abs x t) v) = subs t (Var x, v)
evalnormal (App x t) | x == evalnormal x = (App x (evalnormal t))
                     | otherwise = (App (evalnormal x) t)



--call-by-name reduction

evalcbn :: Term -> Term
evalcbn (Var x) = Var x
evalcbn (Abs x t) = (Abs x t)
evalcbn (App (Abs x t) v) = subs t (Var x, v)
evalcbn (App x y) | x == evalcbn x = (App x y)
                  | otherwise = (App (evalcbn x) y) 

--call-by-value reduction

evalcbv :: Term -> Term
evalcbv (Var x) = Var x
evalcbv (Abs x t) = (Abs x t)
evalcbv (App (Abs x t) y) | y == evalcbv y = subs t (Var x, y)
                          | otherwise = App (Abs x t) (evalcbv y)
evalcbv (App x y) | x == evalcbv x = (App x (evalcbv y))
                  | otherwise = (App (evalcbv x) y) 


--head reduction

headreduction :: Term -> Term
headreduction (Var x) = Var x
headreduction (Abs x t) = (Abs x (headreduction t))
headreduction (App (Abs x t) y) = subs t (Var x, y)
headreduction (App x y) | x == headreduction x = (App x y)
                  | otherwise = (App (headreduction x) y) 


--call-by-value reduction

apporder :: Term -> Term
apporder (Var x) = Var x
apporder (Abs x t) = (Abs x (apporder t))
apporder (App (Abs x t) y) | apporder (Abs x t) /= (Abs x t)  = (App (apporder (Abs x t)) y)
                           | apporder (Abs x t) == (Abs x t) && apporder y /= y = (App (Abs x t) (apporder y))
                           | apporder (Abs x t) == (Abs x t) && apporder y == y = subs t (Var x, y)
apporder (App x y) | x == apporder x = (App x (apporder y))
                  | otherwise = (App (apporder x) y) 
                  
--evaluate a xgc-term

evalxgc :: Term -> Term
evalxgc (App (Abs x t) v) = XSub t (Var x) v
evalxgc (App x t) | x == evalxgc x = (App x (evalxgc t))
                     | otherwise = (App (evalxgc x) t)
evalxgc (Var x) = Var x
evalxgc (Abs x t) = (Abs x (evalxgc t))
evalxgc (XSub (Var x) from to) = if (Var x) == from then to
                                 else (Var x)
evalxgc (XSub (Abs x m) from to) =  if from `elem` (freevar (Abs x m)) then Abs x (XSub m from to)
                                    else (Abs x m)
evalxgc (XSub (App x y) from to) =  if from `elem` (freevar (App x y)) then App (XSub x from to) (XSub y from to)
                                    else (App x y)      
evalxgc (XSub (XSub x f t) from to) = if from `elem` (freevar (XSub x f t)) then XSub (evalxgc (XSub x f t)) from to
                                      else (XSub x f t)

--evaluate a xgc-term by cbn

evalcbn_xgc :: Term -> Term
evalcbn_xgc (Var x) = Var x
evalcbn_xgc (Abs x (XSub m  from to)) = (Abs x (evalxgc (XSub m from to)))
evalcbn_xgc (Abs x t) = (Abs x (evalxgc t))
evalcbn_xgc (App (Abs x t) v) = XSub t (Var x) v
evalcbn_xgc (App x t) | x == evalxgc x = (App x (evalxgc t))
                     | otherwise = (App (evalxgc x) t)
evalcbn_xgc (XSub (Var x) from to) = if (Var x) == from then to
                                 else (Var x)
evalcbn_xgc (XSub (Abs x m) from to) =  if from `elem` (freevar (Abs x m)) then Abs x (XSub m from to)
                                    else (Abs x m)
evalcbn_xgc (XSub (App x y) from to) =  if from `elem` (freevar (App x y)) then App (XSub x from to) (XSub y from to)
                                    else (App x y)      
evalcbn_xgc (XSub (XSub x f t) from to) = if from `elem` (freevar (XSub x f t)) then XSub (evalxgc (XSub x f t)) from to
                                      else (XSub x f t)

--Term susbstitution

subs :: Term -> (Term, Term) -> Term 
subs (Var x) (Var y, t) | x == y = t
                        | x /=y = Var x   


subs (Abs y m) (Var x, n) | not ((Var y) `elem` (freevar n)) &&  y /= x =  Abs y (subs m (Var x, n))
                          | y == x = Abs y m
                          | (Var y) `elem` (freevar n) && y/= x = Abs 'z' (subs (subs m (Var y, Var 'z')) (Var x, n) )       


subs (App p q) (Var y, n) = App (subs p (Var y, n)) (subs q (Var y, n))


--print a term

tostring :: Term -> String
tostring (Var x) = [x]
tostring (Abs x y) = "(/" ++ [x] ++ "." ++ (tostring y) ++ ")"
tostring (App x y) = "(" ++ tostring x ++ tostring y ++ ")"
tostring (XSub m from to) = tostring m ++ "<" ++ tostring from ++ " := " ++ tostring to ++ ">"





 






