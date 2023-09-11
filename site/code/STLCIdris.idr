-- From Lambda Calculus to Bicartesian Closed Categories, Part 1

-- TODO: manually get these
import Data.List.Elem 
import BCC
import Prelude 

Multigraph : Type -> Type 
Multigraph a = List a -> a -> Type 

data LPrims : Multigraph Ty where
  -- the unit for the monoid takes an empty list of inputs - this is equivalent to a morphism from the unit type as before
  LE : LPrims Nil N 
  -- the monoid multiplication now takes two elements - this is equivalent to a morphism from a product of elements
  LMult : LPrims [N, N] N

data CPrims : Multigraph Ty where
  -- the unit for the monoid takes an empty list of inputs - this is equivalent to a morphism from the unit type as before
  E : CPrims g N  
  -- the monoid multiplication now takes two elements - this is equivalent to a morphism from a product of elements
  Mult : CPrims (N :: N :: g) N
  Neg : CPrims (N :: g) N
-- we're splitting the context into parts that we're using, and the remainder. 

namespace Snoc
  data List' a = Lin | Snoc (List' a) a

  infixr 5 -:
  (-:) : List' a -> a -> List' a 
  (-:) = Snoc

  data Term : List' Ty -> Ty -> Type where
    Lam : {a, b : Ty} -> Term (g -: a) b -> Term g (a ~> b)
    -- Lambda application
    App : {a, b : Ty} -> Term g (a ~> b) -> Term g a -> Term g b

data Term : Multigraph Ty where
  -- Primitives
--  CPrim : {g : List Ty} -> {a : Ty} -> CPrims g a -> Term g a 
  LPrim : {g : List Ty} -> {a : Ty} -> LPrims g a -> Term g a 
  -- Variables 
  Var : {a : Ty} -> {g : List Ty} -> Elem a g -> Term g a
  -- Lambda abstraction
  Lam : {g : List Ty} -> {a, b : Ty} -> Term (a::g) b -> Term g (a ~> b)
  -- this is the most interesting rule as it shows a manipulation of contexts - the free variable 'a' is taken from the context and bound in the term
  -- Lambda application
  App : {a, b : Ty} -> Term g (a ~> b) -> Term g a -> Term g b
  -- Products
  Pair : {a, b : Ty} -> Term g a -> Term g b -> Term g (Prod a b)
  Fst : {a, b : Ty} -> Term g (Prod a b) -> Term g a
  Snd : {a, b : Ty} -> Term g (Prod a b) -> Term g b
  -- Coproducts
  InL : {a, b : Ty} -> Term g a -> Term g (Sum a b)
  InR : {a, b : Ty} -> Term g b -> Term g (Sum a b)
  Case : {g : List Ty} -> {a, b, c : Ty} -> Term g (Sum a b) -> Term (a::g) c -> Term (b::g) c -> Term g c
  -- Let binding
  Let : {s : Ty} -> Term ctx s -> Term (s :: ctx) t -> Term ctx t

{-- It would have been possible to define our primitive elements inside of our Terms as well, such as 
  E : Term g N  
  -- the monoid multiplication now takes two elements - this is equivalent to a morphism from a product of elements
  Mult : Term g N -> Term g N -> Term g N
But this would break the conceptual separation between the primitives and the connectives built on top of them.
Our way of presenting things is also suggestive of a deeper insight into the relationship between the lambda calculus and BCC combinators - while the combinators are free over a set of edges, the lambda calculus is free over a set of "edges with multiple inputs", aka edges of a multi-graph. 

--}

evalTy : Ty -> Type
evalTy Unit = Unit
evalTy N = Nat
evalTy (Exp t1 t2) = (evalTy t1) -> (evalTy t2)
evalTy (Prod t1 t2) = (evalTy t1, evalTy t2)
evalTy (Sum t1 t2) = Either (evalTy t1) (evalTy t2) 

{--
We then need to define a notion of environment. 
The cruicial difference from before is that whereas combinators have one input and output, now we have a list of inputs, represented by our context
This corresponds to evaluating our term into a function from an environment of inputs. 
--}

-- Cons list, Extend environment from the left
infixr 5 ::-
data Env : List Ty -> Type where
  CNil  : Env Nil
  (::-) : evalTy t -> Env g -> Env (t :: g)

-- Snoc list, extend environment from the right
infixr 5 -::
(-::) : {t : Ty} -> (env : Env ctxt) -> (obj : evalTy t) -> Env (t::ctxt)
(-::) env obj = obj ::- env
  
lookup : Elem t g -> Env g -> evalTy t
lookup = ?xx 

-- We could, for instance, write a function that takes two variables and binds them to our primitive 
-- Nat -> Nat -> Nat

--ex : {g : List Ty} -> Term g (N ~> (N ~> N)) 
--ex = Lam (Lam (CPrim Mult)) 

ex' : {g : List Ty} -> Term Nil (N ~> (N ~> N)) 
ex' = Lam (Lam (LPrim LMult)) 

evalPrims : CPrims g t -> (Env g -> evalTy t)
evalPrims E env = 0 -- ignore the environment
evalPrims Neg (m1 ::- env) = m1 -- pop the first value from the environment and negate it
evalPrims Mult (m1 ::- m2 ::- env) = m1 + m2 -- pop the first two values from the environment and add them 

evalPrims' : LPrims g t -> (Env g -> evalTy t)
evalPrims' LE env = 0 -- ignore the environment
evalPrims' LMult (m1 ::- m2 ::- env) = m1 + m2 -- pop the first two values from the environment and add them 

-- then our evaluator will take a term and give back a function from an environment to a term
eval : {g : List Ty} -> Term g t -> (Idr (Env g) (evalTy t))
eval (Var v) env = lookup v env
--eval (CPrim e) env = evalPrims e env
eval (LPrim e) env = evalPrims' e env
eval (Lam t) env = \x => (eval t) (x ::- env) 
eval (App t1 t2) env = (eval t1 env) (eval t2 env)
eval (Pair t1 t2) env = (eval t1 env, eval t2 env)
eval (Fst t) env = fst (eval t env)
eval (Snd t) env = snd (eval t env)
eval (Let t c) env = eval c (env -:: (eval t env))
eval (InL t) env = Left (eval t env) 
eval (InR t) env = Right (eval t env) 
eval (Case t1 t2 t3) env = case (eval t1 env) of 
  Left l => eval t2 (env -:: l)
  Right r => eval t3 (env -:: r)


-- Convert a context into a tuple
ctxToProd : List Ty -> Ty 
ctxToProd tys = foldr Prod Unit tys 

ctxToProd' : List Ty -> Ty 
ctxToProd' Nil = Unit
ctxToProd' [t] = t
ctxToProd' (t::ts) = Prod t (ctxToProd' ts) 

ctxToProd'' : List Ty -> Ty 
ctxToProd'' Nil = Unit
ctxToProd'' (t::ts) = Prod t (ctxToProd'' ts) 

{--
Here is an interesting thing about the translation. If we had chosen to use the linear primitives that use each variable in the context, and nothing else, then our translation between primitives would be trivial. 
--}

-- Cant use? 
evalPrim : {g : List Ty} -> LPrims g t -> Prims (ctxToProd' g) t 
evalPrim LE = E
evalPrim LMult = Typed.Mult


{--
Unfortunately, the translation from a cartesian context is a little bit trickier. Instead of simply converting between primitives, we will use some structural operations within our BCC language to manipulate the contexts
--}


evalPrim' : {ctx : List Ty} -> CPrims ctx t -> Comb Prims (ctxToProd' ctx) t 
evalPrim' E = Prim Typed.E <<< Terminal
evalPrim' {ctx=N::Nil} Neg = Prim {k=Prims} Typed.Neg 
evalPrim' {ctx=N::m::g} Neg = (Prim {k=Prims} Typed.Neg) <<< Typed.Fst
evalPrim' {ctx=N::N::Nil} Mult = Prim {k=Prims} Typed.Mult 
-- works, we're also expanding ctx by an extra variable
evalPrim' {ctx=N::N::m::Nil} Mult = Comp (Comp (Prim {k=Prims} Typed.Mult) ?d2) SwapP
evalPrim' {ctx=N::N::m::g} Mult = Comp (Prim {k=Prims} Typed.Mult) ?d3 
 
{--
infixr 5 :::  
data List' : Type -> Type where 
  Nil' : List' a 
  In' : a -> List' a 
  (:::) : List' a -> List' a -> List' a 

fProd : List' Ty -> Ty 
fProd Nil' = Unit
fProd (In' t) = t
fProd (t:::ts) = Prod (fProd t) (fProd ts) 

data Elem' : a -> List' a -> Type where 
  Here' : Elem' x ((In' x) ::: xs)
  There' : Elem' x xs -> Elem' x (y:::xs)

env' : {g : Graph Ty} -> {ctx: List' Ty} -> {ty : Ty} -> Elem' ty ctx -> Comb g (fProd ctx) ty
env' {ctx}  Here' = ?z0 Id 
env' {ctx=(x:::x2:::g)}  Here = Typed.Fst
env' {ctx=(x:::y:::Nil')} ((There (Here {x=y}))) = Typed.Snd 
env' {ctx=(x:::y:::xs)}  ((There t)) = Comp  (env' {ctx=y:::xs} t) Typed.Snd
--}

env : {g : Graph Ty} -> {ctx: List Ty} -> {ty : Ty} -> Elem ty ctx -> Comb g (ctxToProd' ctx) ty
env {ctx=(x::Nil)}     Here = Id 
env {ctx=(x::y::g)}    Here = Fst
env {ctx=(x::y::xs)} ((There t)) = Comp (env t) Snd

env' : {g : Graph Ty} -> {ctx: List Ty} -> {ty : Ty} -> Elem ty ctx -> Comb g (ctxToProd'' ctx) ty
env' {ctx=(x::Nil)}     Here = Comp Id UnitL
env' {ctx=(x::x2::g)}   Here = Fst 
env' {ctx=(x::y::xs)} ((There t)) = Comp (env' t) Snd

--env1 : Comb Prims N N
--env1 = env {ctx = [N]} Here 
--
--env2 : Comb Prims (Prod Unit N) N
--env2 = env {ctx = [Unit, N]} (There Here) 
--
--env3 : Comb Prims (Prod N Unit) N
--env3 = env {ctx = [N, Unit]} Here 
--
--env4 : Comb Prims (Prod N Unit) Unit
--env4 = env {ctx = [N, Unit]} (There Here) 

-- here we have a small mismatch between Proj and Fst, one acts on morphisms and one acts on objects.
-- we can fix this by composing a projection with the output of the evaluation

sem : {ctx: List Ty} -> {ty : Ty} -> Term ctx ty -> Comb Prims (ctxToProd'' ctx) ty
sem (Var v) = env' v
sem  (LPrim e) = case e of 
  LE => Prim Typed.E
  LMult => (BifP Id UnitL) >>> Prim Typed.Mult
sem (Pair t1 t2) = ProdI (sem t1) (sem t2)
sem (Snd t) = sem t >>> Snd 
sem (Fst t) = sem t >>> Fst 
sem (Lam t) = let x = sem t in (Curry (SwapP >>> x))  
sem (App t1 t2) = Apply <<< (ProdI (sem t1) (sem t2)) 
sem (Let t c) = let evc = sem (Lam c) 
                    evt = sem t in 
                      Apply <<< (ProdI evc evt)
sem (InL t) = sem t >>> InL  
sem (InR t) = sem t >>> InR
sem (Case t1 t2 t3) = Copy >>> BifP (sem t1) Id >>> Distrib >>> BifC (sem t2) (sem t3) >>> Cocopy

{-}
m1 : g -> a + b 
m2 : (a * g) -> ty 
m3 : (b * g) -> ty 
----------------------
g -> ty 
```

As an Idris expression, it would look like this:

```

\g => case g of 
  Left a => m2 (a, g)
  Right b => m3 (b, g)
