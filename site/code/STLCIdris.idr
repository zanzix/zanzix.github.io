-- From Lambda Calculus to Bicartesian Closed Categories, Part 1

-- TODO: manually get these
import Data.List.Elem 
import BCC
import Prelude 


Multigraph : Type -> Type 
Multigraph a = List a -> a -> Type 

data LinPrims : Multigraph Ty where
  -- the unit for the monoid takes an empty list of inputs - this is equivalent to a morphism from the unit type as before
  E' : LinPrims Nil N 
  -- the monoid multiplication now takes two elements - this is equivalent to a morphism from a product of elements
  Mult' : LinPrims [N, N] N

data Prims' : Multigraph Ty where
  -- the unit for the monoid takes an empty list of inputs - this is equivalent to a morphism from the unit type as before
  E : Prims' g N  
  -- the monoid multiplication now takes two elements - this is equivalent to a morphism from a product of elements
  Mult : Prims' (N :: N :: g) N
  Neg : Prims' (N :: g) N
-- we're splitting the context into parts that we're using, and the remainder. 

namespace Snoc
  data List' a = Lin | Snoc (List' a) a

  infixr 5 -:
  (-:) : List' Ty -> Ty -> List' Ty 
  (-:) = Snoc

  data Term : List' Ty -> Ty -> Type where
    Lam : {a, b : Ty} -> Term (g -: a) b -> Term g (a ~> b)
    -- Lambda application
    App : {a, b : Ty} -> Term g (a ~> b) -> Term g a -> Term g b

data Term : Multigraph Ty where
  -- Primitives
  Prim' : {g : List Ty} -> {a : Ty} -> Prims' g a -> Term g a 
  -- Variables 
  Var : {a : Ty} -> {g : List Ty} -> Elem a g -> Term g a
  -- Lambda abstraction
  Lam : {a, b : Ty} -> Term (a::g) b -> Term g (a ~> b)
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
  Case : {a, b, c : Ty} -> Term g (Sum a b) -> Term (a::g) c -> Term (b::g) c -> Term g c
  TT   : Term g Unit
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

  -- ,- for cons and -, for snoc

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
ex : {g : List Ty} -> Term g (N ~> (N ~> N)) 
ex = Lam (Lam (Prim' Mult)) 

--ex' : {g : List Ty} -> Term g (N ~> (N ~> N)) 
--ex' = Lam (Lam (Prim' Mult)) 

evalPrims : Prims' g t -> (Env g -> evalTy t)
evalPrims E env = 0 -- ignore the environment
evalPrims Neg (m1 ::- env) = m1 -- pop the first value from the environment and negate it
evalPrims Mult (m1 ::- m2 ::- env) = m1 + m2 -- pop the first two values from the environment and add them 

-- then our evaluator will take a term and give back a function from an environment to a term
eval : {g : List Ty} -> Term g t -> (Idr (Env g) (evalTy t))
eval (Var v) env = lookup v env
eval (Prim' e) env = evalPrims e env
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
eval TT env = ()


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

help : TypedBCC k (Prod a b) c -> TypedBCC k a c 
help = ?helps 

addU : TypedBCC k a c -> TypedBCC k (Prod a Unit) c 
addU = ?helps'

dropU : TypedBCC k (Prod a Unit) c -> TypedBCC k a c 
dropU = ?d

dropN : TypedBCC k (Prod a (Prod b c)) (Prod a b)  
dropN = ?d1x

{--
Here is an interesting thing about the translation. If we had chosen to use the linear primitives that use each variable in the context, and nothing else, then our translation between primitives would be trivial. 
--}

evalPrim : {g : List Ty} -> LinPrims g t -> Prims (ctxToProd' g) t 
evalPrim E' = E
evalPrim Mult' = Typed.Mult

{--
Unfortunately, the translation from a cartesian context is a little bit trickier. Instead of simply converting between primitives, we will use some structural operations within our BCC language to manipulate the contexts
--}

evalPrim' : {ctx : List Ty} -> Prims' ctx t -> TypedBCC Prims (ctxToProd' ctx) t 
evalPrim' {ctx} E = Comp (Prim {k = Prims} Typed.E) Terminal
evalPrim' {ctx=N::Nil} Neg = Prim {k=Prims} Typed.Neg 
evalPrim' {ctx=N::m::g} Neg = Comp (Prim {k=Prims} Typed.Neg) Typed.Fst
evalPrim' {ctx=N::N::Nil} Mult = Prim {k=Prims} Typed.Mult 
-- works, we're also expanding ctx by an extra variable
evalPrim' {ctx=N::N::m::Nil} Mult = Comp (Comp (Prim {k=Prims} Typed.Mult) ?d2) Swap 
evalPrim' {ctx=N::N::m::g} Mult = Comp (Prim {k=Prims} Typed.Mult) ?d3 

-- here we have a small mismatch between Proj and Fst, one acts on morphisms and one acts on objects.
-- we can fix this by composing a projection with the output of the evaluation
{-}
sem : {ctx: List Ty} -> {ty : Ty} -> Term ctx ty -> TypedBCC Prims (ctxToProd' ctx) ty
sem {ctx=(x::Nil)}    (Var Here) = Id
--sem {ctx=(x::xs)}     (Var (Here {x, xs})) = Typed.Fst
sem {ctx=(x::x2::g)}  (Var Here) = Typed.Fst
sem {ctx=(x::y::Nil)} (Var (There (Here {x=y}))) = Typed.Snd 
sem {ctx=(x::y::xs)}  (Var (There (Here {x=y}))) = Comp  ?f1 Typed.Snd 
--  (Typed.Fst {a=y, b=ctxToProd' xs}) 
sem {ctx=(x::xs)} (Var (There t)) = Comp  (sem {ctx=xs} (Var t)) ?f1'
sem (Prim' e) = evalPrim' e
sem (Pair t1 t2) = ProdI (sem t1) (sem t2) 
sem (Snd t) = Comp Snd (sem t)
sem (Fst t) = Comp Fst (sem t)
sem (Lam {a} t) = ?cs --Curry (sem t) 
sem (App t1 t2) = Comp Apply (ProdI (sem t1) (sem t2)) 
sem (Let t c) = ?evs -- encode as Lambda
sem (InL t) = ?l2 --Left (eval t env) 
sem (InR t) = ?l1 --Right (eval t env) 
sem (Case t1 t2 t3) = ?cas --Comp (CoprodI (help (sem t2)) (help (sem t3))) (sem t1) 
sem TT = ?u

{-- Re-using the interpreter for BCCs before, our final translation from the lambda calculus to a BCC becomes

--}
-- just as above, it's a morphism from a product of objects into an object
--interp : {ctx: List Ty} -> {ty : Ty} -> (b : BCC g) -> Term ctx ty -> g (b.ty (ctxToProd' ctx)) (b.ty ty)
--interp b t = eval' b (sem t) 
