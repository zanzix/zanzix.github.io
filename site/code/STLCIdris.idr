-- From Lambda Calculus to Bicartesian Closed Categories, Part 1

-- TODO: manually get these
import Data.List.Elem 
import BCC
import Prelude 

Multigraph : Type -> Type 
Multigraph a = List a -> a -> Type 

namespace Snoc
  -- Snoc List
  data SList a = Lin | Snoc (SList a) a
  
  infixr 5 -:
  (-:) : SList a -> a -> SList a 
  (-:) = Snoc

  -- Terms with Snoc-lists
  data Term : SList Ty -> Ty -> Type where
    Lam : {g : SList Ty} -> Term (g  -: a) b -> Term g (a ~> b)
    App : {a, b : Ty} -> Term g (a ~> b) -> Term g a -> Term g b

-- Cartesian primitives
data CPrims : Multigraph Ty where
  CZ : CPrims g N  
  CMult : CPrims (N :: N :: g) N

-- Linear primitives
data LPrims : Multigraph Ty where
  LZ : LPrims Nil N 
  LMult : LPrims [N, N] N

-- STLC Terms
data Term : Multigraph Ty where
  -- Variables 
  Var : {g : List Ty} -> {a : Ty} -> Elem a g -> Term g a
  -- Primitives
  LPrim : {g : List Ty} -> {a : Ty} -> LPrims g a -> Term g a 
  -- Lambda abstraction: (a::g → b) → (g → (a ⇨ b))
  Lam : {g : List Ty} -> {a, b : Ty} -> Term (a::g) b -> Term g (a ~> b)
  -- Lambda application: (g → (a ~> b)) → (g → a) → (g → a)
  App : {g : List Ty} -> {a, b : Ty} -> 
    Term g (a ~> b) -> Term g a -> Term g b
  -- First projection: (g → (a * b)) → (g → a)
  Fst : {g : List Ty} -> {a, b : Ty} -> Term g (Prod a b) -> Term g a
  -- Second projection: (g → (a * b)) → (g → b)
  Snd : {g : List Ty} -> {a, b : Ty} -> Term g (Prod a b) -> Term g b
  -- Product introduction: (g → a) → (g → b) → (g → (a * b))
  Pair : {g : List Ty} -> {a, b : Ty} 
    -> Term g a -> Term g b -> Term g (Prod a b)
  -- Left injection: (g → a) → (g → a + b)
  InL : {g : List Ty} -> {a, b : Ty} -> Term g a -> Term g (Sum a b)
  -- Right injection: (g → b) → (g → a + b)
  InR : {g : List Ty} -> {a, b : Ty} -> Term g b -> Term g (Sum a b)
  -- Case matching: (g → a + b) → (a::g → c) → (b::g → c) → (g → c)
  Case : {g : List Ty} -> {a, b, c : Ty} -> 
    Term g (Sum a b) -> Term (a::g) c -> Term (b::g) c -> Term g c
  -- Let binding: (g → s) → (s::g → t) → (g → t)
  Let : {g : List Ty} -> {s : Ty} 
    -> Term g s -> Term (s::g) t -> Term g t

ex : {g : List Ty} -> Term Nil (N ~> (N ~> N)) 
ex = Lam (Lam (LPrim LMult)) 

-- Environments
infixr 5 ::-
data Env : List Ty -> Type where
  CNil  : Env Nil
  (::-) : evalTy t -> Env g -> Env (t :: g)
  
lookup : Elem t g -> Env g -> evalTy t
lookup Here (x ::- xs) = x 
lookup (There t) (y ::- xs) = lookup t xs 

-- Evaluator for primitives
evalPrims' : LPrims g t -> (Env g -> evalTy t)
evalPrims' LZ CNil = 0 
evalPrims' LMult (m1 ::- m2 ::- CNil) = m1 + m2

-- Evaluator of STLC terms into Idris
eval : {g : List Ty} -> Term g t -> Idr (Env g) (evalTy t)
eval (Var v) env = lookup v env
eval (LPrim e) env = evalPrims' e env
eval (Lam t) env = \x => eval t (x ::- env)
eval (App t1 t2) env = (eval t1 env) (eval t2 env)
eval (Pair t1 t2) env = (eval t1 env, eval t2 env)
eval (Fst t) env = fst (eval t env)
eval (Snd t) env = snd (eval t env)
eval (Let t c) env = eval c ((eval t env) ::- env)
eval (InL t) env = Left (eval t env) 
eval (InR t) env = Right (eval t env) 
eval (Case t1 t2 t3) env = case eval t1 env of 
  Left l => eval t2 (l ::- env)
  Right r => eval t3 (r ::- env)

-- Folding a context of types into a type
ctxF : List Ty -> Ty 
ctxF tys = foldr Prod Unit tys

-- An alternative evaluator
ctxEv : List Ty -> Ty 
ctxEv Nil = Unit
ctxEv [t] = t
ctxEv (t::ts) = Prod t (ctxEv ts) 

-- Evaluate primitives directly using the alternative evaluator
evalPrim : {g : List Ty} -> LPrims g t -> Prims (ctxEv g) t 
evalPrim LZ = Typed.Z
evalPrim LMult = Typed.Mult

-- Evaluate linear primitives into combinators
evalPrimF : {ctx : List Ty} -> LPrims ctx t -> Comb Prims (ctxF ctx) t
evalPrimF LZ = Prim Typed.Z
evalPrimF LMult = BifP Id UnitL >>> Prim Typed.Mult 

-- Evaluate cartesian primitives into combinators
evalPrim' : {ctx : List Ty} -> CPrims ctx t -> Comb Prims (ctxF ctx) t 
evalPrim' CZ = Terminal >>> Prim Typed.Z
evalPrim' CMult = BifP Id Fst >>> Prim Typed.Mult

-- Translate a variable into a sequence of projections
var : {g : Graph Ty} -> {ctx: List Ty} -> {ty : Ty} -> 
  Elem ty ctx -> Comb g (ctxF ctx) ty
var Here = Fst 
var (There t) = Comp (var t) Snd

-- Evaluate an STLC term into combinators 
sem : {ctx: List Ty} -> {ty : Ty} -> Term ctx ty -> Comb Prims (ctxF ctx) ty
sem (Var v) = var v
sem (LPrim e) = evalPrimF e
sem (Pair t1 t2) = ProdI (sem t1) (sem t2)
sem (Snd t) = sem t >>> Snd 
sem (Fst t) = sem t >>> Fst 
sem (Lam t) = let x = sem t in (Curry (SwapP >>> x))  
sem (App t1 t2) = (ProdI (sem t1) (sem t2)) >>> Apply  
sem (Let t c) = let evc = sem (Lam c) 
                    evt = sem t in 
                      ProdI evc evt >>> Apply
sem (InL t) = sem t >>> InL
sem (InR t) = sem t >>> InR
sem (Case t1 t2 t3) = Copy >>> BifP (sem t1) Id >>> 
  Distrib >>> BifC (sem t2) (sem t3) >>> Cocopy