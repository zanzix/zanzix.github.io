-- From Lambda Calculus to Bicartesian Closed Categories, Part 1


-- TODO: manually get these
import Data.List.Elem 

{-- 
the most important thing to notice is that even as we keep increasing the generality of our code, the general shape remains the same. 
This is going to be a recurring theme in this series. The structure of your data determines the structure of your programs.
--}

-- Now let's work with the 
infixr 5 :::
data Env : List Ty -> Type where
  CNil  : Env Nil
  (:::) : evalTy t -> Env g -> Env (t :: g)

lookup : Elem t g -> Env g -> evalTy t
lookup = ?xx 

extend : {t : Ty} -> (env : Env ctxt) -> (obj : evalTy t) -> Env (t::ctxt)
extend env obj = obj ::: env

-- TODO: check De Bruijn library: https://github.com/jfdm/idris-containers/blob/master/Data/DeBruijn.idr

public export 
data Term : List Ty -> Ty -> Type where
  -- often times people will use Ctx = List Ty as short-hand, but since we're going to look at many different calculi with their own unique notion of context, I like to be explicit here
  Prim'' : {a, b : Ty} -> Prims a b -> Term [a] b 
  Var : {a : Ty} -> {g : List Ty} -> Elem a g -> Term g a
  Lam : {a, b : Ty} -> Term (a::g) b -> Term g (a ~> b)
  -- this is the most interesting rule as it shows a manipulation of contexts - the free variable 'a' is taken from the context and bound in the term
  -- TODO: replace '::' with a comonadic 'Pop' that takes a variable from the stack
  App : {a, b : Ty} -> Term g (a ~> b) -> Term g a -> Term g b
  Pair : {a, b : Ty} -> Term g a -> Term g b -> Term g (Prod a b)
  Fst  : {a, b : Ty} -> Term g (Prod a b) -> Term g a
  Snd  : {a, b : Ty} -> Term g (Prod a b) -> Term g b
  InL'' : {a, b : Ty} -> Term g a -> Term g (Sum a b)
  InR'' : {a, b : Ty} -> Term g b -> Term g (Sum a b)
  Case : {a, b, c : Ty} -> Term g (Sum a b) -> Term (a::g) c -> Term (b::g) c -> Term g c
  -- Standard rules for products in a cartesian category
  -- another interesting rule, we take a Sum of a b, and two terms - each with a hole corresponding to one part of the sum - and get a result of plugging them in 
  TT   : Term g U
  Let : {s : Ty} -> Term ctx s -> Term (s :: ctx) t -> Term ctx t
  -- A lot of introductory tutorials eschew Let because it seems to be just syntactic sugar for application, but this is only true for (CBV - double check). 
  -- For reasons that we will cover later, this is the most important rule, as it distills composing two terms together          

{-- Just as before, let's evaluate our term language into Idris
The cruicial difference from before is that whereas combinators have one input and output, now we have a list of inputs, represented by our context
This corresponds to evaluating our term into a function from an environment of inputs. 
--}
namespace ToType 
  eval : {g : List Ty} -> Term g t -> (Env g -> (evalTy t))
  eval (Var v) env = lookup v env
  eval (Lam t) env = \x => (eval t) (x ::: env)
  eval (App t1 t2) env = (eval t1 env) (eval t2 env)
  eval (Pair t1 t2) env = (eval t1 env, eval t2 env)
  eval (Fst t) env = fst (eval t env)
  eval (Snd t) env = snd (eval t env)
  eval (Let t c) env = eval c (extend env (eval t env))
  eval (InL'' t) env = Left (eval t env) 
  eval (InR'' t) env = Right (eval t env) 
  eval (Case t1 t2 t3) env = case (eval t1 env) of 
    Left l => eval t2 (extend env l)  
    Right r => eval t3 (extend env r)
  eval TT env = ()


{-- Notice the similarity between evalBCC and evalSTLC - the former generates a morphism, and the latter generates a morphism from an environment.

Now we come to the final part, translating from the lambda calculus into our typed language of combinators
what we'd like is something like eval : Term g t -> c (Env g) (evalTy t)
we're looking for a 

--}

--data TypedBCC' : Cat Ty where
--  Fst' : TypedBCC' (Prod a b) a

-- Convert a list of inputs into a product of inputs
ctxToProd : List Ty -> Ty 
ctxToProd Nil = U
ctxToProd (t::ts) = Prod t (ctxToProd ts) 

help : TypedBCC k (Prod a b) c -> TypedBCC k a c 
help = ?helps 

help' : TypedBCC k a c -> TypedBCC k (Prod a U) c 
help' = ?helps'

-- TODO: go through the typed holes step-by-step
sem : {ctx: List Ty} -> Term ctx ty -> TypedBCC Prims (ctxToProd ctx) ty
sem (Pair t1 t2) = ProdI' (sem t1) (sem t2) 
-- here we have a small mismatch between Proj and Fst, one acts on morphisms and one acts on objects.
-- we can fix this by composing a projection with the output of the evaluation
sem (Fst t) = Comp1' Proj1' (sem t)
sem (Lam {a} t) = Curry' (sem t)  --TODO: fix Curry' and use snoc-lists instead?
sem (App t1 t2) = Comp1' Apply' (ProdI' (sem t1) (sem t2)) 
sem (Let t c) =  ?evs -- encode as Lambda
sem (Case t1 t2 t3) = Comp1' (CoprodI' (help (sem t2)) (help (sem t3))) (sem t1) 
sem (Prim'' t) = help' (Prim' t) 
sem (Var e) = case e of 
  Here => ?hs 
  There t => ?ts 
sem _ = ?sems 

{-}  
When I started this post I wasn't expecting the translation to combinators to be this easy. But when you line up the types, things just work. 
However, even though things work, how much insight did we really gain. 
Historically, the algorithms like bracket abstraction were motivated by the fact that we wanted an algebraic understanding of our formal languages, and languages without variable binders were a lot easier to understand. 
But the structure of variable contexts is one of the most interesting parts of the language. Various calculi based on substructural, bunched, cyclic logics are based on their own notion of variable context.
Rather than getting rid of contexts, we would prefer to have a first-class way of working with them, and giving them semantics.
This is the focus of this blog series. 
In a slogan, the structure of your variable context determines the structure of your language. 
Our main tool in this will be (generalised) multicategories. 
And if that sounds hard, then don't worry, we will start from much simpler foundations.
In the next post we will introduce the sledge-hammer 


    idArr : {o : g.obj} -> g.hom o o
    compArr : {a, b, c : g.obj} -> g.hom a b -> g.hom b c -> g.hom a c 
    apArr : {ctx, a, b : g.obj} -> g.hom ctx (g.expObj a b) -> g.hom ctx a -> g.hom ctx b
    mkPair : {ctx, a, b : g.obj} -> g.hom ctx a -> g.hom ctx b -> g.hom ctx (g.pairObj a b)
    proj1 : {ctx, a, b : g.obj} -> g.hom ctx (g.pairObj a b) -> g.hom ctx a
    proj2 : {ctx, a, b : g.obj} -> g.hom ctx (g.pairObj a b) -> g.hom ctx b


-- p7, uses distributive law of Maybe and LC: https://www.slideshare.net/ekmett/revisiting-combinators-edward-kmett