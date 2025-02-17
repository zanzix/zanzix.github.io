---
title: "From Lambda Calculus to Bicartesian Closed Categories"
author: Zanzi Mihejevs
date: Sep 23, 2023
tags: []
description: Converting the simply typed lambda calculus into typed combinators
image: bibby-alone.png
---

## Introduction

In the [previous post](/posts/bcc) we've defined a typed combinator language for bicartesian closed categories. In this post, we will define the Simply Typed Lambda Calculus and translate it into our combinator language.

The reason why we'd want to do this is that while combinators allow us to work with the primitives of some categorical structure, they make for a very austere programming language - one with no variables or binding. So while it's possible to program entirely in combinators, we would be limiting ourselves to writing point-free programs. Instead, we will write our programs in the STLC and compile the code into combinators.

But while the translation from lambda terms to closed cartesian categories is standard, there is a slight impedance mismatch between variable contexts and products that we will encounter again and again. So in addition to showing the translation itself, the goal of this blog post is to start introducing the idea of categories with a first-class notion of context, aka multicategories.

## Types
Just as before, we start by defining a type for our STLC types, as well as infix type synonyms for each type constructor.

```idr
data Ty : Type where
  Unit : Ty
  Prod : Ty -> Ty -> Ty
  Sum : Ty -> Ty -> Ty
  Exp : Ty -> Ty -> Ty
  N : Ty

infixr 5 ~>
(~>) : Ty -> Ty -> Ty
(~>) = Exp

infixr 5 :*:
(:*:) : Ty -> Ty -> Ty
(:*:) = Prod

infixr 5 :+:
(:+:) : Ty -> Ty -> Ty
(:+:) = Sum
```

As we can see, the types stay the same as before. In fact, looking at the STLC and our [combinator language](/posts/bcc) side by side reveals that a lot of structure is carried over with little modification.

Let's start by looking at the core language, and then add the rest of the constructors.

## Core language
```idr
-- Terms of the Simply Typed Lambda Calculus
data Term : List Ty -> Ty -> Type where
  -- Variables
  Var : {g : List Ty} -> {a : Ty} -> Elem a g -> Term g a
  -- Primitives
  Prim : {g : List Ty} -> {a : Ty} -> Prims g a -> Term g a
  -- Lambda abstraction
  Lam : {g : List Ty} -> {a, b : Ty} -> Term (a::g) b -> Term g (a ~> b)
  -- Lambda application
  App : {g : List Ty} -> {a, b : Ty} -> Term g (a ~> b) -> Term g a -> Term g b
```

The first thing we notice is that our type signature has changed. While combinators take a single input to a single output ```Ty -> Ty -> Type```, we are now working with a list of inputs - aka our variable context - which is then taken to an output ```List Ty -> Ty -> Type```. Since we will use the latter type a lot, we'll define a type synonym for it, and call it a multigraph.

```idr
Graph : Type -> Type
Graph obj = obj -> obj -> Type

Multigraph : Type -> Type
Multigraph obj = List obj -> obj -> Type
```
Since we now have a list of inputs as opposed to a single input, we need some way of embedding variables into our variable context. This is done using the ```Var``` constructor. It kind of looks like the identity arrow from the combinator language if you squint, and indeed the correspondence would become a lot more precise if we were working with a linear lambda calculus:

```idr
Id   : {a : Ty}                              -> Comb _ a  a
LVar : {a : Ty}                              -> Term  [a] a
Var  : {a : Ty} -> {g : List Ty} -> Elem a g -> Term   g  a
```

So ```Id``` takes a single input to a single output, ```Var``` embeds a variable into a larger context, while ```LVar``` embeds the variable into a singleton context. From this we can see the difference between linear and cartesian variables - cartesian variables can be projected out of a larger context, ignoring the rest, while linear variables must be used without anything else remaining.

Here [Elem](https://www.idris-lang.org/docs/idris2/current/base_docs/docs/Data.List.Elem.html) is taken from the Idris standard library, it's kind of proof-relevant membership relation, which guarantees that the variable ```a``` will be inside of the larger context ```g```.

```idr
data Elem : a -> List a -> Type where
  ||| A proof that the element is at the head of the list
  Here : Elem x (x :: xs)
  ||| A proof that the element is in the tail of the list
  There : Elem x xs -> Elem x (y :: xs)

-- Find the variable corresponding to Elem t g, from an environment Env g
lookup : Elem t g -> Env g -> evalTy t
lookup Here (x ::- xs) = x
lookup (There t) (y ::- xs) = lookup t xs

```
We can also see that lambda abstraction looks kind of like currying, but flipped. If we were to work with Snoc-lists instead of Cons-lists then we would see the correspondence between the two constructors a lot clearer:

```idr
-- Snoc List
data SList a = Lin | Snoc (SList a) a

infixr 5 -:
(-:) : SList a -> a -> SList a
(-:) = Snoc

Lam   : {g : SList Ty} -> Term   (g  -: a) b -> Term   g (a ~> b)
Curry : {c :       Ty} -> Comb _ (c :*: a) b -> Comb _ c (a ~> b)
```

We can see that the two line-up very closely, except that Curry takes as an input a morphism from a tuple ```(c :*: a)```, while Lam takes as an input a term with the context ```g -: a```. Lambda abstraction then takes the free variable ```a```, and binds it inside the function ```(a ~> b)```. So in a way, a context is just a convenient representation for an n-ary tuple.

Unfortunately, while the Snoc-list representation makes working with lambda abstraction much easier, it will complicate working with the rest of our binding operators, so we will not be using it in the full language.

We've also split Apply into multiple terms. Whereas previously the entire operation was expressed as a single combinator, we are now defining it as a meta-operation on terms, each with their own context:

```idr
App   : Term   g  (a ~> b) -> Term g a -> Term g b
Apply : Comb _   ((a ~> b) :*:       a)          b
```

This will be a recurring pattern in the translation, and many other combinators will be split this way.

## Primitives
We can also see that just as we've changed the type of our term language to be a multigraph, we've done the same to our primitives ```Prims : List Ty -> Ty -> Type```. Similar to Lam, each primitive will take a number of variables from the context and bind them to a primitive expression.

Let's define some primitives. Just like before, we'd like to work with the generators of a monoid. There are a few choices of representation that we can take here, depending on how we want our primitives to interact with the context.

The easiest thing to do would be to say that our generators take a number of variables from some larger context, and leave the rest of the context unchanged, implicitly discarding it. The unit of the monoid takes no variables from the context ```g```, and leaves the entire thing unchanged, while the multiplication takes two variables ```N :: N :: g```, and leaves the rest.

```idr
-- Primitives with "cartesian" contexts
data CPrims : Multigraph Ty where
  CZ : CPrims g N
  CMult : CPrims (N :: N :: g) N
```

This would be convenient to program with, since we could embed our primitives inside terms with an arbitrary context.

```idr
ex : {g : List Ty} -> Term g (N ~> (N ~> N))
ex = Lam (Lam (Prim CMult))
```

Unfortunately - as we will see below - this would make the translation to combinators a lot more cumbersome. So instead, we will use primitives with a more careful context discipline, only admitting contexts with the exact number of variables that will be used.

So the monoid unit will require an empty context ```[]```, which is equivalent to a morphism from the unit object, and the monoid multiplication will use a context with exactly two free variables, which is equivalent to a morphism from a tuple. This will make the translation to the set of primitives from the last post almost trivial. Almost.

```idr
-- Primitives with "linear" contexts
data LinPrims : Multigraph Ty where
  LZ : LinPrims [] N
  LMult : LinPrims [N, N] N

-- the context needs to be empty, or the expression won't type-check
ex' : {g : List Ty} -> Term Nil (N ~> (N ~> N))
ex' = Lam (Lam (Prim LMult))

```

Alternatively, we could have defined our set of primitives within the language itself:

```idr
data STLC : List Ty -> Ty -> Type where
  -- ... stlc constructors
  E : STLC g N
  Mult : STLC g N -> STLC g N -> STLC g N
```

But this would not maintain the clean separation between the primitives and the terms built on top of them, like we did in our combinator language.

Our presentation also gives us an insight into a more subtle relationship between lambda terms and combinators - combinators are defined over an underlying graph, while terms are defined over an underlying multigraph.

## STLC with Products and Sums

Having looked at the core language, let's now turn our attention to the full language:

```idr
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
```

We can see that just as with the core language, the new connectives fall into two categories - they either interact with the context, such as Case and Let, or they do not.

## Let is all you need

```Let``` is often seen as redundant since it can be defined using ```Lam```, but doing so is only valid in a category with exponentials. While this is obviously true in our full language, our goal is to mix-and-match the syntax as needed. So keeping the Let operator will allow us to retain the ability to bind variables even if we move to a subset of the language without lambda abstraction.

In fact, if we look closely at the Let connective, we'll notice that it's possible to work in a language with *nothing but* variables and Let.

```idr
Let         : Term    g s -> Term   (s :: g) t -> Term   g t
(flip Comp) : Comb _  c s -> Comb _  s       t -> Comb _ c t
```

So ```Let``` is nothing other than composition! Or to be more precise, it's a notion of composition for morphisms that contain variable contexts. We will call these 'multi-morphisms'. Meanwhile, the constructor for linear variables ```LVar``` that we've seen earlier is a notion of an identity arrow for multi-morphisms.

Taking this a step further, we can see a correspondence between a free category on a graph, and a free "multicategory" on a multigraph.

```idr
-- Free category over a graph 'g'.
data Cat : {obj : Type} -> Graph obj -> Graph obj where
  Id : {a : obj} -> Cat g a a
  Cons : {a, b, c : obj} -> g b c -> Cat g a b -> Cat g a c

-- Free multicategory over the multigraph 'm'.
data Multicat : {obj : Type} -> Multigraph obj -> Multigraph obj where
  LVar : {a : obj} -> Multicat m [a] a
  Let : {ctx : List obj} -> {s, t : obj} ->
    m ctx s -> Multicat m (s :: ctx) t -> Multicat m ctx t
```

(Strictly speaking, this is a cartesian multicategory, since the context 'ctx' is shared between terms).

But this is getting ahead of ourselves. We will talk about multicategories - including non-cartesian ones - in much more detail later, but for now let's get back to the lambda calculus.

## Translation into Idris

Having defined our term language, let's start by translating it into Idris' types and functions, after which we will do a more general translation into combinators.

As always, we start by translating the types. This stays exactly as in our last post:

```idr
evalTy : Ty -> Type
evalTy Unit = Unit
evalTy N = Nat
evalTy (Exp t1 t2) = (evalTy t1) -> (evalTy t2)
evalTy (Prod t1 t2) = (evalTy t1, evalTy t2)
evalTy (Sum t1 t2) = Either (evalTy t1) (evalTy t2)
```

Next we would like to translate the primitives, however here we face our first complication. Previously our evaluator converted a primitive into a function from one input to one output:
```idr
evalPrims : Prims ty1 ty2 -> Idr (evalTy ty1) (evalTy ty2)
```

Now we would like to define a function from multiple inputs to an output:
```idr
evalPrims : Prims g ty -> (Idr (?evalCtx g) (evalTy t))
```

How should we represent these multi-input functions? We can think of n-ary functions as functions out of an environment, represented as a heterogeneous list of values.

We will use the following representation of our environment. We can think of it as a list of values ```(evalTy t)``` indexed by our context ```List Ty```.

```idr
-- Cons list, extends environment from the left
infixr 5 ::-
data Env : List Ty -> Type where
  CNil  : Env Nil
  (::-) : evalTy t -> Env g -> Env (t :: g)
```

Contrast it to the definition of a list:

```idr
data List : Type -> Type
  Nil : List a
  Cons : t -> List t -> List t
```

We can think of an environment as a kind of "heterogenous list of values indexed by a list of types of those values".

We will instantiate our monoid as the monoid of natural numbers ```Nat```. Then our evaluator for primitives becomes as follows. The monoidal unit does not interact with the environment, creating a 0 out of nothing. The monoidal multiplication pops two natural numbers from the environment and adds them.

```idr
evalPrims : LPrims g t -> Idr (Env g) (evalTy t)
evalPrims E CNil = 0
evalPrims Mult (m1 ::- m2 ::- CNil) = m1 + m2
```

Combining the above, we get our evaluator that takes terms to n-ary Idris functions. If you compare it to our BCC evaluator from before, then not a lot changes - the constructors that don't interact with the context remain almost the same. The constructors that do interact with the environment - Lam, Case, Let - all involve extending the environment with a new variable, which then gets bound and used within the expression.

```idr
eval : {g : List Ty} -> Term g t -> Idr (Env g) (evalTy t)
eval (Var v) env = lookup v env
eval (LPrim e) env = evalPrims e env
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
```

Finally, we would like to translate our lambda calculus into bicartesian closed categories. Generalising from Idris functions, our goal looks something like
```idr
eval : (bcc : BCC g) -> Term g ty -> bcc (Env g) (evalTy t)
```
However, our environment Env is defined for Idris types, so we would need to generalise it. So what we'll do is interpret our context of types into a product of types, with the empty list being represented by the Unit type.

At first glance, we might want to simply fold over our context:

```idr
ctxF : List Ty -> Ty
ctxF tys = foldr Prod Unit tys
```

However, this would create awkward-looking types such as ```(Prod a (Prod b) Unit)```. So a more nicer alternative would be to convert the empty List into Unit, but not use that as a base case, and instead treat the embedding ```[a]``` of a type into a list as the base case instead. This would give us nicer-looking types without trailing units at the end.

```idr
ctxEv : List Ty -> Ty
ctxEv Nil = Unit
ctxEv [t] = t
ctxEv (t::ts) = Prod t (ctxEv ts)
```

Using this evaluator, our translation between primitives would be trivial.

```idr
-- Translating from LPrims to Typed.Prims
evalPrim : {g : List Ty} -> LPrims g t -> Prims (ctxEv g) t
evalPrim LZ = Typed.Z
evalPrim LMult = Typed.Mult
```

Unfortunately, using this much nicer evaluator would complicate type unification immensely, and make the translation much harder to write. So we will use the messier fold instead and just put up with trailing units.

This means that while the monoidal unit translates correctly to ```Prims Unit N```, the monoidal multiplication becomes ```Prims (Pair N (Pair N Unit)) N```. We could fix this by using the structural rules of the combinator language to rearrange the expression and drop the trailing Unit, but this means that we need to first embed our primitives into the combinator language, rather than translating between two sets of primitives directly.

First, let's add some new structural rules to the combinator language.

```idr
-- Syntactic sugar for composing arrows:
(>>>) : {a, b, c : Ty} -> Comb k a b -> Comb k b c -> Comb k a c
(>>>) f g = Comp g f

-- | New Combinators

-- Bifunctor for products
BifP : {a, b, c, d : Ty} ->
  Comb k a c -> Comb k b d -> Comb k (a :*: b) (c :*: d)
-- Unit elimination
UnitL : {a : Ty} -> Comb g (a :*: Unit) a
```

Now we can do the translation:

```idr
-- Won't work without embedding into Comb
evalPrim : {g : List Ty} -> LPrims g t -> Prims (ctxF g) t
evalPrim LZ = Typed.Z
evalPrim LMult = ?sadness

-- Works
evalPrimF : {ctx : List Ty} -> LPrims ctx t -> Comb Prims (ctxF ctx) t
evalPrimF LZ = Prim Typed.Z
evalPrimF LMult = BifP Id UnitL >>> Prim Typed.Mult
```

Had we chosen to work with cartesian contexts instead, we would have needed to deal with the trailing context of unused variables. The monoidal unit would be ```Prims (ctxF g) N```, with multiplication ```Prims (Pair N (Pair N (ctxF g)))```. This would mean that for each primitive we'd have to zoom into the nested tuple and drop the remaining context by composing it with the terminal morphism: ```Terminal : {a : Ty} -> Comb k a Unit```.

```idr
-- Works, but messy
evalPrim' : {ctx : List Ty} -> CPrims ctx t -> Comb Prims (ctxF ctx) t
evalPrim' CZ = Terminal >>> Prim Typed.Z
evalPrim' CMult = BifP Id Fst >>> Prim Typed.Mult
```

In addition to translating the primitives, we also want to translate variables. When working with contexts, a variable is an index into an environment, pointing at a specific value. When working with tuples, a variable is translated into a sequence of projections from a nested tuple.

```idr
var : {g : Graph Ty} -> {ctx : List Ty} -> {ty : Ty} ->
  Elem ty ctx -> Comb g (ctxF ctx) ty
var Here = Fst
var (There t) = Comp (var t) Snd
```

We're either taking the left-most component with Fst, or traversing the nested tuple with a sequence of Snd's.

Finally, we get our evaluator from terms to combinators. Just like earlier, the only constructors that require special care are the ones that interact with the context. Usually these involve some manner of re-arrangement of nested tuples using the structural rules of bicartesian closed categories. For instance, had we used Snoc-lists, the evaluator for ```Lam``` would be trivial, but instead we will re-arrange the context a bit to make it work.

First, we'll go back to our combinator language and add a few more structural combinators to make it work.

```idr
-- | New Combinators

-- Distributivity of sums over products
Distrib : {a, b, c : Ty} -> Comb k ((a :+: b) :*: c) ((a :*: c) :+: (b :*: c))
-- Bifunctor for sums
BifC : {a, b, c, d : Ty} ->
  Comb k a c -> Comb k b d -> Comb k (a :+: b) (c :+: d)
-- Symmetry for products
SwapP : {a, b : Ty} -> Comb k (a :*: b) (b :*: a)
-- Symmetry for sums
SwapC : {a, b : Ty} -> Comb k (a :+: b) (b :+: a)
-- Unit elimination
UnitL : {a : Ty} -> Comb g (a :*: Unit) a
-- Copy: (a → a * a)
Copy : {a : Ty} -> Comb g a (a :*: a)
-- Cocopy: (a + a → a)
Cocopy : {a : Ty} -> Comb b (a :+: a) a
```

Now we can do the translation itself. The most involved case is that of case matching, which I had [Jules](https://julesh.com/) help me with. We have a morphism from the context into a sum, as well as two morphisms out of a product of a variable and the context. We need to combine them to get a morphism out of the context.

```
m1 : g -> a + b
m2 : (a * g) -> ty
m3 : (b * g) -> ty
----------------------
g -> ty
```

As an Idris expression, it would look like this:

```idr
match : (g -> Either a b) -> ((a, g) -> t) -> ((b, g) -> t) -> g -> t
match m1 m2 m3 g = case m1 g of
  Left a => m2 (a, g)
  Right b => m3 (b, g)
```

Translating this into combinators, we will need the following sequence of transformations:
```idr
-- g -> (g * g) -> ((a + b) * g) ~= ((a * g) + (b * g)) -> ty + ty -> ty

sem (Case t1 t2 t3) = Copy >>> BifP (sem t1) Id >>>
  Distrib >>> BifC (sem t2) (sem t3) >>> Cocopy
```

Putting it all together, our compiler to combinators becomes the following:

```idr
-- Translation into combinators
sem : {ctx : List Ty} -> {ty : Ty} -> Term ctx ty -> Comb Prims (ctxF ctx) ty
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
```

Composing this with the semantic interpreter from combinators to BCCs, we get:

```idr
interp : {ctx : List Ty} -> {ty : Ty} ->
  (b : BCC g) -> Term ctx ty -> g (b.ty (ctxToProd ctx)) (b.ty ty)
interp b t = eval' b (sem t)
```

## Conclusion

We have formulated a translation from the STLC into an arbitrary BCC. This was *mostly* painless, except for when it came to translating constructors that involve context manipulation. Even writing this blog post has fallen to the ~~80:20~~ ~~90:10~~ 95:5 rule, with the majority of the code being straightforward except for the parts involving shuffling variables and binders.

It's worth reflecting on *why* this is so difficult. Categories don't have a first-class notion of variable context or binding operations, so when we're translating from a calculus that does, we need some way of turning binders and variables into morphisms. Doing so, however, makes our semantics more awkward and verbose, and can lead to an explosion of code size.

But what if there was another way? What if instead of translating into categorical combinators, we had a way of giving a semantics for the lambda calculus directly in terms of multicategories? Rather than dealing with the impedance mismatch between contexts and products, our semantics would be a homomorphism on the context, preserving its structure.

This is what we will look at in the next few blog posts, and what will become one of the main themes of the series. And if the idea of working with multicategories sounds daunting, then don't worry, the next blog post will start at the very beginning - with fixpoints of functors and free monads.