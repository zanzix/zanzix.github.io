---
title: "Lambda Calculus and Bicartesian Closed Categories, Part 2"
author: Zanzi
date: Sep 1, 2023
tags: []
description: Converting the simply typed lambda calculus into typed combinators
---

In the previous post we've defined a typed combinator language for bicartesian closed categories. In this post, we will define the Simply Typed Lambda Calculus and translate it into our combinator language.

The reason why we want to do this is two-fold: 

From a practical perspective, while combinators let us work with the primitives of some categorical structure, they make for a very austere DSL - one with no variables or binding. So it's much more convenient to work in a language with variables and binding - the 'internal language of the category - and then translate it into combinators. 

From a theory perspective, this gives us a way to provide a semantics for our language. 

Just as before, we start by defining a type for our types, as well as infix type synonyms.

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

It's instructive to notice what stays the same and what changes as we move from combinators to a type theory. The types stay the same as before. 

We'll start by looking at the core language, then add the rest of the connectives. 

```idr 
data Term : List Ty -> Ty -> Type where
  -- Variables 
  Var : {g : List Ty} -> {a : Ty} -> Elem a g -> Term g a
  -- Primitives
  Prim' : {g : List Ty} -> {a : Ty} -> Prims g a -> Term g a 
  -- Lambda abstraction
  Lam : {g : List Ty} -> {a, b : Ty} -> Term (a :: g) b -> Term g (a ~> b)
  -- Lambda application
  App : {g : List Ty} -> {a, b : Ty} -> Term g (a ~> b) -> Term g a -> Term g b
```
-- TODO: Variables

The first thing that we can see is that our type signature has changed. While combinators take a single input to a single output ```Ty -> Ty -> Type```, we're now working with a list of inputs (our variable context) which are taken to an output ```List' Ty -> Ty -> Type```. We will call this a multigraph. 

```idr
Multigraph : Type -> Type 
Multigraph a = List a -> a -> Type 
```

We can also notice that lambda abstraction looks kind of like currying ```TypedBCC k (a :*: b) c -> TypedBCC k a (b ~> c)```, except flipped. If we were to work with Snoc-lists instead of Cons-lists then we would see the correspondence a lot clearer:

```idr
data List' a = Lin | Snoc (List' a) a

infixr 5 -:
(-:) : List' a -> a -> List' a 
(-:) = Snoc

Lam : Term (g -: a) b -> Term g (a ~> b)
``` 

We can now see that the two line-up very closely, except that now instead of taking a value from a tuple and turning it into a function, we now take a variable from the context, and create a function which binds that variable. 

We can also see that just as we've changed the type of our term language to be a multigraph, we've done the same to our primitives ```Prims : List Ty -> Ty -> Type```. Similar to lambda abstraction, they will now take a number of variables from the context and bind them to a primitive expression. 

Same as before, let's try to define our primitives for a monoid. But first, let's look at how not to do it.
```idr
data LinPrims : Multigraph Ty where
  -- the unit for the monoid takes an empty list of inputs - this is equivalent to a morphism from the unit type as before
  E' : LinPrims [] N 
  -- the monoid multiplication now takes two elements from the context - this is equivalent to a morphism from a product of elements
  Mult' : LinPrims [N, N] N
```

This definition looks correct at first glance, but it is too strict - it misses out the fact that we might have unused variables in the context, and will fail if we do. So it will work in a *linear* setting where each variable must be used once, but not in our *cartesian* setting where the context is shared across terms. So the right notion of primitives will look like this:

```idr
data Prims' : Multigraph Ty where
  -- the unit for the monoid doesn't take anything from the context, and leaves it unchanged
  E : Prims' g N  
  -- the monoid multiplication now takes two elements from the context, and leaves the rest
  Mult : Prims' (N :: N :: g) N
```
-- TODO: encode a few examples

We're now splitting the context into two parts - the part we're using, and the rest of it. 

The last thing that's changed is that we've split Application into multiple terms. Whereas previously the entire operation was expressed as a single combinator ```Apply : TypedBCC k ((a ~> b) :*: a) b```, we are now defining it as a meta-operation on terms: ```Term g (a ~> b) -> Term g a -> Term g b```

Having looked at the core language, let's now turn our attention to the full language:

```idr
data Term : Multigraph Ty where
  Prim' : {g : List Ty} -> {a : Ty} -> Prims' g a -> Term g a 
  -- Variables 
  Var : {a : Ty} -> {g : List Ty} -> Elem a g -> Term g a
  -- Lambda abstraction
  Lam : {a, b : Ty} -> Term (a::g) b -> Term g (a ~> b)
  -- Lambda application
  App : {a, b : Ty} -> Term g (a ~> b) -> Term g a -> Term g b
  -- First projection
  Fst : {a, b : Ty} -> Term g (Prod a b) -> Term g a
  -- Second projection
  Snd : {a, b : Ty} -> Term g (Prod a b) -> Term g b
  -- Product introduction
  Pair : {a, b : Ty} -> Term g a -> Term g b -> Term g (Prod a b)
  -- Left injection
  InL : {a, b : Ty} -> Term g a -> Term g (Sum a b)
  -- Right injection
  InR : {a, b : Ty} -> Term g b -> Term g (Sum a b)
  -- Coproduct elimination, aka case matching 
  Case : {a, b, c : Ty} -> Term g (Sum a b) -> Term (a::g) c -> Term (b::g) c -> Term g c
  -- Let binding
  Let : {s : Ty} -> Term ctx s -> Term (s :: ctx) t -> Term ctx t
```

We can see that just as with the core language, the new connectives fall into two categories - they either interact with the context, such as Case and Lam, or they do not. We've also included a Let connective, which is often elided in introductions to the lambda calculus since it can be defined as syntactic sugar. However, this definition assumes that our category is closed, and while this is true in our full language, our goal is to use our syntax modularly if needed.

So let's look at why the let connective has special importance, by putting it side by side with it's equivalent from the combinator language. 

```idr
  Let         : Term        ctx s -> Term       (s :: ctx) t -> Term       ctx t
  (flip Comp) : TypedBCC _  a   b -> TypedBCC _  b         c -> TypedBCC _ a   c
```

As we can see, while Comp composes two morphisms built-up from a graph, Let composes two (multi)-morphisms built-up from a multigraph. So just as Comp corresponds to composition in a category, Let corresponds to composition in a multicategory. But more on that later. 

Having defined our term language, we will first translate it into Idris, and then translate it into our combinators. 

We start by defining a translation from the STLC types to Idris types. This stays exactly as before.

```idr
evalTy : Ty -> Type
evalTy Unit = Unit
evalTy N = Nat
evalTy (Exp t1 t2) = (evalTy t1) -> (evalTy t2)
evalTy (Prod t1 t2) = (evalTy t1, evalTy t2)
evalTy (Sum t1 t2) = Either (evalTy t1) (evalTy t2) 
```

Next we would like to translate the primitives, however we have a small complication. Whereas previously we defined our evaluator as translating a primitive into a function from one input to one output ```evalPrims : Prims ty1 ty2 -> Idr (evalTy ty1) (evalTy ty2)```, we would now like to define a function from multiple inputs to an output ```evalPrims' : Prims' g ty -> (Idr (?evalCtx g) (evalTy t))```. And while we could define a type of Idris multi-functions, it's much more convenient to represent a multi-function as a function from an environment of values.

We will use the following representation of our environment. We can think of it as a list of values ```(evalTy t)``` indexed by our context ```List Ty```. 

```
-- Cons list, extends environment from the left
infixr 5 ::-
data Env : List Ty -> Type where
  CNil  : Env Nil
  (::-) : evalTy t -> Env g -> Env (t :: g)


-- Snoc, extends environment from the right
infixr 5 -::
(-::) : {t : Ty} -> (env : Env ctxt) -> (obj : evalTy t) -> Env (t::ctxt)
(-::) env obj = obj ::- env
```

Then our evaluator for primitives becomes:

```idr
evalPrims : Prims' g t -> (Env g -> evalTy t)
evalPrims E env = 0 -- no interaction with environment context
evalPrims Mult (m1 ::- m2 ::- env) = m1 + m2 -- pop the first two values from the environment and add them 
```

Finally, we get our evaluator from terms to n-ary Idris functions. If you compare it to our BCC evaluator from before, then not a lot changes - the evaluators for primitives that don't interact with the context are almost the same. The primitives that do interact with the environment - Lam, Case, Let - all involve extending the environment with a new variable, which then gets bound and used within the expression. 

```idr
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
```

Finally, we would like to translate our lambda calculus into bicartesian closed categories. Generalising from Idris functions, our goal looks something like ```eval : (bcc : BCC g) -> Term g ty -> bcc (Env g) (evalTy t)```. However, our environment Env is defined for Idris types, so we would need to generalise away from it somehow. So what we'll do is interpret our context of types as a product, with the empty list being represented by the Unit type.

It would be tempting to simply fold over our context:

```idr
ctxToProd' : List Ty -> Ty 
ctxToProd' tys = foldr Prod Unit tys 
```

But this would create awkward-looking types such as ```(Prod a (Prod b) Unit)```. So what we'll do is convert the empty List into Unit, but not use that as a base case, and treat the embedding [a] of a type into a list as the base case instead. This will give us nicer-looking types without trailing units at the end.

```idr 
ctxToProd : List Ty -> Ty 
ctxToProd Nil = Unit
ctxToProd [t] = t
ctxToProd (t::ts) = Prod t (ctxToProd ts) 
```

Now we can define our translation into combinators. First let's take care of the primitives. 

```idr

```

In the previous post we parametrised our TypedBCC language with its type of primitives: ```TypedBCC : Graph Ty -> Graph Ty```, from which we can see that our combinator language was a free f-algebra over some underlying graph. In this post we've hardcoded the type of primitives into our language, however let's see what happens if we parametrise over it: ```Term : Multigraph Ty -> Multigraph Ty```. We can see that our lambda calculus is now a free f-algebra over a multigraph! 

From this we could ask: what if instead of translating our language into combinators, we could work with multicategories directly? This would have the advantage of keeping variable and context data first-class, rather than translating them into a semantics where they are encoded indirectly. 

If this sounds daunting, don't worry, we will start from the basics. In the next post we will introduce a simplified form of multicategory called an operad, and relate it to the more familiar notions of fixpoints and free monads over an endofunctor. 
