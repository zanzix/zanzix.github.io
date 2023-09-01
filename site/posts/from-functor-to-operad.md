---
title: "From Fixpoint of Functor to Operad"
author: Zanzi
date: Aug 10, 2023
tags: [functor, fixpoint, operad]
description: Lets start the blog
image: code.jpg
---

* start with a definition of a recursive type, ie List, and then extract the base functor

First, lets introduce the fixpoint of an endofunctor

``` idris
data Mu : (pattern : Type -> Type) -> Type where
	In : {f: Type -> Type} -> f (Mu f) -> Mu f
```


We can build expressions with it

``` idris
example expressions

```

to evaluate them, we define a notion of algebra

```idris 
Algebra : (Type -> Type) -> Type -> Type

Algebra f a = f a -> a
```

and we define a catamorphism, or a fold, which uniformly evaluates any 'f' that's a functor

``` idris
cata : Functor f => Algebra f a -> Mu f -> a
cata alg (In op) = alg (map (cata alg) op)
```

TODO: Try doing this with mendler-style eval which doesn't rely on Functor

Now, this gives us a notion of closed expression. We can represent algebraic signatures, say, Monoids, Semirings, and we can evaluate them. 

But it doesn't quite feel like universal algebra, since we don't have variables. To get variables, we move up a level of abstraction. Instead of using fixpoints over endofunctors, we work with free monads.


``` idris
data Free : (pattern: (Type -> Type)) -> (var: Type) -> Type where
	Var : var -> Free pat var
	In : pat (Free pat var) -> Free pat var
```

The only thing that's changed is that we've added the extra constructor Var, and the extra type-variable into the type of Free

Indeed, 
Mu f = Free f Void
and 
Free f a = Mu (f + Const)

But the perspective is valuable, because previously, we took a functor to a value

Functor : Type -> Type 
Functor a = a -> a

Mu : (Functor Type) -> Type 

Whereas Free takes a functor to a functor

Free : (Functor Type) -> (Functor Type)

What this means in practice is that we can now construct terms with variables

```idris
example terms

```

and our evaluator takes an extra parameter, to know how to handle variables

```idris
mcata : (a -> c) -> Algebra f c -> Free f a -> c
mcata g alg = go where

go : Free f a -> c
go (Var a) = g a
go (In $ fs) = alg $ (mcata g alg) fs
```

This is nice, but unfortunately our function mcata is now partial, since our terms are not well scoped

To fix this, we can change our domain from c to 'Maybe c', or maybe some other exception-uandling monad m

```idris
partialEval : (a -> c) -> Algebra f c -> Free f a -> m c

partialEval g alg = go where

go : Free f a -> c

go (Var a) = pure $ g a

go (In $ fs) = alg $ (mcata g alg) fs
```

And indeed, this is a common way of doings things in Haskell. But it doesn't solve the problem, it just pushes it into the codomain. 

Since we're using dependent types, we can go a step further, and define well-scoped terms by construction. 

```idris
data Operad : (Type -> Type) -> (Nat -> Type -> Type) where 
Var : Fin n -> Operad f n a
LetF : f (Operad f (S n) a) -> Operad f n a
LetBind : f a -> Operad f (S n) a -> Operad f n a)
```
TODO: might need to change it to Nat -> Type -> Type to be more regular?
	it'd make it consistent with typed languages: List Ty -> Ty -> Type
	
This time, our Var constructor is bound by Fin. Instead of working with an infinite set of variable, we work with a finite set of variables at a time.

And whereas previously Bind would append a functorial layer into a monad, now it binds it to a variable S. 
* mention that operad is no longer a functor between functors, but between a functor and an indexed functor

Let's look at some example expressions

```idris 
examples
```

Now our evaluator looks like this

``` idris
mcata : (Fin n -> c) -> Algebra f c -> Operad f n -> c
mcata g alg = go where
go : Free f a -> c
go (Var a) = g a
go (In $ fs) = alg $ (mcata g alg) fs
```

The cool thing about this is that our evaluator hardly changed.

While Operad is no longer a monad, it's a free *relative* monad. Aka, a monad relative to Fin. 

But we can form relative monads over other types as well. What they give us, is a very general notion of binding with respect to some context.

We will come back to relative monads soon, but for now let's look at the common abstraction that underlies all of these constructions.

But before we can do that, we need to generalise slightly.