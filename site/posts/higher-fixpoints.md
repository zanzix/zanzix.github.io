---
title: "Fixpoints all the way up"
author: Zanzi
date: Aug 10, 2023
tags: [functor, fixpoint, operad]
description: Lets start the blog
image: code.jpg
---
# Higher order fixpoint
Last blog post we looked at fixpoints over endofunctors, free monads, and free operads.

It might seem like a lot of concepts.

But the secret is that they're all instances of the same thing...

Let's start with the free monad

```idris 
data Free : (Type -> Type) -> Type -> Type where

	Var : v -> Free f v

	In : f (Free f v) -> Free f v
```


We can notice a similarity with the type of Lists, and ineed a free monad is just a list 'one level up'.

So what happens if, just as we did in the first blog post, we extract the recursive component of Free?

```idris 
data FreeF : (Type -> Type) -> (Type -> Type) -> Type -> Type where

	Var : v -> Free f g v

	In : f (g v) -> Free f g v
```


Rewriting the types a litte, we can see the clear link with ListF


FreeF : Functor Type -> Functor Type -> Functor Type
ListF :                Type ->               Type ->               Type  

In fact, if we change the arrows a little

```idris
(:~>) : (Type -> Type) -> (Type -> Type) -> Type

(:~>) f g = {a : Type} -> f a -> g a

```

We will see that 

``` idris
Var : I :~> Free f g 
In : f g ~> Free f g
```

Looks a lot like
```idris
Nil : () -> ListF a b
Cons : (a, b) -> ListF a b
```

With the main difference is that ListF is a monoid with respect to the cartesian product, while FreeF is a monoid with respect to functor composition 
(It is in fact a *category* with respect to functor composition, but we will get to that later...)

Since Free is a functor, specifically in the category of endofunctors, it will have a corresponding notion of fixpoint

``` idr
data Mu2 : (pattern: (Type -> Type) -> (Type -> Type)) -> Type -> Type where

	In2 : {a : Type} -> f (Mu f) a -> Mu f a
```

We can see that it's just Mu one level up

```idr
Mu2 : (Functor Type -> Functor Type) -> Functor Type
Mu :  (        Type ->         Type) ->         Type
```

As a fixpoint of endofunctor, Mu2 will also have its own notion of algebra
``` idr
Algebra : (f : (Type -> Type) -> Type -> Type) -> (a : Type -> Type) -> Type
Algebra f a = f a :~> a

```

or more simply

```idr
Algebra : (Functor Type -> Functor Type) -> Functor Type -> Type
```

And a notion of fold

```
cata : Functor2 hf => (hf f :~> f) -> Mu hf :~> f

cata alg (In op) = alg (maph (cata alg) op)

```

Now, the evaluator for Mu2 gives us a *functor*, not a *value*

So if we want to recover our previous evaluator, we need to post-compose it with a first-order evaluator

``` idr
Algebra2 (FreeF) (Fix List)

eval = fold alg (fold alg2 expr) 
```

The advantage of this approach is that we separate our evaluation. The monadic stage covers variable binding and substitution, and the functor stage covers evaluating the expression itself

We can also evaluate our expression into a value directly, using the konstant functor

```idr
Algebra2 (FreeF) (Konst Nat)
```

# Indexed fixpoint
Our operad is also an example of a higher-order fixpoint

This time, instead of functors over the category of functors, we take functors over the category of indexed functors

as before, we extract our recursive component

```
data Operad : (Type -> Type) -> (Nat -> Type -> Type) -> (Nat -> Type -> Type) where 

	Var : Fin n -> Operad f g n a

	LetF : f (g (S n) a) -> Operad f g n a

-- (Type -> Type) -> (Type -> Type) -> Type -> Type 
```



```idr
data Mu : ((k -> Type) -> (i -> k -> Type)) -> i -> k -> Type where
	In : f (Mu f) n a -> Mu f n a
```
TODO: Does this actually work?

and we evaluate it

```idr
cata 
```

The nice thing about this type is that it works over our regular data-types (Type -> Type),

but if we want a more regualr fixpoint, we could also do

```idr
data Mu : ((k -> Type) -> (k -> Type)) -> k -> Type where
	In : f (Mu f) a -> Mu f a
```

and we can recover our Operad by setting k = (Nat, Type)

TODO: pattern for free relative monad?

So the purpose of this blog post was to introduce higher-order fixpoint, and show how they subsume both free monads and free operads.

And since, as we learned from the previous blog post, we can upgrade Mu to Free, the same is true of Mu2 and IxMu

For Mu2, we get Free2
``` idr
-- data Free :  (Functor Type -> Functor Type) -> Functor Type -> Functor Type

-- this might be wrong
data Free : (pattern: (Type -> Type) -> (Type -> Type)) -> (var: Type -> Type) -> (value: Type) -> Type where


Var : {a : Type} -> v a -> Free f v a

In2 : {a : Type} -> f (Free f v) a -> Free f v a
```

Whereas a first-order free monad has variables that range over values, a second-order free monad has variables that range over functors.

And for MuIx, we get FreeIx

```idr
data FreeI : (pattern: (k -> Type) -> (k -> Type)) -> (con: k -> Type) -> (value: k) -> Type where

Var : {a : k} -> con a -> FreeI f con a

In2 : {a : k} -> f (FreeI f con) a -> FreeI f con a
```