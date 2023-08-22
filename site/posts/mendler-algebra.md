---
title: "From Mendler Algebra to Relative Monads"
author: Zanzi
date: Aug 10, 2023
tags: [functor, fixpoint, operad]
description: Lets start the blog
image: code.jpg
---

So far we've relied on all of our underlying data-types to have a valid instance.

But as we intend to generalise a *lot*, this kind of constraint will lead to far too much boilerplate.

Luckily, we can generalise this away.

TODO: Try my trick of doing cata with no functor constraint?

Interestingly, we can do it in two different ways.
We can either modify our notion of algebra, as is common in the recursion-schemes literature

```idr
MAlgebra : (Type -> Type) -> Type -> Type
MAlgebra f c = {x : Type} -> (x -> c) -> f x -> c
```

Letting us keep the same type of fixpoint Mu, 

```idr
fold : MAlgebra 
```

Or we can modify our notion of the data-type, as is more common in the free-monad literature

```idr 
data Freer : (Type -> Type) -> Type -> Type where
	Var : v -> Freerf f v
	Bind : f x -> (x -> Freer f v) -> Freer f v
```

It turns out that both of these techniques are related.

we can look at Coyoneda, 

```idr
data Coyoneda : (Type -> Type) -> Type -> Type where
  InCoyo : (a -> b) -> f a -> Coyoneda f b
```

we can notice that 
MAlgebra f a = Algebra (Coyoneda f) a

and we can also see that

Freer f a = Freer (Cyoneda f) a

from this, we can even derive a notion of 'freer fixpoint'

```idr
data Mu : (pattern : Type -> Type) -> Type where
    In : {f: Type -> Type} -> Coyoneda f (Mu f) -> Mu 
```

So this gives us a version of Fix and Free that does not rely on an underlying functor instance

But what about Op?

As I mentioned in the last post, Op is not a free monad, but a free *relative* monad. 

The trick to deriving this is to notice that Coyoneda is a special case of a left kan extension, Coyoneda = Lan Id, and that a standard monad is a monad w.r.t to the Identity functor. As it turns out, these two facts are related.

```idr
data Lan : 
	InLan
```

so given a context functor j : (k->Type), the free relative monad over j is given by

```idr
data Relative : {j : k -> Type} -> (k -> Type) -> (k -> Type) -> (k -> Type) where

PureR : {j : k -> Type} -> j x -> Relative j f x

ThenR : {j : k -> Type} -> f x -> (j x -> Relative j f a) -> Relative j f a
Bind : Lan j f (Mu j f v) -> Mu j f v
```

our evaluator now uses a new algebra and a new data-type

```
cata : {j : k -> Type} -> (j n -> c) -> Algebra (Lan j f) c -> Mu j f n -> c
cata g alg = go where

go : Mu j f n -> c

go (Var a) = g a

go (Bind $ MkLan continue action) = alg (MkLan (go . continue) action)
```

TODO: Will this work with last post's notion of operad (Type -> Type) -> (Nat -> Type -> Type) ?

LetF : f (Operad f (S n) a) -> Operad f n a
LetF : Coyoneda f (Operad f (S n) a) -> Operad f n a 

LetBind : f a -> Operad f (S n) a -> Operad f n a

