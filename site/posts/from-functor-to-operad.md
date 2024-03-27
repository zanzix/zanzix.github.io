---
title: "From Fixpoints of Functors to Relative Monads"
author: Zanzi
date: Aug 10, 2023
tags: [functor, fixpoint, operad]
description: Lets start the blog
image: code.jpg
---
- TODO: Fix typo in first blog post 
- TODO: Merge drafts, find leftover drafts lying around in /home

## Fixpoints over Functors
In the previous two blog posts we've looked at a combinator language for categories, as well as a data type for simply typed lambda terms. We've also had a look at translating from one to the other. 

## Free Semirings
To start, let's look at how we'd normally implement a data type of semirings. 

```idr
data Semiring : Type -> Type where 
  Val : a -> Semiring a
  Zero : Semiring a 
  One : Semiring a
  Mult : Semiring a -> Semiring a -> Semiring a 
  Add : Semiring a -> Semiring a -> Semiring a 
```

Now we would like to implement an evaluator for each of the constructors of the semiring.

Rather than doing it manually for each choice of function, we would like to abstract it

eval : (zero : a, one : a, mult : a -> a -> a, add : a -> a -> a) -> Semiring a -> a 
eval ... 

Writing out the entirety of all constructors each time would get tedious though, so we can abstract away the common pattern into what is known as an algebra

AlgebraSemiring : Semiring a -> a 

But we can even go further 
Algebra : f a -> a 

Now our evaluator looks like 

eval : Algebra Semiring a -> Semiring a -> a  
eval .... 

This is great, but what happens when we decide to implement another data structure? Let's say we wish to build an evaluator for a list.
 
eval : Algebra List a -> List a -> a
... 

We now need to write a new eval function from scratch. 

What if instead we could write a generic function.

eval : Algebra f a -> f a -> a? 
eval = ---what-goes-here?

This is what recursion schemes and fixpoints of functors let us do. 

## Fixpoints of functors
We can refactor our free semiring by introducing a datatype of type level fixpoints:

```idr
data Mu : (Type -> Type) -> Type where 
  In : f (Mu f) -> Mu f
```
This lets us rewrite our previous data type in terms of what is called a 'base functor'. Since Mu essentially consumes a free variable to use for recursive calls, we'll have to fix our values to some hardcoded type, ie Nat.

```idr
data SemiringF : Type -> Type where 
  Val : Nat -> SemiringF r
  Zero : SemiringF r 
  One : SemiringF r
  Mult : r -> r -> SemiringF r 
  Add : r -> r -> SemiringF r

data ListF : Type -> Type -> Type where 
  NilF : ListF a b 

Semiring : Type 
Semiring = Mu SemiringF

ex1 : Semiring 

ex2 : Semiring

The syntax encoding looks a bit harsh, but we can use smart constructors to make it nicer

ex1'
ex2'

the upside is that now we have a *generic* evaluator for any data-type f

cata : (f a -> a) -> Fix f -> a 

```

Of course, we don't actually want to lose the flexibility of working with an arbitrary carrier. So we can turn our SemiringF into a functor with two variables, the first of which is our carrier, and the second takes care of the recursive position. 

```idr
data SemiringF : Type -> Type -> Type where 
  Val : a -> SemiringF a r
  Zero : SemiringF a r
  One : SemiringF a r
  Mult : r -> r -> SemiringF a r 
  Add : r -> r -> SemiringF a r

Semiring : Type -> Type 
Semiring a = Mu (SemiringF a)
```

We've now recovered our original formulation of a free term algebra over a semiring.

If we get bored of writing the Functor instance each time, we can do a mendler version:

However, it's now a little bit wonky that we're treating a semiring as a *bi*functor. While there's a formulation of these container like base functors that treats them as semirings, the route we'll go instead is to generalise from fixpoints of functors to free monads. This means that we now have an extra type argument that stands in for the variables of our expression. 


## Free monads 
"Free monad over the signature of a semiring"

```idr
  data Free : (base: Type -> Type) -> (var : Type) -> Type where 
    Var : v -> Free f v
    In : f (Free f v) -> Free f v
```

```
data SemiringF : Type -> Type -> Type where 
  Zero : SemiringF a r
  One : SemiringF a r
  Mult : r -> r -> SemiringF a r 
  Add : r -> r -> SemiringF a r
```

With our evaluator now being

```idr
eval : 

```


Now we can either interpret the variables as merely values, and treat them as before. Or we can treat the variables as variables, ie working with *open* terms. 

Fix f = Free f Void 
Free f a = Fix f + Id a

However, here we run into a problem.

We can either choose a fixed set of variables, and define an evaluator for them. But then we'd lose the ability to add new ones. 
Disjoint set 

Or we can use a large set of variables such as String, but then we'd need to handle variables that aren't in scope, evaluating in some kind of error monad. 

show eval: 

We could even use Fin, but our number of variables will stay fixed globally in an expression. So we need some way of indexing our terms by a Fin, but we don't want to fix the size of `n` a priori, ie we'd like `n` to *change* as we build up our terms.

-- Initiality, some other constructors, proofs: https://github.com/bkomuves/idris-experiments/blob/master/Generic/InitialAlg.idr
## Free operad with Let
We could try to formulate some notion of 'monad with let binding' that let's us interact with the variables.
It would look something like
```idr
FreeOp
```

todo: eval 


But the problem is that this is no longer a *monad* in the traditional sense, in fact it doesn't look like a monad at all. We could try to formulate this as an indexed functor, along with a whole bunch of recursion scheme machinery for working with indexed types - which we will do in the next blog post - but for now our goal is to keep things simple. The problem with the indexed version is that indexed functors have carriers in indexed types. But we'd like to formulate algebras with carriers in standard types.  

Can we turn FreeOp into some kind of monad? Yes we kan! There's a clever trick that we can use here involving relative monads, but before we get to it, let's take a little detour and fix another one of our running problems and generalise away from needing a functor instance. It might seem like a segway at first, but it will pay off in the end.  

## Freer Monads
The standard way of formulating free monads that don't need a functor constraint is known as a "Freer" monad. It's a bit of a silly pun, since it's still *free*, just on something else. Whereas the free monad is free on a functor, the freer monad is free on an arbitrary data type. 

```idr
data Freer : (Type -> Type) -> Type -> Type where
  Var : v -> Freer f v 
  In : f x -> (x -> Freer f v) -> Freer f v
```
You can see that `In` looks a lot like the kleisli arrow of a monad 
```
bind : f x -> (x -> f v) -> f v
```
So essentially we're building in the kleisli continuation into the term itself. 

Our evaluator now being

```idr
eval : 

```

We can now evaluate our terms without needing a functor constraint, at the expense of a slightly more awkward syntax. 
But at this point it's worth asking: *what does being a freer monad really mean?* 


## Fixpoints over Free functors
So far we've been building a lot of freely generated structures: free monads, free monoids, free semirings... So why not build free functors as well? 

In functional programming, the free functor is known as "Coyoneda". The name is derived from the coyoneda lemma, but for our current purpose it doesn't matter what it *means*, merely what it *does*. And what it will do for us, is act as a very versatile piece of glue code. 

:TODO: formula
:TODO: data type 

The data type for Coyoneda is like a suspended map: it takes in the function to be mapped over, and a functor, and waits for it to be applied. The application happens using the corresponding algebra of Coyoneda, aka an implementation of the map. 

algCo : Coyoneda f b -> AlgebraH Coyoneda f -> f b 

It's a well known bit of functional programming folklore that algebras over coyoneda are the same thing as Mendler algebras

mcata : ... 
mcata : Algebra Coyoneda f
:TODO: kmett post

The usual formulation of mendler catamorphisms changes the algebra but keeps the fixpoint as is. What's less well known, is that you can actually change both, and incorporate Coyoneda into the fixpoint itself.

data Fix' : 
  Coyoneda f -> Fix' f 

The evaluator doesn't change much, we just have an explicit continuation that we're carrying around. 

If we unroll this, we'll notice that it's starting to look very familiar: 

data Fix'' 
  ... 

## Free monads over free functors
So Freer monads are nothing more than a mendler style free monad, ie a free monad over a free functor. So the traditional interpreter could be rewritten as 

catafr : (a -> c) -> Algebra f a -> Freer f a -> c

But we could also use the insight we've learned from the previous section and incorporate our Coyoneda into the algebra itself.

```idr
catafr : (a -> c) -> Algebra (Coyoneda f) c -> Freer f a -> c
catafr g alg = go where 
  go : Freer f a -> c
  go (VarFr a) = g a
  go (InFr action continue) = alg $ Coyo (go . continue) action 
```

Why would we want to? For starters, this would let us do a simplified mendler fold for a *free* monad, rather than a freer one

```idr
catafr : (a -> c) -> Algebra (Coyoneda f) c -> Free f a -> c
catafr g alg = go where 
  go : Free f a -> c
  go (VarFr a) = g a
  go (InFr action continue) = alg $ Coyo (go . continue) action 
```

But there's another reason why we might want to do this, which has to do with another piece of functional programming folklore.

## My favorite piece of glue code 
If you've ever stayed up late browsing the various category theory packages on hackage, you might have come across a data type known as a "left kan extension", which bears a striking resemblance to Coyoneda. 

```idr
data Lan :
```

In fact, the kan extensions package even provides a couple of helper functions to translate between the two

Lan == Coyo

While the term "left kan extension" sounds very daunting, just as before we don't need to worry about what it *means*, only what it *does*. And what it does is give us one half of a pair of sledgehammers that will trivialize a lot of what is to come. 

## The free relative monad 

We've seen before that OpLet is not a monad, it doesn't have quite the right shape. But it's actually quite close to something called a relative monad, realtive to some indexing functor K => Type. 

data Tm : ...

We can see that the thing in the middle is exactly our familiar friend, the left kan extension. 

data Tm' : ...
  Lan 



We can recover Free as Lan Id 


Now our terms have a peculiar shape. Each term is indexed by the number of their recursive positions. 
We've also lost the dangling type variable, and replaced it by Fin n. 

This means that none of our terms are carrying *values* merely variables.
When we interpret the free Fin monad, we need to provide a value to each of the variables. 

TODO: translate form fin algebras to coyoneda algebras to kan algebras

## Conclusion

In this post, we have seen the first glimpse of the free relative monad, and we've seen that it corresponds to fixpoints of endofunctors and free monads. The jargon way of describing what it is, is that it's a "free operad", ie a single sorted algebraic theory. 
In the following blog posts we will see that we could do far more than just this with our machinery: multi sorted algebraic theories, signatures with binding, and full fledged *type theories*. 



## Vect-representation of a free operad

## Let bindings?

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

namespace Fin 

data Op : (Nat -> Type) -> Nat -> Type where 
  Var : Fin n -> Tm f n 
  Op : f n -> (Fin n -> Tm f m) -> Tm f m
  OpV : {n : Nat} -> g n -> Vect n (Tm g m) -> Tm g m
