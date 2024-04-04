---
title: "Introduction to Recursion Schemes with Idris"
author: Zanzi
date: Apr 4, 2024
tags: []  
description: Refactoring Algebraic Datatypes with Recursion Schemes
image: algebraic-fish.png
---

## Fixpoints over Functors
In the previous two blog posts we've looked at a [combinator language for categories](https://zanzix.github.io/posts/1-bcc.html), as well as a [data type for simply typed lambda terms](https://zanzix.github.io/posts/2-stlc-idris.html). We've also had a look at translating from one to the other. Both blog posts assumed quite a bit of background knowledge, so our goal today will be to start at the very beginning and introduce recursion schemes step by step. 

## Semirings
To start, let's look at how we'd normally implement a datatype for semirings, along with an evaluator for it, and then see how we can generalise it using recursion schemes. 

First, we'll add a constructor for each operation. 
```idris
namespace Simple
  data Semiring : Type -> Type where 
    Val : value -> Semiring value
    One : Semiring value
    Zero : Semiring value 
    Mult : Semiring value -> Semiring value -> Semiring value 
    Add : Semiring value -> Semiring value -> Semiring value 
```

Now we would like to implement an evaluator for each of the constructors of the semiring.

Following the Haskell tradition of writing folds, it would look something like this:
```idris
  eval : (add : a -> a -> a) -> (mult : a -> a -> a) 
      -> (zero : a) -> (one : a) -> Semiring a -> a 
  eval _ _ _ _ (Val v) = v
  eval _ _ _ one One = one
  eval _ _ zero _ Zero = zero
  eval add mult zero one (Mult x y) = 
    mult (eval add mult zero one x) (eval add mult zero one y)
  eval add mult zero one (Add x y) = 
    add (eval add mult zero one x) (eval add mult zero one y)
```
This function, [known as a fold](https://www.cs.nott.ac.uk/~pszgmh/fold.pdf), is capable of expressing any interpreter that consumes this data type. However, while folds are interesting theoretically, the function itself is fairly boilerplate - all it's doing is matching constructors of the datatype to individual functions that consume them. 

Since we're going to be writing a lot of datatypes, we want to avoid writing an individual evaluator for each of them - we'd rather get them for free. If we had macros in our language, we could use them for this. But we don't need macros where we're going, as we've got category theory. 

The starting idea is that the same way that we bundle up our constructors into a single datatype, we can bundle up our consumers together as well. 

```idris 
  record SemiringAlgebra (a : Type) where 
    add : a -> a -> a     
    mult : a -> a -> a    
    zero : a               
    one : a     

-- if we uncurry we can see that these are all just morphisms of a category
  record SemiringAlgebra' (a : Type) where
    add : (a, a) -> a
    mult : (a, a) -> a
    zero : () -> a
    one : () -> a
```
Using SemiringAlgebra we can get a slightly cleaner looking evaluator: 
```idris 
  eval' : SemiringAlgebra a -> Semiring a -> a 
```
But it would involve the same amount of boilerplate as before. 

The problem is that we are essentially declaring each concept twice - once as a constructor, and once as a function consuming it. What we would like is to do declare it once, and derive the rest from that single declaration.

Now, Semiring has the type `Type -> Type`, and so does SemiringAlgebra. So we want something of the type `(Type -> Type) -> (Type -> Type)`. This turns out to be fairly straightforward:

```idris 
Algebra : (Type -> Type) -> (Type -> Type)
Algebra f a = f a -> a 

SemiringAlgebra' : Type -> Type 
SemiringAlgebra' a = Algebra Semiring a 
```
But how would we use such a thing? Naively, it seems that our evaluator has now become trivial:
```idris 
evalNope : Algebra Semiring a -> Semiring a -> a 
evalNope alg s = alg s 
```
This type checks, however it does not do anything interesting, it merely applies the function that we've supplied to it, and we still need to define that function manually. What we really want is for this function to be derived for us from smaller pieces.  

To resolve this, we notice that our original SemiringAlgebra record does not actually tell us how to tear down a full semiring. All it does is tell us how to tear down each individual layer. So let's start by describing these layers as a data type. 

```idris 
data SemiringLayer : Type -> Type -> Type where 
  Val : value -> SemiringLayer value expression
  One : SemiringLayer value expression
  Zero : SemiringLayer value expression
  Mult : expression -> expression -> SemiringLayer value expression
  Add : expression -> expression -> SemiringLayer value expression
```

The structure of this datatype is very similar to our original Semiring. But whereas Semiring was inductive - we defined complex expressions in terms of simpler ones - our new SemiringLayer only defines the contents of a *single* layer. And rather than being parametrised by a single type of values `Type -> Type`, we now take two parameters `Type -> Type -> Type`: one for values, and one for complex expressions. 

The result is that our ideal evaluator would now look like this: 
```idris 
evalAlg : Algebra (SemiringLayer val) val -> Algebra Semiring val  
```
In other words, we lift an algebra over a layer of a semiring to an algebra over the entire semiring. 
The final piece of the puzzle is that we would like to derive `Semiring` from `SemiringLayer`, rather than defining them separately. 

We do this by using a type-level fixpoint that operates on datatypes. 

```idris
data Fix : (layer : Type -> Type) -> Type where
  In : {layer : Type -> Type} -> layer (Fix layer) -> Fix layer
```
It is not unlike a standard fixpoint operator that works on functions:
```idris
partial
fix : (a -> a) -> a 
fix f = f (fix f)

-- Don't try this at home: 
-- SemiringBoom : Type -> Type 
-- SemiringBoom value = fix (SemiringLayer value)
```
Using `Fix`, we can now define `Semiring` inductively in terms of `SemiringLayer` - each time that `SemiringLayer` expects an expression, `Fix` will fill that in with `Fix SemiringLayer` as a subexpression:

```idris 
Semiring : Type -> Type 
Semiring value = Fix (SemiringLayer value)

-- example expression
ex1 : Semiring Nat 
ex1 = In (Mult (In One) (In $ Val 2))
```
The small downside is that we now have `In` around our code, however this can be avoided using smart constructors.

Now we can finally define our evaluator uniformly without mentioning any individual constructor:
```idris
-- We'll need a functor constraint for what's to come: 
Functor (SemiringLayer a) where 
  map f (Val x) = Val x 
  map f One = One
  map f Zero = Zero 
  map f (Mult x y) = Mult (f x) (f y) 
  map f (Add x y) = Add (f x) (f y)

-- Lift an algebra of a semiring layer to a semiring
eval : Algebra (SemiringLayer val) a -> Fix (SemiringLayer val) -> a 
eval alg (In op) = alg (map (eval alg) op)
```
And since our `eval` makes no reference to the constructors of `Semiring`, this means that we can generalise it to an arbitrary functor. 
```idris
-- Mission accomplished. 
cata : Functor f => Algebra f a -> Fix f -> a 
cata alg (In op) = alg (map (cata alg) op)
```
We can now apply our `cata` to arbitrary datatypes (with some restrictions, that we will talk about later in the blog), and provided that we give them a functor constraint. 

```idris
data ListLayer : Type -> Type -> Type where
  Nil : ListLayer val expr 
  Cons : val -> expr -> ListLayer val expr 

Functor (ListLayer a) where 
  map f [] = []
  map f (Cons x y) = Cons x (f y)

List : Type -> Type 
List a = Fix (ListLayer a)

-- we get the evaluator for free!
foldr : Algebra (ListLayer a) a -> Fix (ListLayer a) -> a 
foldr = cata
```

It's worth tracing out what exactly happens when we use `eval` - the gist of it is that there are two things that we need to do: use `map` to go under an `f` to turn `f (Fix f)` into `f a`, and then use `alg` to turn an `f a` into `a`. 

We can split `cata` into two mutually-inductive functions, each of which is responsible for one of these steps. As a bonus, this makes it structurally recursive over Fix f.
```idris
mutual
  -- take a layer of `f a` to an `a`
  fold : Functor f => (f a -> a) -> Fix f -> a 
  fold alg (In x) = alg (mapFold alg x)

  -- go underneath an f to turn Fix f to a
  mapFold : Functor f => (f a -> a) -> f (Fix f) -> f a 
  mapFold alg op = map (fold alg) op
```

It can get tedious writing all these functor constraints after a while. If we had macros, we could automate this, but once again we can get away without macros with the help of category theory - using what is known as the Coyoneda trick.

## The Coyoneda Trick 
A lot has been written about the Yoneda lemma, and its dual cousin, Coyoneda. Personally, I find that it's one of those concepts that you don't so much "understand" as "get used to". And the best way to get used to something is to use it, which - luckily for us - we'll have plenty of opportunity to do so. 

The datatype representing Coyoneda is simple, it is a pair of a value inside of a functor, and a function that will map this value. Essentially, it is nothing more than a suspended map operation: 
```idris
data Coyoneda : (Type -> Type) -> Type -> Type  where
  Map : {0 a : _} -> (a -> b) -> f a -> Coyoneda f b
-- map :             (a -> b) -> f a ->          f b
```
In other words, Coyoneda is to functors as SemiringLayer is to semirings - it's a data type that holds the contents of a functorial map, the same way that SemiringLayer holds values of some semiring. Like SemiringLayer, Coyoneda comes with its own notion of algebra, and we will make this precise in a futre blog post.
```idris
-- When `f` is a functor, we can tear down a layer of Coyoneda
mapCoyo : Functor f => Coyoneda f b -> f b 
mapCoyo (Map f fa) = map f fa 
```
Using this trick, we can modify our generic evaluator to no longer need a functor constraint:
```idris 
mcata : Algebra (Coyoneda f) c -> Fix f -> c
mcata alg (In op) = alg (Map (mcata alg) op)
```
The `m` in `mcata` stands for `Mendler`, and `Algebra (Coyoneda f) a` is commonly known as a `Mendler Algebra`. 
```idris
MAlgebra : (Type -> Type) -> (Type -> Type)
MAlgebra f a = Algebra (Coyoneda f) a 
```

Kmett wrote a [great post about catamorphisms and Mendler catamorphisms](https://www.schoolofhaskell.com/user/edwardk/recursion-schemes/catamorphisms), and it includes how to go from `cata` to `mcata` and vice versa.

## Algebra Transformers 
The downside of using Mendler-style recursion schemes is that our algebras become a tad more involved. Compare the following: 
```idris 
-- monoid of natural numbers, standard algebra style
algPlus : Algebra (ListLayer Nat) Nat 
algPlus [] = 0 
algPlus (Cons x y) = x + y

-- monoid of natural numbers, Mendler style
malgPlus : MAlgebra (ListLayer Nat) Nat 
malgPlus (Map f []) = 0
malgPlus (Map f (Cons x y)) = x + f y
```
Whereas a normal algebra merely accesses the values of each constructor, a Mendler algebra carries around an extra function that we need to apply before accessing sub-expressions. 

One way around this is to use algebra transformers, ie. a way to turn a simple algebra into a more complex one. 
In this case, we can derive a Mendler algebra from a standard one:
```idris
malgToAlg : Algebra (ListLayer v) a -> MAlgebra (ListLayer v) a
malgToAlg alg (Map f []) = alg []
malgToAlg alg (Map f (Cons x y)) = alg (Cons x (f y)) 
```
We can now use standard algebras with `mcata`, as if they were Mendler algebras: 
```idris 
listEval' : Algebra (ListLayer v) a -> Fix (ListLayer v) -> a 
listEval' alg = mcata (malgToAlg alg)
```
What's interesting is that if we look at `malgToAlg` closely, we'll see that it's nothing other than an inside out functor interface for ListLayer. So in the end we did about the same amount of work as before, but at least with Mendler algebras we could choose when to do it, and we were not forced to write all of our interfaces up front. 

If we had macros at our disposal, we could actually derive malgToAlg automatically. And... well, now I actually wish that I had macros at my disposal here. (Or at least that I had a working knowledge of [elaborator reflection](https://github.com/stefan-hoeck/idris2-elab-util/blob/main/src/Doc/Index.md), which could accomplish the same thing). 

At this point, we might wonder if going through Mendler algebras is worth it if they are equally expressive to standard algebras. As we will soon see, the answer is yes, as a small generalisation to Mendler algebras - leading to what I call "Kan algebras" - will give us a vast amount of expressive power that can capture many datatypes of interest besides those representable as functors on sets. 

But before we get to that, let us talk about monads. 