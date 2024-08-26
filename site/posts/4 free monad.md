---
title: "Free Monads with Idris"
author: Zanzi
date: Apr 4, 2024
tags: []  
description: TODO
image: algebraic-fish.png
---

## Free monads over endofunctors 
In our last post we've looked at fixpoints over endofunctors, and how they let us model algebraic data types generically. 

In this blog post we will look at free monads, and how they relate to fixpoints of endofunctors. This is mostly standard, but we'll go through it anyway for the sake of completion. 

To start, let's look at our SemiringLayer from our last blog post:

```idris
data SemiringLayer : Type -> Type -> Type where 
  Val : value -> SemiringLayer value expression
  One : SemiringLayer value expression
  Zero : SemiringLayer value expression
  Mult : expression -> expression -> SemiringLayer value expression
  Add : expression -> expression -> SemiringLayer value expression
```

One of these constructors is not like the others. While most constructors refer to subexpressions, `Val` refers to values. This makes SemiringLayer a *bi*functor, ie a data type with two parameters. While bifunctors (and n functors) are interesting in their own right, in this blog post we will take an alternative perspective and try to look at a semiring *generically* without reference to any underlying values. 

We start off by removing values from SemiringLayer

```idris
data SemiringLayer : Type -> Type where 
  One : SemiringLayer expression
  Zero : SemiringLayer expression
  Mult : expression -> expression -> SemiringLayer expression
  Add : expression -> expression -> SemiringLayer expression
```

Having removed them, we would like to introduce some notion of variable. We could have simply renamed `Val` to `Var` and called it a day, but our goal here is to formulate a general notion of "expression with variables", rather than a specific data type with a constructor for variables. 
To do so, we extend our Fix with an extra parameter 

```idris
data Fix : (layer : Type -> Type) -> Type where
  In : {layer : Type -> Type} -> layer (Fix layer) -> Fix layer

data Free : (layer : Type -> Type) -> (var : Type) -> Type where
  Var : a -> Free f a
  In : {layer : Type -> Type} -> layer (Free layer a) -> Free layer a
```

Interestingly, what we've invented is exactly the data type for a free monad. While functional programmers are familiar with using free monads to model effects, their original purpose was to model algebraic signatures in universal algebra. Which is exactly what they'll let us do here.

We can now form expressions of semirings with variables
TODO: Ex

And of course as we've noticed before, our new datatype is isomorphic to our old data type + a constructor for variables

But what's important is here is the perspective shift, as it will allow us a very powerful generalisation later. 

Our evaluator stays exactly as before, with the addition of a case for variables. if we set it to identity, we will once again recover our previous cata. 

## Algebraically free monads
Substitution as a free algebra

## Coyoneda trick part 2
We've seen the coyoneda trick in our last blog post, it also applies to this case as well
While we can change our notion of algebra just as before, and everything will work

eval : Free, Coyoneda f, a 

It's much more common in the literature to change the *syntax* of the datatype, and put coyoneda on the constructor. 

```
data Freer
```
It's interesting that we can do both. In fact, one of the original papers that looked at mendler catamorphisms considers the version that uses both the syntax and semantics, but concludes that just one is expressive enough. However, it will turn out that the generalisation we seek will in fact need both. 

Reader question: Can we reformulat mendler catamorphisms by using Fix Coyoneda instead of Fix?

Using Freer monads for expressions let's us use our meta language to handle variables

TODO: example 

Essentially the freer monad represents desugared do notation

TODO: ex, but with do notation 

## Lawvere Theories 
The previous example works, but it's not *entirely* satisfactory as we've now relegated binding to our meta language. This works fine if the scope discipline of our DSL matches the scope discipline of the meta-language. But what if it does not? We would like to have a more fine-grained theory of variables for cases such as that. 

The seeming awkwardness of monads in practice is why mathematicians working in functional languages prefer to use lawvere theories instead. 

A lawvere theory is the same thing as a finitary monad, but the presentation differs slightly. 
Instead of describing the underlying data-type as an endofunctor, we will describe it using a 'signature', which is a datatype indexed by natural numbers. 

```idris
data SemiringSig : Nat -> Type
  One : SemiringSig 0
  Zero : SemiringSig 0
  Mult : SemiringSig 2
  Add : SemiringSig 2
```

Each constructor now refers to the number of positions in it. We can now modify our Free data type by indexing our variables by the number of potential variables in the context.

```idris
data Op : sig : (Nat -> Type) -> Nat -> Type where 
  Var : Fin n -> Op sig n 
--      ^ introduce a variable
  Bind : f n -> Vect n (Op sig n) -> Op sig n 
-- constructor ^ ^assignment of variables 
```
I've first seen this representation in McBride, and it's been used in Frex too. 

TODO: example terms

We're now able to talk about both variables and scopes inside of the DSL. 

And the evaluator is straightforward, we just need to interleave going under Vects with evaluating Op itself

TODO: eval

However, we've seemingly lost the connection to semantics. While 'Free' and 'Freer' correspond to algebraically free monads, what we have now seems to be an entirely syntactical construct. 

But there is a way to recover that connection
### Representable functors
We first notice that `Vect n a` is a representable functor, which means that it witnesses an isomorphism with `Fin n -> a`

TODO: index, tabulate

### Relative monads 

Knowing this, we can rewrite our data type to now be 

```idris
data Op : (Nat -> Type) -> Nat -> Type where 
  Var : Fin n -> Op f n
  (>>=) : {n : Nat} -> f n -> (Fin n -> Op f m) -> Op f m
```
At first sight this doesn't necessarily buy us much, but if we squint we can see the similarity between our new >>= and our >>= for the freer monad

(>>=) : {n : Nat}  -> f n -> (Fin n -> Op f m) -> Op f m
(>>=) : {a : Type} -> f a -> (a     -> Op f b) -> Op f b

This is because Op forms a free *relative* monad.

TODO: flesh out interface
interface Relative j f 
  pure : j n -> f n 
  >>= : f n -> (j n -> f m) -> f m 

Relative Op f

Our new algebra is now indexed by Fin 

FinAlgebra : (Nat -> Type) -> Nat -> Type

What's amazing is that our evaluator now looks exactly as it did before:
```
feval : (Fin n -> c) -> FinAlgebra f c -> Op f n -> c 
feval env alg = go where 
  go : Op f n -> c
  go (Var a) = env a
  go (op >>= env) = alg (go . env) op
```

This begs the question: if the terms for meval and feval are the same, can we combine the two? 

### The Left Kan Extension Trick

There's something about FinAlgebra that looks like Coyoneda. 
  In   : Coyoneda   layer (Free layer a) -> Free layer a
  Bind : FinAlgebra   sig (Op     sig m) -> Op sig m

As we've seen from our last blog post, the purpose of `Coyoneda` is to take a datatype `f : Type -> Type`, and construct a free functor `Type -> Type` over it. But relative monads are not endofunctors, so Coyoneda is not suitable for our purposes. Instead, what we have is a functor `j : Nat -> Type`, and a functor `sig : Nat -> Type`, and we want to combine the two to construct a functor `Type -> Type`. Haskellers familiar with kan extensions will recognize this as a slight generalisation of the Lan datatype from kan extensions

```idris
data Lan : (j: k -> Type) -> (f : k -> Type) -> Type -> Type where 
  MkLan : {j: k -> Type} -> (j a -> b) -> f a -> Lan j f b
```
The phrase 'kan extension' sounds daunting, but just as Coyoneda is a recipe for constructing an functor from a data type, a left kan extension is a recipe for constructing a functor out of two other functors. So what happens if we replace Coyoneda with Lan in our definition of a Freer monad? Because they generalise Freer, I jokingly call this construction the

## Freest Monad 

data Freest : (j : k -> Type) -> (f : k -> Type) -> k -> Type where 
  Var : j n -> Op j f n 
--      ^ introduce a variable indexed by j
  Bind : f n -> (j n -> Op f m) -> Op j f n 
-- suspended relative bind

The freest monad constructs a monad given any functor `j : k -> Type` and `f : k -> Type`

TODO: Presheaf j => Relative Freest

This means that we can now recover both of our previous data types

Freer : Type ... 
Freer = Freest Id

Op : Nat
Op = Freest Fin 

And we can formulate a generic evaluator for an arbitrary free relative monad

Given a kan algebra 

KanAlgebra F 

Our evaluator is
```
eval : (j n -> c) -> KanAlgebra j f c -> Freest j f n -> c 
eval env alg = go where 
  go : Op f n -> c
  go (Var a) = env a
  go (op >>= env) = alg (go . env) op
```

## Conclusion
In this blog post we've introduced to of the most important tools that we'll be using through the rest of the series - free relative monads, and kan algebras. Relative monads give us a very powerful tool for modelling variable contexts, while kan algebras give us a very general way to evaluate relative monads. 

In future blog posts we will look at how varying the functor `j` can give us more exotic notions of context. 

But first, let's get some more practice with relative monads. 

