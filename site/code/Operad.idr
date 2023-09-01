{--
Very broadly, the purpose of this blog series is to introduce the multicategory perspective. In a sense, multicategories generalise both categories and data types. Because of this, the series will be split into three parts:
Data types - applying category theory to functional programming to get generic tools for working with data types
Categories - treating categories themselves as data types and applying our machinery from part 1 to do category theory 
Multicategories - using the tools from part 1 and part 2 to work with type theories


This post will introduce the core tools that we will use throughout the series. Everything else will be some variation of this. At times it might be non-intuitive, but I encourage you to experiment with the code. 

'Simple but not easy'. 

Some refs:
  Universality of fold: https://www.cs.nott.ac.uk/~pszgmh/fold.pdf

--}
-- from functor to operad

data Mu : (pattern : Type -> Type) -> Type where 
  In : p (Mu p) -> Mu p 

-- compare to fixpoint of function?

-- cata

data Free : (pattern: (Type -> Type)) -> (var: Type) -> Type where
	Var : v -> Free p v
	In : p (Free p v) -> Free p v

-- eval 

-- TODO: show translation
-- Mu f = Free f Void
-- Free f a = Mu (f + Const)

{-- However, this assumes that our function (a -> c) is total. 
If we use a type like String to define our variables, this will take a long time. 
We could use a disjoint union of variables
data Var : X | Y | Z
But then this would lock us into a fixed number of variables, while we want to be able to bind new 

So we need a representation of a finite set of N elements
we can use an indexed type for this

data Fin n : Nat -> Type 
  FZ .. 
  FS ..

Then we could change Var to take this finite set of variables, and build a term out of them
    Var : Fin n -> Operad f n a

Then our type becomes indexed by variables. We take an endofunctor (Type -> Type) and get an indexed type (Nat -> Type -> Type)

TODO: (Nat -> Type -> Type) or (Nat -> Type) ?
data Operad : (Type -> Type) -> (Nat -> Type -> Type) where 
  Var : Fin n -> Operad f n a
  -- TODO: Which of these to use?
  LetF : f (Operad f (S n) a) -> Operad f n a
  LetBind : f a -> Operad f (S n) a -> Operad f n a

When talking about freeness, it's important to specify what we are free over. 
We'll call this the free operad over endofunctors. Later on, we'll meet the free operad over a signature. 

Our new evaluator then becomes
TODO: non-mendler version... im just showing off.
mcata : (Fin n -> c) -> Algebra f c -> Operad f n -> c
mcata g alg = go where
go : Free f a -> c
go (Var a) = g a
go (In $ fs) = alg $ (mcata g alg) fs

TODO: is this a relative monad? Double check the formulation.

TODO: From Operad to Free Monad and back?
In a sense, an operad is a reified version of a monad. If Monads generalise Lists, then Operads generalise Vectors

--}

{-- Fixpoints all the way up

Last post we've introduced several related constructions. Fixpoints of functors, free monads over functors, operads over functors. It's a proliferation of datatypes of datatypes. 
In this blog post we will see how all of these are actually the same concept. 

Fix

Coyo

HFix
HCoyo 

IxFix 
IxCoyo 

It would be nice if we could formulate a uniform definition of all of the above. 
While expressing a type of algebras parametric over some underlying category is straightforward
GenAlg : ... 
Which lets us recover our previous definitions of algebra
Alg = GenAlg Idr
HAlg = GenAlg Nat 
IxAlg = GenAlg IxNat 
(TODO: Try mendler version?)
It's much harder to generalise the remaining components of the fixpoint definition
cata : ... 
Becuase we have data-types, which necessarily have Type in their codomain, limiting our expressivity. 
It could still be possible to do a deep encoding of the idea, as was done in Phil Freeman's blog, using generalised functors
But a strong emphasis of this series is that all of our top-level machinery needs to be first-class, ie our language's type system needs to enable us to be able to write the kinds of programs that we want.
Nevertheless, we will go back to this point once we apply our tools to the 


-- Constrained/Restricted Monads

There are a lot of possible avenues of exploration here. What structure do these subcategories have? What sort of adjunctions are possible between them? What structure is preserved by (co)products, etc? What would f-algebras in them look like?

If we have Fix, we can have free. And if we have Free, we can have Fix one level up. So the cycle can continue as needed. 
  It's fixpoints all the way up!

--}

{-- Mendler Algebras and Relative Monads
Last post we've looked at how fixpoints of functors in different categories give us a unified notion of syntax. 
It's a useful conceptual picture, and it teaches us a very valuable skill of being able to jump between categories. 
But it is not the only perspective on this. There is another generalisation that we could use, one that takes the concept of a monad as primitive. 

In the previous post we've used Coyoneda as a convenient way to avoid writing boilerplate code. 

-- TODO: mcata

-- TODO: meval

-- TODO: relative eval

Then show how we can recover meval as relative monad to the identity

The reason why this perspective is valuable is that it avoids jumping between levels.
Previously, each of cata, eval, reval lived in separate categories
But now they live in the same place. A lot of the time we want to be able to add variables to a language without redoing the infrastructure, and this allows us to do so
Still, it's a matter of taste, and some prefer the simplicity of the fixpoint perspective.

In the next post we will get some hands-on experience working with relative monads by looking at a prototypical example, restricted monads. As functional programmers know, sets do not form a monad over types because they require an equality constraint.
However, they form a relative moad. 
In the post after that, it will be time to have The Talk that all budding category theorists have: where monads come from. 

--}