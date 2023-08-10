---
title: "Fixpoints all the way up"
author: Zanzi
date: Aug 10, 2023
tags: [functor, fixpoint, operad]
description: Lets start the blog
image: code.jpg
---

In the previous blog posts, we've looked at free operads for well-scoped domain specific languages. A natural question to ask, is what would it mean to have a well-typed language?

TODO: Start with Type -> Type instead of Ty->Type and show that we can extract the recursive component just as well

We will look at it in this blog post.

Let's say we have a simple language, with Booleans and Arithmetic

First we define our types

```idr
data Ty = BOOL | NAT
```

Then we define our data type, indexed by the types

```
data BoolArith : Ty -> Type 

V1 : interpTy type -> BoolArith1 type

AddNat : BoolArith1 NAT -> BoolArith1 NAT -> BoolArith1 NAT

Conj : BoolArith1 BOOL -> BoolArith1 BOOL -> BoolArith1 BOOL

```

  
We could write a custom evaluator for our well-typed DSL


```idr
evalBA1 : BoolArith1 t -> interpTy t

evalBA1 (V1 t) = t

evalBA1 (AddNat e1 e2) = (evalBA1 e1) + (evalBA1 e2)

evalBA1 (Conj e1 e2) = (evalBA1 e1) && (evalBA1 e2)

```

But instead we'd like to use our general machinery

So as always, we start by extracting the recursive component

```idr
data BoolArithF : (Ty -> Type) -> (Ty -> Type) where

VF : interpTy type -> BoolArithF r type

AddF : r NAT -> r NAT -> BoolArithF r NAT

ConjF : r BOOL -> r BOOL -> BoolArithF r BOOL
```

We can see that (Ty -> Type) is an indexed data type, so BoolArithF is an endofunctor over indexed types 

BoolArithF : Functor (Ty -> Type)

So to tie the recursive knot, we need a fixpoint over an indexed endofunctor


``` idr
data Mu : ((k -> Type) -> (k -> Type)) -> k -> Type where

In : f (Mu f) a -> Mu f a
```

So now we recover our previous data-type

```idr
BoolArith : Ty -> Type
BoolArith = (Mu BoolArithF)
```

If we want to evaluate our typed expressions, we can do it just as before.

``` 
example of eval
```

This is neat, but as in chapter 1, this only gives us closed expressions.

But what if we want our expression language to have variables?
ref: https://tyde.systems/post/2019-12-04-razor/

As we've seen before, to add variables we need to go from Mu to Free, and to make the variables well-scoped, we need to go from Free to Operad.

Let's do that straight away. 

However, what we notice is that while previously our type was

Operad : (Nat -> Type -> Type)

this is no longer sufficient for our purposes. Since we have more than one type, we need a more expressive scope than Fin

So what we can notice is that Nat is isomorphic to a list over a one-element set 
Nat == List Unit

So if we want to go from an untyped language to a typed one, we generalise our scope from Nat to List
Matching the intuition that an untyped language is the same as a language with a single type.
Or more accurately, a well-scoped language is a typed language with a single type.

So generalising from Nat to List, our constructor for well-typed expressions would look like this

```idr 
data RazorST : List Ty -> Ty -> Type where
	Let : RazorST ctxt a -> RazorST (a::ctxt) b -> RazorST ctxt b
```

extracting the recursive component
  
```idr
data RazorF : (List Ty -> Ty -> Type) -> List Ty -> Ty -> Type where
	Let : f ctxt a -> f (a::ctxt) b -> RazorST ctxt b
```


A multi-object operad is often called a coloured operad, a multi-sorted algebraic theory. 
They're also often called a multi-category, but I would make a distinction that a coloured operad is an operad over a finite number of types. A full-fledged multicategory, is an operad over an inductively defined set of types.

But we will get to that later.

