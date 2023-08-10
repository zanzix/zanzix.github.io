---
title: "Lambda Calculus and Cartesian Closed Categories"
author: Zanzi
date: Aug 10, 2023
tags: [functor, fixpoint, operad]
description: Lets start the blog
image: code.jpg
---

I'm writing a blog series on programming with category theory. 



I want to make this accessible to people coming from either field - programmers wanting to understand category theory, type-theorists wanting to understand categorical semantics, category theorists wanting to see how programming or type theory can give syntax to their ideas

Instead of giving a semantics on paper, we would like to use the semantics in practice. 
Can we define a lambda calculus once, and then evaluate it into an arbitrary closed cartesian category?
And more generally, how can we extend this machinery beyond CCCs into languages based on monoidal, or traced, or even more exotic categories?




Things we will expand on

    De bruijn and contexts
    Free categories vs type-classes
    fully dependently-typed records for semantics

What kind of structure can we tear down?

    all connectives, leaving LetVal
    type-structure, leaving an operad
    context-structure, leaving a category
    all structural rules, going down to premonoidal
    evaluation strategy

data Cat : {o : Type} -> (o -> o -> Type) -> (o -> o -> Type) where
  Id   : Cat g a a 
  Comp : {o : Type} -> g b c -> Cat g a b -> Cat g a c  
  -- Dot  : {o : Type} -> g b c -> Cat g a b -> Cat g a c 

foldCat : Category c => ({0 x, y : _} -> g x y -> c x y) -> Cat g s t -> c s t 
foldCat _ Id = id
foldCat f (Comp g c) = (f g) . (foldCat f c)


In this post I would like to translate the simply typed lambda calculus into closed cartesian categories

First let's look at a definition of a 


---


-- 

* Conal's post: http://conal.net/blog/posts/overloading-lambda
* Follow-up: http://conal.net/blog/posts/circuits-as-a-bicartesian-closed-category
* Connor's paper (Compiling to CCCs):
* Bernady's follow-up (Compiling to SMCs):
* Will's post on profunctors and arrows: https://elvishjerricco.github.io/2017/03/10/profunctors-arrows-and-static-analysis.html
* vs SKI?: https://thma.github.io/posts/2021-04-04-Lambda-Calculus-Combinatory-Logic-and-Cartesian-Closed-Categories.html


---



First we will define an intrinsically typed language



``` idris
evalTy : Ty -> Type

evalTy N = Nat

evalTy U = ()

evalTy (Imp t1 t2) = (evalTy t1) -> (evalTy t2)

evalTy (Prod t1 t2) = (evalTy t1, evalTy t2)

evalTy (Sum t1 t2) = Either (evalTy t1) (evalTy t2)
```

As a first-pass, lets translate it into Idris

```
STLC -> Idris
```

Now we would like to translate it into category theory.

First define our classes
```
Records
```

Then define a translation from types
```
Ty -> evalTy 
```

