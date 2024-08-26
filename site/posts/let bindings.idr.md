---
title: "Adding let binders to free monads"
author: Zanzi
date: Apr 4, 2024
tags: []  
description: write me 
image: algebraic-fish.png
---

In a previous post, we've looked at free monads and free relative monads. 
In this blog post, we will explore how to add let binders and multi let binders to our DSL.

First, let's look at what a let binder is. I quite like the naming convention that I found on Jan's blog of "Let this beThis inThis". It's a helpful mnemonic to remember the role of each argument in a let binder. Since we are using Fins to represent our variables, the binder itself is represented as an extra successor variable in the context.

```idris
namespace Let
  data Op : (Nat -> Type) -> Nat -> Type where 
    Var : Fin n -> Op f n 
    (>>=) : {n : Nat} -> f n -> (Fin n -> Op f m) -> Op f m
    Let : Op f m -> Op f (S m) -> Op f m
```

TODO: eliminate Let
TODO: Substitution 

A more interesting variation would be to add multiple let bindings 
```idris
namespace Lets
  data Op : (Nat -> Type) -> Nat -> Type where 
    Var : Fin n -> Op f n 
    (>>=) : {n : Nat} -> f n -> (Fin n -> Op f m) -> Op f m
    Lets : {n : Nat} -> (Fin n -> Op f m) -> Op f (n + m) -> Op f m
```
Now we have the option of binding multiple variables 

TODO: Eliminate lets 

In practice, I find it much more comfortable to work with strings than numbers. So we can get the best of both worlds with a representation that uses strings but auto infers the variables 
-- Idris variable scopes: https://crunchytype.wordpress.com/2017/05/07/let-idris-take-care-of-you-variable-binding/

-- Strength: https://mathstodon.xyz/@zanzi/111711943133693877