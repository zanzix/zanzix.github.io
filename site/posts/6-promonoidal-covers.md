---
title: "Compiler Engineering for Substructural Languages I: Day Convolution for Covers"
author: Zanzi Mihejevs
date: Feb 17, 2025
tags: []
description: Lets define some combinators
---

In the [previous post]() we've posed the problem of defining substructural polymorphism, but while we've defined substitution for a polymorphic language, we did not do so for the substructural one. We will rectify this in the current blogpost, as well as introduce some nice combinators for working with covers.

### Substitution in the Linear Lambda Calculus
First let's define substitution in the linear lambda calculus the way we'd do normally, then try to introduce some more general machinery.

Just as in the last post, we'll start by defining relevant covers, well-scoped lambda terms, and substitutions

```idr
data Cover : (k, l, m : List a) -> Type where
  Done   :                Cover      []      []      []
  Left   : Cover k l m -> Cover (a :: k)     l  (a :: m)
  Right  : Cover k l m -> Cover       k  (a::l) (a :: m)
  Both   : Cover k l m -> Cover (a :: k) (a::l) (a :: m)

--  Binary operators like 'App' have a Cover wrapped around them
data Term : List String -> Type where
  Var : {s : String} -> Term [s]
  Lam : {s : String} -> Term (s::g) -> Term g
  App  : Cover g1 g2 g -> Term g1 -> Term g2 -> Term g

data Sub : List String -> List String -> Type where
  Nil : Sub [] []
  -- ^the empty substitution
  Cons : {a : String} -> Term g1 -> Cover g1 g2 g -> Sub g2 d -> Sub g (a::d)
  -- add a term in context g1 to a substitution with context g2,
  -- and append their contexts
```

But now, let's actually see what the guts of substitution look like.


TODO: Substitution in plan

### Substitution using Day Convolution

TODO: cleaned up substitution

### Factor out covers
Now, what happens if we factor out the cover outside of Sub? This means that, what if instead of combining each individual context using Sub, we collect them into a list of contexts, and only have one outer cover?
