---
title: "Lambda Calculus and Bicartesian Closed Categories, Part 1"
author: Zanzi
date: Aug 10, 2023
tags: []
description: Lets start the blog
image: code.jpg
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



---
[1] When I say 'free' I mean 'inductively defined'. It's not *quite* free in the proper sense