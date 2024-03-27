---
title: "Building a Neural Network from First Principles using Free Categories and Para(Optic)"
author: Zanzi
date: Mar 13, 2023
tags: []
description: Building a Neural Network from First Principles using Free Categories and Para(Optic)
image: code.jpg
---

## Introduction

Our goal is to form this: A simple neural network with statically-typed parameters, and input and output sizes. 

```idris
model : GradedPath ParaLensVect (params : [[2, 2], [2], [], [2, 2], [2]]) [source: 2] [target: 2]
model = [linear, bias, relu, linear, bias] 
```

The cruicial part is the so-called Para construction, which lets us accumulate parameters along the composition of edges. This let's us state the parameters of each edge separately, and then compose them into a larger whole as we go along. 

## Graded Monoids 
Para forms a graded category, and in order to understand what this is we will start with a graded monoid first. 


```idris
  data Env : (k -> Type) -> List k -> Type where 
    Nil : Env f [] 
    (::) : f n -> Env f ns -> Env f (n::ns) 

  Vec : Nat -> Type 
  Vec n = Fin n -> Double

  f1 : Vec 1 
  f2 : Vec 2
  f3 : Vec 3

  fins : Env Vec [1, 2, 3]
  fins = [f1, f2, f3] 

  avg : Env Vec ns -> Double 
```
## Graded Monads 
Just as we can form a graded monoid, we can form a graded monad 

