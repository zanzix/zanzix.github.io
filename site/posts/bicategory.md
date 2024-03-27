---
title: "From Monoid to Monoidal Bicategory"
author: Zanzi
date: Aug 25, 2023
tags: []
description: Bicategories
image: bibby.png
---

We've looked at a lot of rules, now let's look at where these rules come from. 

Function monoid
Generalises to path of functions - horizontal categorification
Or parallel compositions of functions - vertical categorification
Together they form a monoidal category, but there's something not quite right (no intro/elim for tensor)

We can take the semiring of types
And a semiring of functors with composition

These vertically categorify to categories of types and functors
Types form a type-level semiring, with intro/elim rules

Functors also form a type level semiring with composition, with intro/elim rules
But functor composition doesn't have an intro/elim rule, being a monoidal product
Show the monoidal category of functors as Path + Par

This is fixed by a natural deduction style syntax, ie treating the category of functors as a linear multicategory
Now we can also add an intro/elim for day convolution

But functors also form a category between categories, so we can put them into a path. This is horizontal categorification
Now we can introduce ie a product of categories and functors between them

But what happens to our natural transformations from before?
Previously they were between objects. Now they are between arrows.
Vertical composition of nat transforms stays the same
But horizontal composition now uses composition of functors as a category

And what happened to our intro/elim rules? Functor composition now has a universal property w.r.t a path of edges

And what happens to the monoidal structures, product/coproduct/day?
They're not defined w.r.t path composition. We need a->b + c->d not a->b x b->c

So let's take a step back, and look at them from another angle. A pre-bicategory + par. 
Now we have a higher-level par that can form the universal properties of (co)products and day conv

So putting it together, we have a category indexed by a moonoidal category, where we can form universal properties of composition and monoidal products

We also have different notions of closure. 