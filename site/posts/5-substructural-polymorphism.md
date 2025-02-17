---
title: "Compiler Engineering for Substructural Languages I: The Problem with Polymorphism"
author: Zanzi Mihejevs
date: Feb 14, 2025
tags: []
description: Can a correct-by-construction implementation of a substructural language be extended to a polymorphic lambda calculus?
---

We've been working hard at [Glaive](https://glaive-research.org/) to develop a language based on the classical sequent calculus, ie. a type theory with first-class support for continuations and call-cc. I will make a proper announcement of the language soon, but for now I just want to discuss a particularly subtle problem that came up in our development. (In the meantime, you can read [this excellent paper by Binder et al](https://arxiv.org/abs/2406.14719) to get a taste of what programming in this class of languages is like).

For very subtle theoretical reasons, the core language that we're developing needs to be substructural. The problem isn't with copying/deleting by itself - we can still copy and delete variables - this just needs to be done explicitly, at least in the core language. Jules wrote about [representing explicitly cartesian languages](https://zanzix.github.io/posts/4-substructural.html) on this blog before.

So the current intention is that the concrete syntax will be cartesian as normal, but it will desugar to a substructural core language with explicit copy and delete, aka. the Co-de-Bruijn representation. (Though now that we're working on a substructural core, we've actually been talking about experimenting with the design space of languages like Rust).

The problem we're facing, however, is that it's entirely unclear how to adapt a correct-by-construction implementation of a polymorphic language to a substructural discipline.

So the purpose of this blog series is two-fold:

On one hand, I would like to document the current progress of our language implementation in Idris - this will both be a showcase of using dependent types for general compiler engineering, as well as a collection of various folklore around implementing substructural languages specifically.

On the other hand, there are still many open questions that we have in this space, and there are practically no publications on this topic. So we would like to solicit feedback and see if anyone has some ideas that we've overlooked.

In this blog post I will introduce the problem by defining two separate lambda calculi - one with substructural variables, and one with polymorphism. The question of how to combine the two will be one of the main things that we'd like to answer by the time the series finishes.

### Substructural Languages from a Dependently-Typed Point of View
Let's start with the simply-typed substructural lambda calculus.

The main thing that happens when switching from a cartesian to a linear syntax is that we can no longer implicitly share contexts. This means that variables become singletons - only one thing can be in scope at the leaves, and that each term has its own context, so rules that involve more than one term (such as `App`) now need to explicitly combine them.

```idr
-- Naive representation of linear terms
data Term : List String -> Type where
  Var : {s : String} -> Term [s]
  Lam : {s : String} -> Term (s::g) -> Term g
  App  : Term g1 -> Term g2 -> Term (g1 ++ g2)
```

This of course creates the dreaded green slime in the domain of `App` - we now have a function in our data-type definition, which will cause problems later.

Because of this, the standard solution is to use 'covers', which represent the function (++) as a proof-relevant relation. This gives us a way to pattern-match on the Cover when needed, thus avoiding the unifier from getting stuck in such cases.

```idr
-- A relation for splitting relevant terms.
-- Each variable either goes into one of the contexts, or both.
data Cover : (k, l, m : List a) -> Type where
  Done   :                Cover      []      []      []
  Left   : Cover k l m -> Cover (a :: k)     l  (a :: m)
  Right  : Cover k l m -> Cover       k  (a::l) (a :: m)
  Both   : Cover k l m -> Cover (a :: k) (a::l) (a :: m)
```

Given a context `m`, the cover shows how to decompose it into the contexts `k` and `l`, by putting each variable into either one or both of the contexts.

Our term representation now looks like this.
```idr
--  Binary operators like 'App' have a Cover wrapped around them
data Term : List String -> Type where
  Var : {s : String} -> Term [s]
  Lam : {s : String} -> Term (s::g) -> Term g
  App  : Cover g1 g2 g -> Term g1 -> Term g2 -> Term g
```

This won't be a full introduction to Co-de-Bruijn, for more details I recommend [this blog post by Jesper Cockx](https://jesper.sikanda.be/posts/1001-syntax-representations.html) (Ctrl+F for 'Co-de-Bruijn'), [Conor's original paper](https://arxiv.org/abs/1807.04085), or [this great Masters thesis by Matthias Heinzel](https://studenttheses.uu.nl/bitstream/handle/20.500.12932/44219/thesis-final-matthias-heinzel.pdf?sequence=1&isAllowed=y).

In this blog post I'd like to focus on one of the reasons for *why* we care about Co-de-Bruijn, which is that it eliminates one of the biggest sources of inefficiency when it comes to implemeting substitution.

Regardless of which representation of substitution we use, we will inevitably need to perform substitution under binders. Traditionally, this is done by introducing the concept of a *renaming*, or *thinning*. The idea is that as we substitute under binders we additionally perform a renaming of a term, extending its context with a new variable. [András Kovacs has a great reference implementation here](https://gist.github.com/AndrasKovacs/bd6a6333e4eecd7acb0eb9d98f7e0cb8).

Semantically, this is nice - renaming forms a functor, substitution forms a (relative) monad on that functor. (We will look at this semantic perspective in more detail in a future series, but for now we'll just focus on the syntax).

Operationally, this is a nightmare - we now need to traverse each term twice, and moreover, the renaming doesn't *do* anything beyond keeping the contexts of sub-terms in sync with each other. Context sharing was meant to be a simplification, but now it induces a major operational cost on our implementation.

The beautiful thing about substructural languages is that they forego the need for renaming - because contexts are split, there's no need to keep them in sync. And because the variables are now singletons, there is no need to traverse the entire term just to update its context about all the variables it won't be using anyway.

In practice, our substitution datatype would look like this.

```idr
-- A substitution for a substructural language
data Sub : List String -> List String -> Type where
  Nil : Sub [] []
  -- ^the empty substitution
  Cons : {a : String} -> Term g1 -> Cover g1 g2 g -> Sub g2 d -> Sub g (a::d)
  -- add a term in context g1 to a substitution with context g2,
  -- and append their contexts

-- Substitution traverses the term and applies the environment to each subterm
subst : Term g -> Sub d g -> Term d
```

(Compare it to [this definition in Kovac's implementation which uses implcit context-sharing](https://gist.github.com/AndrasKovacs/bd6a6333e4eecd7acb0eb9d98f7e0cb8#file-stlcsubst-agda-L162)). The only difference is that whenever we Cons a new term on the environment, we need to explicitly add its context using a cover.

This works well, modulo some wrangling of covers, for which we've come up with some helpful combinators with the help of Vikraman Choudhury, and that I'll show in the next blog post.

For now, the main point is that the most expensive operation - extending the context by a new variable - is now entirely free, [rather than requiring us to individually weaken each term in the environment](https://gist.github.com/AndrasKovacs/bd6a6333e4eecd7acb0eb9d98f7e0cb8#file-stlcsubst-agda-L179).

```idr
ext : {g' : List Ty} -> Sub g g' -> Sub (s :: g) (s :: g')
ext lift e = Cons Var (Left coverRightId) e
```
All we do is Cons a variable to an existing environment `e`, and our cover is a proof that the new variable goes on the left-most context, while all the other variables go on the right (this is what `coverRightId` does). None of the actual terms in `e` are touched at any point.

Now, unfortunately... I don't think this substitution datatype generalises to the polymorphic case, at least not in an obvious way.

To see that, let's first sketch out what a polymorphic language with shared contexts looks like.

### A Quick Introduction to Polymorphic Lambda Calculi
András Kovacs has us covered once again, as he has a [great reference implementation](https://github.com/AndrasKovacs/system-f-omega/blob/master/Term.agda).

Unlike András, we will be going with a well scoped rather than well typed representation, in order to avoid the buckets of green slime that a typical intrinsically typed implementation of System F will saddle us with.

First we will define types, which are now indexed by a list of type variables.

```idr
data Ty : (typeVars : List String) -> Type where
  VarT : Elem a g -> Ty g
  -- ^ Type variables
  Forall : Ty (s::g) -> Ty g
  -- ^ Type quantification
  Mu : Ty (s::g) -> Ty g
  -- ^ Least fixpoint of a datatype
  (~>) : Ty g -> Ty g -> Ty g
  -- ^ Function type
```

For terms contexts, the simplest approach is to define them as being indexed by two independent lists, one for type variables and one for term variables, as is [done by Sandro Stucki here](https://github.com/sstucki/system-f-agda/blob/master/src/SystemF/Term.agda):

```idr
Term : (typeVars : List String) -> (termVars : List String) -> Type
```

This representation is convenient to work with, but misses an important connection between the two contexts - term variables can refer to type variables in their types! So a more informative representation would allow the term context to be synced with the type context, and the standard solution to this is to index the latter by the former.

```idr
-- a list indexed by another list
data IxList : (a : Type) -> List a -> Type where
  Nil : IxList a []
  -- ^the empty IxList is indexed by the empty List
  (::) : a -> IxList a ls -> IxList a ls
  -- ^add a new term variable without touching the index
  (:::) : (el : a) -> IxList a as -> IxList a (el::as)
  -- ^add a new type variable,
  -- increasing the type context by which future term variables will be indexed
```

We now need a version of the [`Elem` data-type](https://www.idris-lang.org/docs/idris2/0.6.0/base_docs/docs/Data.List.Elem.html) for indexed list, ie. a proof-relevant variable that keeps track of its position in the context.

```idr
data IxElem : a -> IxList a ks -> Type where
  Here    : IxElem a (a :: as)
  There   : IxElem a as -> IxElem a (b :: as)
  ThereK  : IxElem a as -> IxElem a (b ::: as)
```

We've now got everything to define a well scoped fragment of System F.
```idr
data Term : (tyVars : List String)
         -> (trmVars : IxList String tyVars) -> Type where
  Var  : (var : String) -> IxElem {tyVars} var termVars -> Term tyVars termVars
  -- Proof that the variable var is in the IxList termvars

  Lam  : (a : String) -> (tya : Ty tyVars)
      -> Term tyVars (a :: trmVars) -> Term tyVars trmVars
  -- Lambda abstraction is standard, and includes a type annotation `ty`

  App : Term tyVars trmVars -> Term tyVars trmVars
     -> Term tyVars trmVars
  -- lambda application is standard

  In   : (f : Ty (tyVar :: tyVars)) -> Term tyVars trmVars -> Term tyVars trmVars
    -- inject into a term of a recursive type `f`

  Out  : (f : Ty (tyVar :: tyVars)) -> Term tyVars trmVars -> Term tyVars trmVars
    -- project from a term of a recursive type `f`

  TLam : (tyVar : String) -> Term (tyVar :: tyVars) (tyVar ::: trmVars)
      -> Term tyVars trmVars
  -- type abstraction now binds a type variable `k` in both contexts

  TApp  : Term tyVars trmVars -> Ty tyVars -> Term tyVars trmVars
  -- Type application applies a type to a term with a type lambda
```
For now we will assume some familiarity with System F, so I won't go into too much detail into what each constructor does, but we can rectify that in a future blog post. I recommend [this paper by Chapman et al](https://homepages.inf.ed.ac.uk/wadler/papers/mpc-2019/system-f-in-agda.pdf) (aptly called "System F in Agda, for Fun and Profit") in the meantime.

At this point, we have enough to start defining renaming and substitution, but before that we should take note of something interesting: because we designed our term contexts to be indexed by type contexts, this decision will propagate across all context operations. So term renamings are indexed by type renamings, and term substitutions are indexed by type substitutions.

For our purposes, we only care about substitution, since a substructural type system side-steps renaming.

In order to define term substitutions we first need to define type substitutions:

```idr
-- type substitution with implicitly shared contexts 'g'
data TySub : List String -> List String -> Type where
  NilTy : TySub g []
  -- ^empty type substitution.
  ConsTy : (tyVar : String) -> Ty g -> TySub g d -> TySub g (tyVar::d)
  -- ^extend the type substitution with a new variable
```
Contrast this to the earlier implementation of `Sub` which used a cover to concatenate contexts - we are now assuming that the context `g` is the same across all terms. While this simplifies the datatype, it comes at the cost of requiring any operation on term contexts (such as weakening) to apply to *all* terms in the substitution.

We can see this once we define substitution, which is no different to substitution in any well scoped syntax.

```idr
-- projection from the environment
indexEnv : TySub g d -> Elem a d -> Ty g
indexEnv (ConsTy a x y) Here = x
indexEnv (ConsTy a x y) (There t) = indexEnv y t

-- Traverse a type and substitute all the type variables
tySubst : TySub g d -> Ty d -> Ty g
tySubst sub (VarT x) = indexEnv sub x
tySubst sub (Forall s x) = Forall s $ tySubst (tyExt sub) x
tySubst sub (Mu s x) = Mu s $ tySubst (tyExt sub) x
tySubst sub (Imp x y) = Imp (tySubst sub x) (tySubst sub y)

-- extending the type environment
extTy : TySub g d -> TySub (s :: g) (s :: d)
```
Just as before, we rely on the extension operation `tyExt` when dealing with binders such as Forall or Mu. This operation weakens the context of each value in the substitution, thus requiring a full traversal of each value. Unlike with the substructural case, where we get this operation for free, defining it here requires us to also define renaming, and so we'll elide this definition for now (but it can be found in any of the reference implementations above).

What we're really interested in is term substitutions, so lets see what our new datatype looks like.

```idr
data TrmSub : (g : IxList String as) -> (sub : TySub as bs)
           -> (d : IxList String bs) -> Type where
  NilTrm : TrmSub g NilTy []
  -- an empty term substitution indexed by an empty type substitution

  ConsTrm : (trmVar : String) -> Term tyVars g
         -> TrmSub g sub d -> TrmSub g sub (trmVar::d)
  -- extend the term variable context by `trmVar` without affecting the type variables

  ConsTrmTy : (tyVar : String) -> (ty : Ty tyVars)
         -> TrmSub g sub d -> TrmSub g (ConsTy tyVar ty sub) (tyVar ::: d)
  -- extend both the term and type variable contexts by a type variable `tyVar`
  ```

This is... a lot, so let's break it down into components.

The first thing we notice is that the type of TrmSub is indexed by an instance of TySub - ie. in order to map a term context `g`, which is indexed by a type context `as`, into `d`, which is indexed by `bs`, we need to explain how to map `as` to `bs`. (Jules tells me that this means that we're probably dealing with a fibration).

The rules for NilTrm and ConsTrm are just as before, except that NilTrm is indexed by the empty type substitution, and ConsTrm is indexed by an arbitrary type substitution `sub`, which it does not interact with.

The interesting case is `ConsTrmTy` - it extends the term substitution by a *type* variable - which in turn means that it needs to extend the indexing type substitution `sub` with the same variable.

We can now define the action of substitution on terms, and just like with term contexts and term substitutions it will be indexed by a corresponding action of type substitutions on types. Unlike before, I'll work through the full definition here:

```idr
-- Lookup a term in an environment
lookupTrm : TrmSub d tySub g -> IxElem as g -> Term bs d
lookupTrm (ConsTrm a x y) Here = x
lookupTrm (ConsTrm b y z) (There x) = indexTrmEnv z x
lookupTrm (ConsTrmTy b y z) (ThereK x) = indexTrmEnv z x

-- Substitute a term
trmSubst : (tySub : TySub as bs) -> (trmSub : TrmSub g tySub d)
        -> Term bs d -> Term as g
trmSubst tySub trmSub (Var a x)
  = lookupTerm trmSub x
trmSubst tySub trmSub (Lam a tya x)
  = Lam a (tySubst tySub tya) (trmSubst tySub (extTrm trmSub) x)
trmSubst tySub trmSub (App x y)
  = App (trmSubst tySub trmSub x) (trmSubst tySub trmSub y)
trmSubst tySub trmSub (In ty trm)
  = In (tySubst (extTy tySub) ty) (trmSubst tySub trmSub trm)
trmSubst tySub trmSub (Out ty trm)
  = Out (tySubst (extTy tySub) ty) (trmSubst tySub trmSub trm)
trmSubst tySub trmSub (TLam k trm)
  = TLam k $ trmSubst (extTy tySub) (extTrmTy trmSub) trm
trmSubst tySub trmSub (TApp trm ty)
  = TApp (trmSubst tySub trmSub trm) (tySubst tySub ty)
```

Let's work through these one by one.

`Var` is unchanged beyond looking up the value in a more complicated environment.

`Lam` extends the term substitution just as in the simply typed case, but now performs an additional type substitution on its type annotation.

`App` is the same as with the STLC.

Both `In` and `Out` involve a binder in the datatype that we're taking the fixpoint over, so they require us to perform an extension of the type substitution, but they substitute the term itself as normal.

`TLam` is the most interesting case because it binds a type variable inside a term. This means that we need to extend the type substitution, as well as extend the term substitution by a new *type* variable. This is the reason why `TrmSub` has the shape it does.

`TApp` is not much more complicated than `App`, except that one of the things it substitutes is a term and the other is the type that we're applying to it.

Of note is the fact that term substitutions now have two extension operations:

```idr
-- extend the term substitution by a new term variable
extTrm : TrmSub g tySub d -> TrmSub (a :: g) tySub (a :: d)

-- extend the term substitution by a new *type* variable
extTrmTy : TrmSub g tySub d -> TrmSub (k ::: g) (extTy tySub) (k ::: d)
```

`extTrm` leaves the type substitution alone, but `extTrmTy` extends both the term substitution and the type substitution that it's indexed by with the same variable

And just as before, in order to implement `extTrm` and `extTrmTy` we would need to implement term renamings which are indexed by type renamings. This is standard, and is included in all of the earlier references.

### Towards substructural polymorphism

At this point we have two generalisations of the simply typed lambda calculus - one takes us into substructural types, the other into polymorphism. It would be really nice if we could combine the two, and define a substructural polymorphic language. Unfortunately though, it's *extremely* not obvious how to do this.

The usual answer provided in the literature is to keep the type contexts cartesian, and only make the term contexts linear. After all, what does it even *mean* for a type context to be linear?

While this works on paper, this would make the implementation quite cumbersome. What makes the implementation above as slick as it is, is the fact that the inductive structure of type-indexed-terms closely matches the inductive structure of the types indexing them. Letting types have implicitly shared contexts while enforcing a linear discipline on terms would not work so well (or at all?). And moreover, if one of the reasons for working substructurally is to avoid the expensive renaming operation, it would be a job-half-done if we eliminated term renamings while keeping renamings of types.

So while it's true that it doesn't quite make sense to talk about "linear type contexts", we could still talk about 'explicitly cartesian contexts', ie. Co-de-Bruijn-style contexts which allow copying and deleting of type variables so long as that's done explicitly, rather than implicitly through context-sharing.

But this still begs the question - what should the right definition of a polymorphic substructural lambda calculus even be?

Defining polymorphic covers would not be such a big deal - working by analogy with the other polymorphic operations, we can guess that a cover that handles term contexts will be indexed by a cover for type contexts.

But where things break down is when we need to define linear term substitutions, ie. this data-type:

```idr
data LinTrmSub : (g : IxList String as) -> (sub : LinTySub as bs)
              -> (d : IxList String bs) -> Type where
```

I have attempted this a few times now, but each time I reached a dead-end.

Jules suspects that this is because monoidal fibrations are much less obvious to work with than cartesian fibrations, but I have not figured out how to translate the extra data needed in the definition of a monoidal fibration into code.

So this is the problem that we're currently facing, and I'd be interested if anyone has some ideas here.

In the meantime, the blog series will explore the things that we *do* know how to do well. In the next few posts I'll show you how to work with covers more generally, how to define scope-checkers and type-checkers for substructural languages, and how to put all the pieces together into a full compiler pipeline using [Andre Videla's library for dependent compiler pipelines](https://cybercat.institute/2025/01/13/program-pipelines.idr/).