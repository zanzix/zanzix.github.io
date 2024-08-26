Implementing LetRec with Free Cyclic Monads

In the last blog post, we've looked at let binders and multi let binders.
In this blog post, let's look at cyclic terms and let rec. 

First of all, what is a cyclic term. Just as the name suggests, it is a term with a *cycle* or a self reference. We'll start by looking at a concrete example, and then generalise. 

Cyclic lists, circuits

We'd like to formulate a generic definition of 'cyclic monad over an endofunctor'. 
Ie we would like to be able to specify loops in our data type. 

We will start by adding a fixpoint operation to our freest monad data type. 

```idris
namespace Mu
  data Op : (Nat -> Type) -> Nat -> Type where 
    Var : Fin n -> Op f n 
    (>>=) : {n : Nat} -> f n -> (Fin n -> Op f m) -> Op f m
    Mu  : Op f (S m) -> Op f m 
```

Mu is a least fixpoint, and it's name is not a coincidence. The constructor Mu takes a term with a free variable, and binds it - to itself. In a representation that uses strings, it would look like this: TODO, add string version

In order to evaluate cyclic terms, we need to use codata. 

```idris
  eval : KAlgebra f a -> Op f n -> a 
```

This lets us unfold a potentially infinite list. 

Now, to go from Mu to LetRec, we introduce the LetRec construct

```idris
namespace LetRec
  data Op : (Nat -> Type) -> Nat -> Type where 
    Var : Fin n -> Op f n 
    (>>=) : {n : Nat} -> f n -> (Fin n -> Op f m) -> Op f m
    Mu  : Op f (S m) -> Op f m 
    LetRec : Op f (S m) -> Op f (S m) -> Op f m
```

Notice the similarity to the let binder:
  Let : Op f m -> Op f (S m) -> Op f m
  LetRec : Op f (S m) -> Op f (S m) -> Op f m

Whereas a let binder introduces a binder in the second expression, the letrec binder introduces a binder in both expressions. ie we declare a variable and bind it to an expression that can refer to itself. 

Perhaps unsurprisingly, the letrec binder does not add any extra expressivity, and can be eliminated. Just as before, this corresponds to substitution, aka a form of cut elimination. This time for cyclic terms. 

TODO: substitution

LetRec2 
Having defined a letrec for a single variable, we would like to define it for multiple. It can be quite jarring to jump to the full thing, so let's look at how to bind two expressions

First we will need to define an analogue of Mu. Mu introduces an expression with a single free variable that binds to itself. So Mu2 will introduce two expressions with two free variables each, which bind them to each other. 

  Mu2  : Spec (S (S m)) -> Spec (S (S m)) -> Spec m 

Similarly, LetRec2 will bind two new variables to two expressions with two free variables each, and then assign that to an expression with two free variables 

  LetRec2 : Vect 2 (Spec (S (S m))) -> Spec (S (S m)) -> Spec m

All in all, we can define substitution just as before 

### Multi LetRec
Finally, let's look at the fully fledged version. 
For MultiMu, We now need to define a vector of variables of size `n`, each of which has `n` free variables. 

  MultiMu : Vect n (Spec (n + m)) -> Spec m 

And MultiLetRec assigns this vector to an expression 
  LetRec : {n : Nat} -> Vect n (Spec (n + m)) -> Spec (n + m) -> Spec m 

Substitution can be generalised just as before:

## Conclusion
We've now defined a calculus of cyclic, mutually recursive terms. All of this development can be generalised to multi sorted algebraic theories, which we will look at next.

### Multi sorted cyclic terms
In a previous blog post, we've looked at cyclic monads, which modelled cyclic algebraic theories. In this blog post we will see how to generalise that to the multi sorted case. 