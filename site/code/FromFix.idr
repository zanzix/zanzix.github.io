import Data.Fin 

-- TODO: Descriptions of nat transforms - how are they different to ornaments?
-- TODO: Link between fibrations and rel monads? Reindexing = functor from Context to Term. What is Pure/Bind? Fibs give you type-in-term subst?
-- TODO: N-ary descriptions: https://www.cl.cam.ac.uk/teaching/1718/L28/agda/generic.html
-- https://gist.github.com/plt-amy/92f538ee2976dc6670cb2f2e3b53d7e7

namespace ADT 

  data Semiring : Type -> Type where 
    Val : a -> Semiring a
    Zero : Semiring a 
    One : Semiring a
    Mult : Semiring a -> Semiring a -> Semiring a 
    Add : Semiring a -> Semiring a -> Semiring a 

  foldSemiring : (a -> a -> a) -> (a -> a -> a) -> a -> a -> Semiring a -> a 

  -- contrast to 

  foldList : (a -> a -> a) -> a -> List a -> a

  -- We can make this a little bit nicer by packaging up the algebra into a record, just as we've done in the first two posts
  record SemiringAlg (a : Type) where 
    constructor MkSemiring  
    zero : a 
    one : a 
    mult : a -> a -> a 
    add : a -> a -> a 

  -- we now have the more neat-looking
  eval : SemiringAlg a -> Semiring a -> a 
  eval alg (Val a) = a
  eval alg Zero = alg.Zero 
  eval alg One = alg.one
  eval alg (Mult e1 e2) = alg.mult (eval e1) (eval e2)
  eval alg (Add e1 e2) = alg.add (eval e1) (eval e2)  

  -- List, 
  -- Nat, 
  -- Min/Plus
  -- Types

  -- We can see that there is a lot of redundancy here - we need to define both the syntax, and the algebra. 
  -- At each stage, the algebra and the evaluator always mirror the syntax, so could we derive them for free?

  -- For starters, we can make the notion of algebra match the mathematical shape better
  Algebra : (Type -> Type) -> Type -> Type 
  Algebra f a = f a -> a 

  We can now see that both SemiringAlg and ListAlg are instances of algebra:

  ListAlg : Algebra List a 

  SemiringAlg : Algebra Semiring a 

  -- So we now have a unified notion of algebra, but can we get a unified evaluator?

  -- Naively we might try something like this:
  eval : Algebra f a -> f a -> a 
  eval alg fa = alg fa

  -- But the problem with this definition is that it's kind of redundant. All of the interesting work is happening inside of 'Algebra f a', and eval is reduced to mere function application. 
  -- We would like to be more modular than that, and to do that we will start by disentangling the recursive component of data-types. 

  -- Link the ring paper
namespace Fix 
  -- To start, let's define a fixpoint over functors.   
  data Fix : (Type -> Type) -> Type where 
    In : f (Fix f) -> Fix f

  -- it is named this way because it has a lot of resemblance to the fixpoint function

  fix : (a -> a) -> a 
  fix f = f (fix f)

  -- the only difference is that Fix is a type-level fixpoint, while `fix` is value-level
  
  -- We now want to rewrite our semiring and list data-types in a way that removes self reference, and turns it into a parameter
  -- Now, Semiring was already a parametrised type (Type -> Type), but let's simplify it first to illustrate the basic idea. 

  -- if we start with a semiring fixed to natural numbers,
  data Semiring' : Type 
    Val' : Nat -> Semiring' 
    Zero' : Semiring'
    One' : Semiring'
    Mult' : Semiring' -> Semiring' -> Semiring' 
    Add' : Semiring' -> Semiring'-> Semiring'
 
  -- then we can extract all instances of self-reference in the inputs, and replace them with an arbitrary parameter  
  data SemiringF' : Type -> Type where 
    ValF' : Nat -> SemiringF' a -- let's fix this for now 
    ZeroF' : SemiringF' a 
    OneF' : SemiringF' a
    MultF' : a -> a -> SemiringF' a 
    AddF' : a -> a -> SemiringF' a 

  -- Now Mu takes this data-type (Type -> Type) and gives us a Type. We can take our base functor and form a fixpoint over it. 
  Semiring : Type 
  Semiring = Mu SemiringF

  -- This gives us expressions 

  -- Now we can form our general evaluator, known as a catamorphisms. 
  cata : Functor f => Algebra f a -> Mu f -> a
  cata alg (In op) = alg (map (cata alg) op)

  cata : Algebra (Coyoneda f) a -> Mu (Coyoneda f) -> a
  cata alg (In op) = alg (map (cata alg) op)

  -- Ref: Universality of fold.

  -- Since the evaluator depends on our datatype being a functor, we need to define the functor instance. 
  
  Functor SemiringF where
    map = ?z

  -- and now we have our general evaluator. 

  -- We'd like to recover the original semiring, so we add a separate parameter for the contents

  data SemiringF : Type -> Type -> Type where 
    Val : a -> SemiringF a b -- let's fix this for now 
    Zero : SemiringF a b 
    One : SemiringF a b
    Mult : b -> b -> SemiringF a b 
    Add :  b -> b -> SemiringF a b 

  -- this works just as before.

  -- Using the same parametrisation idea, we can implement lists

  data ListF : Type -> Type where 
    Nil : ListF a b 
    Cons : a -> b -> ListF a b

  List : Type -> Type 
  List a = Mu (ListF a) 

  -- Technically SemiringF is now a bifunctor. The first parameter is used for the contents, and the second is used for the recursive position. 

  -- exev1, exev2

namespace Bif 
-- Bifunctor: https://www.cs.uoregon.edu/research/summerschool/summer22/lectures/Gibbons3notes.pdf
-- We can incorporate the bifunctor structure in a first-class way. 
  data Mu : (Type -> Type -> Type) -> Type -> Type where 
    In  : f a (Mu f a) -> Mu f a
    In' : f (Mu f a) a -> Mu f a

  -- Bifunctor instance for SemiringF 

  -- bifunctors get their own form of catamorphism 

  -- bcata : Algebra f a -> Mu f a -> a 

namespace Free 
  -- Bifunctors are a great way to talk about functors with first-class values, but what if we wanted to abstract away from values altogether?
  -- In other words, what if instead of working with expressions with an arbitrary - but fixed - carrier, we instead worked with expressions with *variables*, and only chose the carrier at runtime? 
  -- This is where free monads come in. While normally in functional programming, monads are used to talk about effects, in abstract algebra they are used for talking about expressions with variables.

  -- The datatype for free monads over a functor looks like this:
  data Free : (Type -> Type) -> Type -> Type where 
    Var : a -> Free f a
    In : f (Free f a) -> Free f a

  -- You can notice that this is exactly our earlier type Fix, but with variables.
  -- In fact, if we form "Free f Void" then we will get back Fix exactly

  --data Free : (Type -> Type) -> Type -> Type where 
  --  Var : Void -> Free f Void
  --  In : f (Free f Void) -> Free f Void 

  -- TODO: Fix <-> Free
  
  -- And vice versa, if we start with Fix and add a constant, we can get Free. 

  -- Using Free, we can define our type of semirings as before, but this time we drop the carrier 
  data SemiringF : Type -> Type where 
    ZeroF : SemiringF a 
    OneF : SemiringF a
    MultF : a -> a -> SemiringF a 
    AddF : a -> a -> SemiringF a 

  -- Leaves no longer contain values taken from 'a', they are now variables
  TermSemiring : Type -> Type
  TermSemiring a = Free SemiringF a

  -- And our evaluator now takes an extra parameter - it will first fill the variables with an environment, and then evaluate the algebra
  eval : (a -> b) -> (f b -> b) -> Free f a -> b
  -- eval  <- variables
  -- eval  <- looks like before
  
  -- We can recover our previous evaluator when a= Void, and we can also fill-in the id environment to get values

  -- We could also combine both values and variables
  data SemiringP : Type -> Type -> Type where 
    Val : a -> SemiringF a b 
    ZeroF : SemiringF a b
    OneF : SemiringF a b
    MultF : b -> b -> SemiringF a b 
    AddF  : b -> b -> SemiringF a b 
   
  -- TODO: Free monad over a bifunctor?
  -- However, these are not scoped, so if we want to use variables, the standard thing to do is to use error-handling

  -- This complicates issues, as we need to now evaluate into a monad, rather than directly. 
  -- This is in fact where the main topic of this post will come in, relative monads. 
  -- But before we delve into them, let's take a deeper dive into the structure of recursion schemes. 

namespace Coyoneda 
  -- So far we've been writing out a functor instance each time we introduced a new structure. 
  -- This'll get old very quickly, as we will look at a lot of data-types in a lot of categories.
  -- So this begs the question, if we're looking at free structures anyway, why not work with free functors as well?

  -- The free functor over a data-type is known as 'Coyoneda'. We don't need to think too much about what it means yet, just what it does. And what it does is act as glue code:
  data Coyoneda : (Type -> Type) -> Type -> Type where 
    Coyo : (a -> b) -> f a -> Coyoneda f b

  -- Using Coyoneda we can avoid needing a functor instance on our evaluators.
  -- Interestingly, it's enough to modify either our syntax, or our algebra

  -- for instance, weaving coyoneda into the syntax would look like this

  data Fix' : (Type -> Type) -> Type where 
    In : Coyoneda f (Fix' f) -> Fix' f 

  -- Or equivalently

  Fix'' : (Type -> Type) -> Type 
  Fix'' = Fix (Coyoneda f)

  -- But we can also modify the algebra

  Algebra' : (Type -> Type) -> Type -> Type 
  Algebra' = Coyoneda f a -> a 

  -- or equivalently 
  Algebra'' : (Type -> Type) -> Type -> Type 
  Algebra'' = Algebra (Coyoneda f) a 

  -- Modifying the algebra is known as the "Mendler Algebra" approach to recursion schemes. 

  mcata  : Algebra (Coyoneda f) a -> Fix f -> a 
  mcata' : Algebra f a -> Fix (Coyoneda f) -> a

  mcata' : Algebra f a -> Fix (Coyoneda f) -> a

  -- Unrolling the definitions will give us the more familiar form known as the mendler catamorphism

  --  mcata' : Fix f -> a 

  -- Modifying the syntax is a little bit less familiar in the fixpoints-of-functors literature, however if we apply the same idea to our free monad data-type 

  data Free' : (Type -> Type) -> Type -> Type where 
    Var : a -> Free' f a 
    In : Coyoneda f (Free' f a) -> Free' f a

  -- Or equivalently 

  Free' : (Type -> Type) -> Type -> Type
  Free' f a = Free (Coyoneda f) a 

  -- We can see that this is nothing other than the so-called 'freer monad':

  data Freer : (Type -> Type) -> Type -> Type where
    VarFr : v -> Freer f v 
    InFr : f x -> (x -> Freer f v) -> Freer f v

  --data Mu : (pattern : Type -> Type) -> (var: Type) -> Type where
  --  Var : v -> Mu f v 
  --  In : {f: Type -> Type} -> Coyoneda f (Mu f v) -> Mu f v
  
  -- and our evaluator for Free (Coyoneda f)

  eval : Algebra f a -> Free (Coyoneda f) a -> a 
  --cata : (a -> c) -> Algebra (Coyoneda f) c -> Mu f a -> c
  --cata g alg = go where 
  --go : Mu f a -> c
  --go (Var a) = g a
  --go (In $ Coyo continue action) = alg $ Coyo (go . continue) action

  -- is the same as the iterator for the freer monad 

  iter : Algebra f a -> Freer f a -> a 
--  catafr : (a -> c) -> Algebra (Coyoneda f) c -> Freer f a -> c
--  catafr g alg = go where 
--    go : Freer f a -> c
--    go (VarFr a) = g a
--    go (InFr action continue) = alg $ Coyo (go . continue) action 

-- TODO: Coyoneda for bifunctor, Freer Bifunctor

namespace Scoped
  -- Now, what did this digression have to do with well-scoped terms? Surprisingly, a lot. 
  -- To see that, let's start by looking at what well-scoped terms would look like 
  -- First we look at signatures. Whereas previously they corresponded to an endo-functor (Type -> Type), now they are Nat-indexed data-type (Nat -> Type)

  data SemiringSig : Nat -> Type where 
    Zero : SemiringF 0
    One : SemiringF 0
    Mult : SemiringF 2 
    Add : SemiringF 2

  -- Rather than representing our inputs directly, we count the number of inputs and represent them in the signature.
  -- Our type of fixpoints would then need to take in such a signature and give back a type

  data Fix : (Nat -> Type) -> Type where 
  -- But what should go in it? 

  -- Since Fix expects a natural number, we can no longer simply apply it to Fix f, which is a type. 

  -- In : f (Fix f) -> Fix f
  -- So we need to use a representation similar to the freer monad, where the outer `f` and inner `Fix f` are split:

  -- In : f n -> ?continuation -> Fix f 
  -- But what will go into the continuation?
  -- Under a first approximation, if `f n` corresponds to a signature with `n` positions, then we want some way to fill those positions. 
  -- We could start by placing the `n` values into a vector 
  
  -- Ref: Conor

  -- In : f n -> Vect n (Fix f) -> Fix f 
  -- In : {n : Nat} -> g n -> Vect n (Tm g m) -> Tm g m 
  -- Lets ignore for a moment that the resulting structure looks nothing like a monad, and try to work with it. 

  -- ex1, ex2, ex3

  -- Constructing terms of Fix isn't too bad. We have a tuple of a layer, and a vector of values that go inside. 
  -- It looks and feels a lot like Freer, except that Freer uses a continuation, while our Fix uses a vector of values.

  -- Now, we could follow the paper and implement a fold for our data-type. 
  -- It'll be quite involved:

  -- fold : Fix f -> a 
  -- foldVect : 
  
  -- Or we can notice that (Vect n a) is isomorphic to (Fin n -> a), on account of being what is known as a representable functor. 
  -- the resulting structure looks a *Lot* like Coyoneda, except with more structure and dependent types. In fact, it is only a slight generalisation 
namespace Lan 
  -- This data type is known as the left kan extension. We don't need to know the theory behind it, the main thing we need to know is that while Coyoneda was like a free functor, Lan is like a free functor constructed from a couple of other functors
  -- It takes in a J, and it takes in an F, and constructs the functor Lan j f 
  -- Functor instance 

  -- Lan-algebra : Lan j f a -> f a 

  -- What this gives us is a very powerful class of recursion schemes known as Kan Folds. 

  -- Coyo = Lan Id 
--   data Lan : (j: k -> Type) -> (f : k -> Type) -> Type -> Type where 
--     MkLan : (j a -> b) -> f a -> Lan j f b
  
-- traversal: https://gitlab.com/avidela/types-laboratory/-/blob/main/src/Optics/Lens.idr#L63

-- Fibred codes for Id = inductive types
-- fibred codes for Domain fibration = indexed containers
--  https://personal.cis.strath.ac.uk/fredrik.nordvall-forsberg/papers/fibred_lics2013.pdf

-- IR -> Fam(D) -> Fam(D)    https://lmcs.episciences.org/1154/pdf
 
namespace KanFix
  -- We now have 
  data Fix : (Nat -> Type) -> Type where 
    In : f n -> (Fin n -> Fix f) -> Fix f

  -- which is equivalent to 
  data Fix' : (Nat -> Type) -> Type where 
    In' : Lan Fin f (Fix' f) -> Fix' f 

  -- just as we've previously modified our notion of algebra to mendler algebra, we now have a kan algebra

  Algebra : (Type -> Type) -> Type -> Type 
  Algebra = Lan Fin f a -> a 

  -- And just as before, we get the corresponding fold

  kfold : KanAlgebra f c -> Fix f n -> c

  -- We can see that constructing the terms of Fix is not any more difficult than that of FixVect

  -- exs: ...
  data MonF : Nat -> Type where 
    Zero : MonF 0
    Mult : MonF 2 

  example : Op MonF 1
  example = Bind Mult (\i => case i of 
    FZ => FZ 
    FS FZ => FZ)

  -- TODO: Autobind
namespace Fin
  -- Finally, we can generalise Fix one more time. Just as before, we'd like to move from fixpoints of functors to monads. 
  -- So what kind of monad would underly Fix? 
  -- All we need to do is add an extra parameter, as well as a case for variables
  
  data Fin : Nat -> Type where 

  data Rel : (j, f : k -> Type) -> k -> Type where 
    Var : j n -> Rel j f n 
    Bind  : f n -> (j n -> Rel j f n) -> Rel j f n 
    Bind' : Lan j f (Rel j f n) -> Rel j f n 

  data Op : (Nat -> Type) -> Nat -> Type where 
    Var : Fin n -> Op f n 
    Bind : f n -> (Fin n -> Op f m) -> Op f m

  data Fix' : (j, f : k -> Type) -> Type where 
    In : Lan j f (Fix' f) -> Fix' j f 
  
  -- Just as before, we can see that Op f 0 = Fix f, where 0 now replaces 'Void' as the initial object

  -- From here, we can get our evaluator - we now have a more precise type of environmnets (Fin n -> c)
  cata : (Fin n -> c) -> KanAlgebra f c -> Op f n -> c
  
  -- the rest of the code stays the same
  -- in fact, we if we set J = id, then we can get back Free and the corresponding evaluator
   
  cata' : (Fin n -> c) -> KanAlgebra f c -> Op f n -> c


-- Modules: https://www.youtube.com/watch?v=ifwfYK0Hx0E

