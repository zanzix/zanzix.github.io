import Data.Fin 

data Lan : (j: k -> Type) -> (f : k -> Type) -> Type -> Type where 
  MkLan : {j: k -> Type} -> {a:k} -> (j a -> b) -> f a -> Lan j f b

data ArithF : Type -> Type where
  Val : Nat -> ArithF a 
  Add : a -> a -> ArithF a 

data ArithN : Nat -> Type where 
  VarN : Fin n -> ArithN n
  AddN : ArithN n -> ArithN n -> ArithN n 

data ArithN' : Nat -> Type -> Type where 
  VarN' : Fin n -> ArithN' n a
  AddN' : a -> a -> ArithN' n a 

data ArithN'' : (Nat -> Type) -> Nat -> Type where 
  VarN'' : Fin n -> ArithN'' p n
  AddN'' : p n -> p n -> ArithN'' p n 
  AddNL : p (S n) -> p (S n) -> ArithN'' p n -- maybe linear context?
  AddNL' : p n -> p n -> ArithN'' p (S (S n)) -- maybe linear context?

data ArithSig : Nat -> Nat -> Type where 
  ValS : Nat -> ArithSig n (S n)
  AddS : ArithSig (S (S n)) n
  VarS : Fin n -> ArithSig n n 

data LTy = Val' | Expr 

data ListNF : (LTy -> Type) -> LTy -> Type where 
  NilNF : ListNF f Expr
  ValNF : Nat -> ListNF f Val'
  ConsNF : ListNF f Val' -> ListNF f Expr -> ListNF f Expr 

data Ty = B | N 

-- BoolArith as (Type -> Type) vs (Ty -> Type)

namespace Fix
  data Mu : (pattern : Type -> Type) -> Type where 
    In : p (Mu p) -> Mu p 

  fix1 : Mu ArithF
  fix1 = In $ Add (In $ Val 6) (In $ Val 5)

namespace Free 
  data Free : (pattern: (Type -> Type)) -> (var: Type) -> Type where
  	Var : v -> Free p v
  	In : p (Free p v) -> Free p v 
  	InKl : p x -> (x -> Free p v) -> Free p v
  	InKl' : (x -> Free p v) -> p x -> Free p v
  	Enter : (Free p) (Free p v) -> Free p v
  	EnterKl : Free p x -> (x -> Free p v) -> Free p v

--    EnterFr : (x -> Free p n) -> (n -> Free p a) -> Free p a

  free1 : Free ArithF String 
  free1 = In (Add (Var "test") (Var "this"))

  free1' : Free ArithF String 
  free1' = InKl (Add "test" "this") Var 
  -- TODO: free1 <-> free1'. will this work? same algeba needs to do the same thing

  free1'' : Free ArithF String 
  free1'' = InKl (Add (Var "test") (Var "this")) id
  -- we can't use "id" in freest! It must be Pure

  freen : Free ArithF (Fin 2)
  freen = In (Add (Var FZ) (Var (FS FZ)))

  freen' : Free ArithF (Fin 2)
  freen' = InKl ?z ?y
  -- TODO: freen <-> freen', should do the same as above but not partial

  free2 : Free ArithF String 
  free2 = In (Add (In (Add (Var "test") (Var "this"))) (Var "and_this"))

  -- Ooof, will this work?
  free2' : Free ArithF String
  free2' = InKl (Add "test" "this") (\s => (InKl (Add s "and_this") Var))

  free2'' : Free ArithF String 
  free2'' = 
    let ex = InKl (Add (InKl (Add "test" "this") Var) (Var "and this")) Var
    in EnterKl ex id

    -- can formulate Join using EnterKl. But using inKl?

  free2''' : Free ArithF String 
  free2''' = InKl (Add (InKl (Add "test" "this") Var) (Var "and this")) id

  free2'''' : Free ArithF String 
  free2'''' = let ex1 = InKl {p=ArithF} (Add (InKl {p=ArithF} (Add "test" "this") ?v2) ?v) in  ?vs
  -- (Var "and this")

  free3 : Free ArithF String 
  free3 = In (Add (In (Add (Var "test") (Var "this"))) (Var "and_this"))

    --InKl' ?z1 (InKl' Var ?ys)
    -- (Add "test" "this")  ?z0 
  -- (Add "test" "this") ?z0




--  free2' = InKl (Add (InKl (Add "test" "this") Var) ?v3) Var
  


  -- TODO: more layers for coyoneda version
  
  -- todo: partial eval

  -- todo: full eval? but how does substitution interact with Fin n?
  -- limitations? brittleness?

namespace Op
  data Operad : (Type -> Type) -> (Nat -> Type) where 
    Var : Fin n -> Operad f n
    In  : f (Operad f n) -> Operad f n
    InB : f (Operad f (S n)) -> Operad f n
    InB2 : f (Operad f (S (S n))) -> Operad f n
    LetBind : f a -> Operad f (S n) -> Operad f n
    OutB : f (Operad f n) -> Operad f (S n)
    OutB2 : f (Operad f n) -> Operad f (S (S n))

  op1 : Operad ArithF 2
  op1 = In (Add (Var FZ) (Var $ FS FZ))

  -- looks wrong, bind a variable to a layer?
  op2 : Operad ArithF 1 
  op2 = InB (Add (Var FZ) (Var $ FS FZ))

  -- bind both? will this work?
  op3 : Operad ArithF 0 
  op3 = InB2 (Add (Var FZ) (Var $ FS FZ))
  
  -- try with OutB and OutB2 - request a variable from the environment?
    
  -- what should rel-bind be?

namespace IFix
  data IxMu : ((k -> Type) -> (l -> Type)) -> (l -> Type) where 
    In : f (IxMu f) v -> IxMu f v

  -- TODO: IFix ArithNF

  -- IFix : (k -> Type) -> (k -> Type)
  -- vs 
  -- Rel  : (k -> Type) && (k -> Type)

  -- TODO: eval : IFix Operad -> Nat ?

namespace RFix 
  data RFix : (k -> Type) -> l -> Type where
  -- Operad as RFix?

namespace Rel 
  -- The free relative monad over j
  data Freest : {k : Type} -> (k -> Type) -> (k -> Type) -> k -> Type where
    Var  : {j : k -> Type} -> j v -> Freest j f v
    In : {j : k -> Type} -> Lan j f (Freest j f v) -> Freest j f v
    InKl  : {j : k -> Type} -> f x -> (j x -> Freest j f a) -> Freest j f a

  data Freest' : {k : Type} -> (k -> Type) -> (k -> Type -> Type) -> k -> Type where
    Var'  : {j : k -> Type} -> j v -> Freest' j f v
    InKl'  : {j : k -> Type} -> {f : k -> Type -> Type} -> f x b -> (j x -> Freest' j f a) -> Freest' j f a

  
  Ariths : Type 
  Ariths = Freest' Fin ArithN' 2

  
  fr1 : Freest (\a=>a) ArithF String 
  fr1 = In $ MkLan Var (Add "test" "this") 
  -- this is different to Free, we don't use 'Var' over the strings. does it work?
  -- feels wrong... needs to be the recursor. can i do recursive expressions this way?


  fr1' : Freest (\a=>a) ArithF String
  fr1' = InKl (Add "test" "this") Var 


  -- this is wrong - it expects a recursive type! need to remove recursor
  fr1n : Freest Fin ArithN 2 
  fr1n = InKl (AddN ?xf ?yf) Var 

  -- i think totally broken? inner type can be anything
  fr1n' : Freest' Fin ArithN' 2
  fr1n' = InKl' (AddN' "why" "strings") Var'

  -- ok looks correct - recursor replaced with Fin? Now it has same shape as fr1, with variables inside
  fr1n'' : Freest Fin (ArithN'' Fin) 2 
  fr1n'' = InKl (AddN'' FZ (FS FZ)) Var

  -- erm, wrong? where would the two variables come from?
  fr1n''' : Freest Fin (ArithN'' Fin) 0 
  fr1n''' = InKl (AddNL FZ FZ) Var

  -- ???? no idea what im trying to do here, i think it's broken.
  fr1n'''' : Freest Fin (ArithN'' Fin) 2
  fr1n'''' = InKl (AddNL' (FS FZ) FZ) ?vs

  fr2 : Freest Fin ArithN 2
  fr2 = In $ MkLan Var (AddN (VarN FZ) ((VarN (FS FZ))))

  fr2' : Freest Fin ArithN 2 
  fr2' = InKl (AddN (VarN FZ) ((VarN (FS FZ)))) Var

  
  add : Fin n -> Fin n -> Freest Fin (ArithN'' Fin) n
  add n1 n2 = InKl (AddN'' n1 n2) Var
  -- InKl (AddN'' s FZ) Var

  -- Will this work? Is there a different way? can I bind two vars?
  fr2n : Freest Fin (ArithN'' Fin) 2 
  fr2n = InKl (AddN'' FZ (FS FZ)) (\s => add s FZ)
  -- can I use smart constructors for both?

  
--  In (Add (In (Add (Var "test") (Var "this"))) (Var "and_this"))
--  free2' : Freest Fin ArithN 2
--  free2' = InKl (Add "test" "this") (\s => (InKl (Add s "and_this") Var))

  -- TODO: Example with more complicated Var?
  -- test with permutations!

  -- TODO: ListNF as rfix?

  --  InFst  : {j : k -> Type} -> f x -> (j x -> g a) -> FreeLanF j f g a

{-}
mcata : (Fin n -> c) -> Algebra f c -> Operad f n -> c
mcata g alg = go where
go : Free f a -> c
go (Var a) = g a
go (In $ fs) = alg $ (mcata g alg) fs




















{--
Very broadly, the purpose of this blog series is to introduce the multicategory perspective. In a sense, multicategories generalise both categories and data types. Because of this, the series will be split into three parts:
Data types - applying category theory to functional programming to get generic tools for working with data types
Categories - treating categories themselves as data types and applying our machinery from part 1 to do category theory 
Multicategories - using the tools from part 1 and part 2 to work with type theories


This post will introduce the core tools that we will use throughout the series. Everything else will be some variation of this. At times it might be non-intuitive, but I encourage you to experiment with the code. 

'Simple but not easy'. 

Some refs:
  Universality of fold: https://www.cs.nott.ac.uk/~pszgmh/fold.pdf

--}
-- from functor to operad



-- compare to fixpoint of function?

-- cata


-- eval 

-- TODO: show translation
-- Mu f = Free f Void
-- Free f a = Mu (f + Const)

{-- However, this assumes that our function (a -> c) is total. 
If we use a type like String to define our variables, this will take a long time. 
We could use a disjoint union of variables
data Var : X | Y | Z
But then this would lock us into a fixed number of variables, while we want to be able to bind new 

So we need a representation of a finite set of N elements
we can use an indexed type for this

data Fin n : Nat -> Type 
  FZ .. 
  FS ..

Then we could change Var to take this finite set of variables, and build a term out of them
    Var : Fin n -> Operad f n a

Then our type becomes indexed by variables. We take an endofunctor (Type -> Type) and get an indexed type (Nat -> Type -> Type)

TODO: (Nat -> Type -> Type) or (Nat -> Type) ?
data Operad : (Type -> Type) -> (Nat -> Type -> Type) where 
  Var : Fin n -> Operad f n a
  -- TODO: Which of these to use?
  LetF : f (Operad f (S n) a) -> Operad f n a
  LetBind : f a -> Operad f (S n) a -> Operad f n a

When talking about freeness, it's important to specify what we are free over. 
We'll call this the free operad over endofunctors. Later on, we'll meet the free operad over a signature. 

Our new evaluator then becomes
TODO: non-mendler version... im just showing off.
mcata : (Fin n -> c) -> Algebra f c -> Operad f n -> c
mcata g alg = go where
go : Free f a -> c
go (Var a) = g a
go (In $ fs) = alg $ (mcata g alg) fs

TODO: is this a relative monad? Double check the formulation.

TODO: From Operad to Free Monad and back?
In a sense, an operad is a reified version of a monad. If Monads generalise Lists, then Operads generalise Vectors

--}

{-- Fixpoints all the way up

Last post we've introduced several related constructions. Fixpoints of functors, free monads over functors, operads over functors. It's a proliferation of datatypes of datatypes. 
In this blog post we will see how all of these are actually the same concept. 

Fix

Coyo

HFix
HCoyo 

IxFix 
IxCoyo 

It would be nice if we could formulate a uniform definition of all of the above. 
While expressing a type of algebras parametric over some underlying category is straightforward
GenAlg : ... 
Which lets us recover our previous definitions of algebra
Alg = GenAlg Idr
HAlg = GenAlg Nat 
IxAlg = GenAlg IxNat 
(TODO: Try mendler version?)
It's much harder to generalise the remaining components of the fixpoint definition
cata : ... 
Becuase we have data-types, which necessarily have Type in their codomain, limiting our expressivity. 
It could still be possible to do a deep encoding of the idea, as was done in Phil Freeman's blog, using generalised functors
But a strong emphasis of this series is that all of our top-level machinery needs to be first-class, ie our language's type system needs to enable us to be able to write the kinds of programs that we want.
Nevertheless, we will go back to this point once we apply our tools to the 


-- Constrained/Restricted Monads

There are a lot of possible avenues of exploration here. What structure do these subcategories have? What sort of adjunctions are possible between them? What structure is preserved by (co)products, etc? What would f-algebras in them look like?

If we have Fix, we can have free. And if we have Free, we can have Fix one level up. So the cycle can continue as needed. 
  It's fixpoints all the way up!

--}

{-- Mendler Algebras and Relative Monads
Last post we've looked at how fixpoints of functors in different categories give us a unified notion of syntax. 
It's a useful conceptual picture, and it teaches us a very valuable skill of being able to jump between categories. 
But it is not the only perspective on this. There is another generalisation that we could use, one that takes the concept of a monad as primitive. 

In the previous post we've used Coyoneda as a convenient way to avoid writing boilerplate code. 

-- TODO: mcata

-- TODO: meval

-- TODO: relative eval

Then show how we can recover meval as relative monad to the identity

The reason why this perspective is valuable is that it avoids jumping between levels.
Previously, each of cata, eval, reval lived in separate categories
But now they live in the same place. A lot of the time we want to be able to add variables to a language without redoing the infrastructure, and this allows us to do so
Still, it's a matter of taste, and some prefer the simplicity of the fixpoint perspective.

In the next post we will get some hands-on experience working with relative monads by looking at a prototypical example, restricted monads. As functional programmers know, sets do not form a monad over types because they require an equality constraint.
However, they form a relative moad. 
In the post after that, it will be time to have The Talk that all budding category theorists have: where monads come from. 

--}