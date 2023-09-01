{-- Multi-sorted algebraic theories 

should I put this into Operad? It's not that much more difficult
But maybe I'll want to do it separately and include everything we've derived since the Operad chapter
Imo the point of the Operad chapter is to show a smooth progression from fixpoints to operads
whereas this breaks the progression a bit, so imo deserves its own place

--}

data Ty = M | S 

data Term : List Ty -> Ty -> Type where
  Var : {a : Ty} -> {g : List Ty} -> Elem a g -> Term g a
  -- LetVal
  Unit : Term g M
  Mult : Term g M -> Term g M -> Term g M 
  Act : Term g M -> Term g S -> Term g S 
  -- TODO: are there more operations?

Val : Ty -> Type 
Val M = Nat 
Val S = Nat 

{--
We can see that our language is starting to look like our earlier simply typed lambda calculus. The main difference is that while we have some fixed set of types, we don't have type connectives.
This is the main distinction between a multi-sorted algebraic theory and a type theory. 

--}