-- Our goal is to show the common machinery between three different fixpoints:
-- Endofunctors, the universe of regular functors, and (simple) IR codes

namespace Endo 
  -- The "universe" of endofunctors, ie any type (Type -> Type)
  Endo : Type 
  Endo = Type -> Type 

  -- the interpretation is identity, ie we interpret functors as-is
  Ev : Nt (Type -> Type)
  Ev = id

  -- Standard version of the fixpoint
  data Mu : Endo -> Type where 
    In : (id f) (Mu f) -> Mu f 
  -- == In : f (Mu f) -> Mu f 

  -- Signature for Natural Numbers
  NatF : Endo 
  NatF a = Either Unit a

  zero : Mu NatF 
  zero = In (Left ())

  one : Mu NatF -> Mu NatF 
  one n = In (Right n)

  -- General version: Mu is a special case of Fix
  Mu' : Endo -> Type 
  Mu' = Fix {u = Endo} Ev

  zero' : Mu' NatF
  zero' = In (Left ())

  one' : Mu' NatF -> Mu' NatF
  one' n = In (Right n)

  -- Bonus: We can re-use native datatypes, and NatF = Maybe
  NatF'' : Endo 
  NatF'' a = Maybe a
  
  zero'' : Mu' Maybe 
  zero'' = In Nothing 

  one'' : Mu' Maybe -> Mu' Maybe 
  one'' n = In (Just n)  

namespace Regular
  -- the universe of regular functors
  data Regular : Type where
    Var : Regular
    Zero : Regular
    Unit : Regular
    Plus  : Regular -> Regular -> Regular
    Times : Regular -> Regular -> Regular

  -- Interpetation of regular functors
  Ev : Nt Regular
  Ev Var ty = ty
  Ev Zero ty = Void
  Ev Unit ty = Unit
  Ev (Plus x y) ty = Either (Ev x ty) (Ev y ty)
  Ev (Times x y) ty = Pair (Ev x ty) (Ev y ty)

  Ev' : Nt'' Regular 
  Ev' Var ty = ty
  Ev' Zero ty = Void
  Ev' Unit ty = Unit
  Ev' (Plus x y) ty = Either (Ev' x ty) (Ev' y ty)
  Ev' (Times x y) ty = Pair (Ev' x ty) (Ev' y ty)
  
  -- Fixpoint of a regular functor
  data Mu : Regular -> Type where 
    In : (Ev desc) (Mu desc) -> Mu desc
  
  -- Natural numbers
  NatF : Regular 
  NatF = Plus Unit Var

  zero : Mu NatF 
  zero = In (Left ())

  one : Mu NatF -> Mu NatF 
  one n = In (Right n)

  -- Mu is a special case of Fix
  Mu' : Regular -> Type 
  Mu' = Fix {u = Regular} Ev

  zero' : Mu' NatF 
  zero' = In (Left ())

  one' : Mu' NatF -> Mu' NatF 
  one' n = In (Right n)

namespace Desc 
  -- Universe of descriptions/IR codes
  data Desc : Type where
    One : Desc 
    Sig : (s : Type) -> (s -> Desc) -> Desc 
    Ind : Desc -> Desc 

  -- Interpetation of descriptions
  Ev : Nt Desc
  Ev One x = Unit
  Ev (Sig s p) x = (s' : s ** Ev (p s') x)
  Ev (Ind d) x = (x, Ev d x) 

  -- Fixpoint of descriptions, aka Data
  data Mu : Desc -> Type where 
    In : (Ev desc) (Mu desc) -> Mu desc
  
  -- Nat
  NatF : Desc
  NatF = Sig Bool (\case 
    False => One
    True => Ind One) 

  zero : Mu NatF
  zero = In (False ** ())

  one : Mu NatF -> Mu NatF 
  one n = In (True ** (n, ()))

  -- The general version, Mu is also a special case of Fix
  Mu' : Desc -> Type 
  Mu' = Fix {u = Desc} Ev

  zero' : Mu' NatF 
  zero' = In (False ** ())

  suc' : Mu' NatF -> Mu' NatF 
  suc' n = In (True ** (n, ()))  

