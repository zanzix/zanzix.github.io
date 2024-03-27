namespace Indexed 
--  data IxFix : ((Nat -> Type) -> Nat -> Type) -> Nat -> Type where 

  IxType : Type -> Type 
  IxType a = a -> Type 

  data IxFix : (IxType Nat -> IxType Nat) -> IxType Nat where 
  -- compare type to Fix

  -- We split our operations into those that affect the variables, and those that do not
  -- ie we're putting Op and Semiring on the same level
  data SemiringIx : IxType Nat -> IxType Nat where 
    Zero : SemiringIx f n 
    One : SemiringIx f n 
    Mult : f n -> f n -> SemiringIx f n
    Add : f n -> f n -> SemiringIx f n

    Var : Fin n -> SemiringIx f n 
    Bind : f n -> (Fin n -> SemiringIx f m) -> SemiringIx f m
    Let : f (S n) -> SemiringIx f n -> SemiringIx f n
    -- TODO: How to sensibly split SemiringIx and Op?
    
--  data SemiringIx' : (Nat -> Type) -> List Type -> Type -> Type where 
--    Add' : SemiringIx' f [f n, f n] (f n)

namespace IxFree 
  data IxFree : (IxType Nat -> IxType Nat) -> IxType Nat -> IxType Nat where
    Var : {a : k} -> f a -> FreeI ix f a
    Bind : {a : k} -> ix (FreeI ix f) a -> FreeI ix f a
--    In2C : {a : k} -> (g ~> FreeCoyo w f) -> w g a -> FreeCoyo w f a 

  -- TODO: SemiringIx as IxFree?

namespace ListSig
  data Op : (List a -> a -> Type) -> List a -> a -> Type where 

  data SemiringF : List a -> a -> Type where 
    Zero : SemiringF [] a
    One : SemiringF [] a 
    Mult : SemiringF [a, a] a  
    Add : SemiringF [a, a] a

  data SemiringF' : List a -> a -> Type where 
    Zero' : SemiringF' g a
    One' : SemiringF' g a 
    Mult' : SemiringF' (a::a::g) a  
    Add' : SemiringF' (a::a::g) a