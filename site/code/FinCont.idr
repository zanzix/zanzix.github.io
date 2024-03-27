data FibLan : (j: k -> Type) -> (fib : s -> k) -> Type -> Type where
  MkFibLan : (  a ** (j (fib a) -> b)) -> FibLan j fib b

namespace Original
-- Finitary Container, contains a set of operations and their arity
  record Signature where 
    constructor MkSig 
    Symbols : Type 
    Arity : Symbols -> Nat 

  -- Interpretation of a signature as an endofunctor
  Ev : Signature -> (Type -> Type) 
  Ev (MkSig s ar) t = (s ** Vect (ar s) t)

  -- Fixpoint of a signature
  data Mu : Signature -> Type where 
    In : (Ev s) (Mu s) -> Mu s 

  -- F-Algebra over a signature
  Algebra : (s : Signature) -> (Type -> Type)
  Algebra f a = (Ev f) a -> a 

  fold : Algebra f a -> Mu f -> a 
  fold f (In {s} x) = ?green_slime

  mapFold : Algebra f a -> Vect n (Mu f) -> Vect n a 
  mapFold f Nil = Nil 
  mapFold f (x :: xs) = fold f x :: mapFold f xs 

  -- Operations for arithmetic
  data ArithSymbols : Type where 
    Lit : Nat -> ArithSymbols
    Add : ArithSymbols

  -- Construct a signature by giving an arity to each operation
  ArithSig : Signature 
  ArithSig = MkSig ArithSymbols $ \ar => case ar of 
    Lit n => 0
    Add => 2 

  ex0 : Mu ArithSig 
  ex0 = In (Lit 42 ** Nil)

  ArithAlg : Algebra ArithSig Nat 
  ArithAlg (Lit n ** Nil) = n 
  ArithAlg (Add ** n1 :: n2 :: Nil) = n1 + n2 

  vec : (n : Nat ** Vect n Int)
  vec = (2 ** [3, 4])

  bpair : (n : Nat ** Vect n Bool)
  bpair = (2 ** [False, True])

  arpair : Signature -> Type
  arpair (MkSig s ar) = (s ** Vect (ar s) Nat)

namespace Vect 
  Sig : Type -> Type 
  Sig s  = (s : Type ** s -> Nat) 
  
  -- Interpretation of a signature as an endofunctor
  Ev : (s : Type ** s -> Nat) -> (Type -> Type) 
  Ev (s ** ar) t = (s ** Vect (ar s) t)

  -- explain relationship between Sig and functors (Type -> Type)
  data Mu : (s : Type ** s -> Nat) -> Type where 
    In : {s : Type} -> {ar : s -> Nat} -> 
      (s' ** Vect (ar s') (Mu (s ** ar))) -> Mu (s ** ar)

  Algebra : (s : Type ** s -> Nat) -> (Type -> Type)
  Algebra (s ** ar) a = ((s ** Vect (ar s) a)) -> a 

  mutual
    fold : Algebra f a -> Mu f -> a 
    fold f (In (s ** v)) = f (s ** mapFold f v)

    mapFold : Algebra f a -> Vect n (Mu f) -> Vect n a 
    mapFold f Nil = Nil 
    mapFold f (x :: xs) = fold f x :: mapFold f xs 

  public export
  data ArithSym : Type where 
    Lit : Nat -> ArithSym
    Add : ArithSym
    Zero : ArithSym

  public export
  ArithSig : (s : Type ** s -> Nat) 
  ArithSig = (ArithSym ** (\ar => case ar of 
    Lit n => 0
    Add => 2
    Zero => 0))

  ex0 : Mu ArithSig 
  ex0 = In (Lit 42 ** Nil)

  ex1 : Mu ArithSig 
  ex1 = In (Add ** [In (Lit 40 ** Nil), In (Lit 10 ** Nil)])
    
  ArithAlg : Algebra ArithSig Nat 
  ArithAlg (Lit n ** Nil) = n 
  ArithAlg (Add ** n1 :: n2 :: Nil) = n1 + n2 
  ArithAlg (Zero ** Nil) = 0 

namespace Fin
  data Mu : (s : Type ** s -> Nat) -> Type where 
    In : (s' ** (Fin (ar s') -> Mu (s ** ar))) -> Mu (s ** ar)

  -- Algebra for a finitary container
  Algebra : (s : Type ** s -> Nat) -> (Type -> Type)
  Algebra (s ** ar) a = (s ** (Fin (ar s) -> a)) -> a 

  -- Fold over a finitary container
  fold : Algebra (s ** ar) a -> Mu (s ** ar) -> a 
  fold alg (In  (s ** env)) = alg (s ** (fold alg) . env)

namespace Coyo
  data Mu : (s : Type ** s -> Nat) -> Type where 
    In : FibLan Fin ar (Mu (s ** ar)) -> Mu (s ** ar)

  Algebra : (s : Type ** s -> Nat) -> (Type -> Type)
  Algebra (s ** ar) a = FibLan Fin ar a -> a

  fold : Algebra (s ** ar) a -> Mu (s ** ar) -> a 
  fold alg (In (MkFibLan (s' ** env))) = alg $ MkFibLan (s' ** (fold alg) . env) 
