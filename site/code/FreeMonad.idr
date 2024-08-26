data SemiringLayer : Type -> Type where 
  One : SemiringLayer expression
  Zero : SemiringLayer expression
  Mult : expression -> expression -> SemiringLayer expression
  Add : expression -> expression -> SemiringLayer expression

data Freer : (layer : Type -> Type) -> (var : Type) -> Type where 
  Pure : var -> Freer layer var  
  (>>=) : f a -> (a -> Freer f var) -> Freer f var 

exOne : Freer SemiringLayer Nat 
exOne = do 
  pure False
