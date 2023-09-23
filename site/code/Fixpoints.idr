-- First-order


-- Second-order
infixr 1 :~>

-- Second-order Coyoneda
data Coyoneda  : (hf: (Type -> Type) -> Type -> Type) -> (f : Type -> Type) -> Type -> Type where
  Coyo : ({a : Type} -> g a -> f a) -> hf g a -> Coyoneda hf f a

-- Second Order Left Kan Extension - simplify the type...
data Lan  : (jf, hf: ((Type -> Type) -> Type -> Type)) -> (f : Type -> Type) -> (a: Type) -> Type  where
  MkLan : {jf : ((Type -> Type) -> Type -> Type)} -> ({a : Type} -> jf g a -> f a) -> hf g a -> Lan jf hf f a

-- Natural transformations
(:~>) : (Type -> Type) -> (Type -> Type) -> Type  
(:~>) f g = {a : Type} -> f a -> g a 

Algebra : (f : (Type -> Type) -> Type -> Type) -> (a : Type -> Type) -> Type
Algebra f a = f a :~> a

data Mu : (pattern: (Type -> Type) -> (Type -> Type)) -> Type -> Type where
  In : {a : Type} -> f (Mu f) a -> Mu f a

cata : Functor2 hf => (hf f :~> f) -> Mu hf :~> f
cata alg (In op) = alg (maph (cata alg) op)

mcata : Algebra (Coyoneda f) c -> Mu f :~> c
mcata alg (In op) = alg $ Coyo (mcata alg) op

--version with MAlgebra
--mcata : MAlgebra h f -> Mu f :~> c
--mcata alg (In op) = alg (mcata alg) op


-- Mu2 + Var 
data Free : (pattern: (Type -> Type) -> (Type -> Type)) -> (var: Type -> Type) -> (value: Type) -> Type where 
  Var : {a : Type} -> v a -> Free f v a 
  In2 : {a : Type} -> f (Free f v) a -> Free f v a

-- Coyoneda version
data Mu2 : (pattern: (Type -> Type) -> (Type -> Type)) -> (var: Type -> Type) -> (value: Type) -> Type where 
  Var : {a : Type} -> v a -> Mu2 f v a 
  In2 : {a : Type} -> Co f ((Mu2 f) v) a -> Mu2 f v a

{--

--}

-- 

{--
TODO: Show how Fix and HFix are special cases of IxFix

Introduce the idea of GenAlg
While higher-order functors are neatly subsumed by indexed functors, first order functors are a little bit more awkward.
Which is why I consider it valuable to treat them separately. If we have a library for indexed functors, there is no need to have a separate library for higher-order functors. But we'd still want a library for working with first-order ones.
This is because fundamentally, all of these concepts live in separate categories. So rather than try to embed each category into the ones with the most structure, it would be better if we could express these concepts generically, and instantiate them to whichever category suits us in the moment.

--}

-- relative fixpoint
--  data Mu : (k -> Type) -> (k -> Type) -> Type where
--    In : Lan j f (Mu j f) -> Mu j f
