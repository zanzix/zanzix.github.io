{-- Compiling to typed cartesian bicategories Part I --}

-- A type of edges for a graph, parametrised by a type of vertices
Graph : Type -> Type 
Graph obj = obj -> obj -> Type 

-- The category of Idris types and functions
Idr : Graph Type 
Idr a b = a -> b 

-- Kleisli category over some monad m
Kleisli : (Type -> Type) -> Type -> Type -> Type 
Kleisli m a b = a -> m b 

namespace TypeCat 
  -- Free category over Idris types and functions
  data Free : (g : Type -> Type -> Type) -> (a : Type) -> (b : Type) -> Type where 
    Id : Free g a a 
    Comp : g b c -> Free g a b -> Free g a c 

namespace Cat
  -- A more general free category over some type of objects
  data Free : {obj : Type} -> Graph obj -> Graph obj where 
    Id : {a : obj} -> Free g a a 
    Comp : {a, b, c : obj} -> g b c -> Free g a b -> Free g a c 

  -- A basic evaluator
  eval : Free Idr a b -> Idr a b 
  eval Id = id 
  eval (Comp f g) = f . (eval g)

  -- example term 
  ex1 : Free Idr Nat Nat 
  ex1 = Comp (+1) Id

namespace BCC 
  -- Free Bicartesian Closed Category over Idris types and functions
  data FreeBCC : Graph Type -> Graph Type where
    -- Embedding a primitive is now a separate operations from 'Comp' 
    Prim : k a b -> FreeBCC k a b
    -- Identity arrow: a → a
    Id : {a : Type} -> FreeBCC p a a 
    -- Composition of arrows: (b → c) → (a → b) → (a → c)
    Comp : {a, b, c : Type} -> FreeBCC k b c -> FreeBCC k a b -> FreeBCC k a c
    -- Product introduction: (a → b) → (a → c) → (a → (b * c))
    ProdI : {a, b, c : Type} -> FreeBCC k a b -> FreeBCC k a c -> FreeBCC k a (b, c) 
    -- First projection: (a * b) → a
    Fst : {a, b : Type} -> FreeBCC k (Pair a b) a
    -- Second projection: (a * b) → b
    Snd : {a, b : Type} -> FreeBCC k (Pair a b) b
    -- Coproduct introduction: (b → a) → (c → a) → (b + c → a)
    CoprodI : {a, b, c : Type} -> FreeBCC k b a -> FreeBCC k c a -> FreeBCC k (Either b c) a 
    -- Left injection: a → (a + b)
    InL : {a, b : Type} -> FreeBCC k a (Either a b)
    -- Right injection: b → (a + b)
    InR : {a, b : Type} -> FreeBCC k b (Either a b)
    -- Exponential elimination: 
    Apply : {a, b : Type} -> FreeBCC k ((a -> b), a) b
    -- Currying: (a * b → c) → (a → (b ⇨ c)) 
    Curry : {a, b, c : Type} -> FreeBCC k (a, b) c -> FreeBCC k a (b -> c) 
    -- Uncurrying: (a → (b ⇨ c)) → (a * b → c) 
    Uncurry : {a, b, c : Type} -> FreeBCC k a (b -> c) -> FreeBCC k (a, b) c
  
  -- We can evaluate the free category over Idris functions
  eval : FreeBCC Idr a b -> Idr a b 
  eval (Prim f) = f
  eval Id = id 
  eval (Comp f g) = (eval f) . (eval g) 
  eval (ProdI f g) = \c => ((eval f) c, (eval g) c)   
  eval Fst = fst
  eval Snd = snd
  eval (CoprodI f g) = \c => case c of 
    Left l => (eval f) l 
    Right r => (eval g) r 
  eval InL = Left 
  eval InR = Right 
  eval Apply = uncurry apply
  eval (Curry f) = curry $ eval f 
  eval (Uncurry f) = uncurry $ eval f  
  
  record Category (g: Graph Type) where 
    constructor MkCat 
    id : {a: Type} -> g a a 
    comp : {a, b, c : Type} -> g b c -> g a b -> g a c
    prod : {a, b, c : Type} -> g c a -> g c b -> g c (a, b)
    fst : {a, b :Type} -> g (a, b) a 
    snd : {a, b :Type} -> g (a, b) b
    coprod : {a, b, c : Type} -> g a c -> g b c -> g (Either a b) c
    left : {a, b : Type} -> g a (Either a b)
    right : {a, b : Type} -> g b (Either a b)
    apply : {a, b : Type} -> g (a -> b, a) b 
    curry : {a, b, c : Type} -> g (a, b) c -> g a (b -> c)
    uncurry : {a, b, c : Type} -> g a (b -> c) -> g (a, b) c 

  eval' : Category g -> FreeBCC g s t -> g s t  
  eval' alg (Prim f) = f 
  eval' alg Id  = alg.id 
  eval' alg (Comp f g) = alg.comp (eval' alg f) (eval' alg g)
  eval' alg (ProdI f g) = alg.prod (eval' alg f) (eval' alg g)
  eval' alg Fst = alg.fst
  eval' alg Snd = alg.snd
  eval' alg (CoprodI f g) = alg.coprod (eval' alg f) (eval' alg g)
  eval' alg InL = alg.left  
  eval' alg InR = alg.right
  eval' alg Apply = alg.apply
  eval' alg (Curry f) = alg.curry (eval' alg f) 
  eval' alg (Uncurry f) = alg.uncurry (eval' alg f)  

namespace Typed 
  public export
  data Ty : Type where
    Unit : Ty
    Prod : Ty -> Ty -> Ty 
    Sum : Ty -> Ty -> Ty
    Exp : Ty -> Ty -> Ty 
    N : Ty

  infixr 5 ~>
  public export
  (~>) : Ty -> Ty -> Ty
  (~>) = Exp

  infixr 5 :*: 
  public export
  (:*:) : Ty -> Ty -> Ty
  (:*:) = Prod 

  infixr 5 :+: 
  public export
  (:+:) : Ty -> Ty -> Ty 
  (:+:) = Sum 

  -- Free Bicartesian Closed Category over a typed graph
  public export
  data TypedBCC : Graph Ty -> Graph Ty where
    -- Embedding a primitive is now a separate operations from 'Comp' 
    Prim : {k : Graph Ty} -> k a b -> TypedBCC k a b 
    -- Identity arrow: a → a
    Id : {a : Ty} -> TypedBCC p a a 
    -- Composition of arrows: (b → c) → (a → b) → (a → c)
    Comp : {a, b, c : Ty} -> TypedBCC k b c -> TypedBCC k a b -> TypedBCC k a c
    -- Product introduction: (a → b) → (a → c) → (a → (b * c))
    ProdI : {a, b, c : Ty} -> TypedBCC k a b -> TypedBCC k a c -> TypedBCC k a (b :*: c) 
    -- First projection: (a * b) → a
    Fst : {a, b : Ty} -> TypedBCC k (a :*: b) a
    -- Second projection: (a * b) → b
    Snd : {a, b : Ty} -> TypedBCC k (a :*: b) b
    -- Coproduct introduction: (b → a) → (c → a) → (b + c → a)
    CoprodI : {a, b, c : Ty} -> TypedBCC k b a -> TypedBCC k c a -> TypedBCC k (b :+: c) a 
    -- Left injection: a → (a + b)
    InL : {a, b : Ty} -> TypedBCC k a (a :+: b)
    -- Right injection: b → (a + b)
    InR : {a, b : Ty} -> TypedBCC k b (a :+: b)
    -- Exponential elimination: 
    Apply : {a, b : Ty} -> TypedBCC k ((a ~> b) :*: a) b
    -- Currying: (a * b → c) → (a → (b ⇨ c)) 
    Curry : {a, b, c : Ty} -> TypedBCC k (a :*: b) c -> TypedBCC k a (b ~> c) 
    -- Uncurrying: (a → (b ⇨ c)) → (a * b → c) 
    Uncurry : {a, b, c : Ty} -> TypedBCC k a (b ~> c) -> TypedBCC k (a :*: b) c
    -- Terminal morphism into Unit
    Terminal : {a : Ty} -> TypedBCC k a Unit 
    Swap : {a, b : Ty} -> TypedBCC k (a :*: b) (b :*: a) 
    
  public export
  data Prims : Ty -> Ty -> Type where
    E : Prims Unit N  
    Mult : Prims (Prod N N) N
    Neg : Prims N N 
    
  -- We can define an evaluator like before. First we need to evaluate the types
  evalTy : Ty -> Type 
  evalTy Unit = Unit
  evalTy N = Nat
  evalTy (Exp t1 t2) = (evalTy t1) -> (evalTy t2)
  evalTy (Prod t1 t2) = (evalTy t1, evalTy t2)
  evalTy (Sum t1 t2) = Either (evalTy t1) (evalTy t2) 

  -- we'll need an evaluator for primitive elements. Let's use a monoid of natural numbers
  evalPrims : Prims ty1 ty2 -> Idr (evalTy ty1) (evalTy ty2)
  evalPrims E = \() => 0
  evalPrims Mult = uncurry (+)
  evalPrims _ = ?x 

  -- Then we can evaluate the terms. we parametrise it by an interpreter for prim elements
  eval : TypedBCC Prims ty1 ty2 -> Idr (evalTy ty1) (evalTy ty2)
  eval (Prim f) = evalPrims f  
  eval Id = id
  eval (Comp f g) = (eval f) . (eval g) 
  eval (ProdI f g) = \c => ((eval f) c, (eval g) c)   
  eval Fst = fst
  eval Snd = snd
  eval (CoprodI f g) = \c => case c of 
    Left l => (eval f) l 
    Right r => (eval g) r 
  eval InL = Left 
  eval InR = Right 
  eval Apply = uncurry apply
  eval (Curry f) = curry $ eval f 
  eval (Uncurry f) = uncurry $ eval f  
  eval Terminal = \_ => ()
  eval _ = ?s

  -- But now we can also formualte this more generically, by translating into an arbitrary category. 
  public export 
  record BCC {obj: Type} (g: Graph obj) where 
    constructor MkBCC 
    -- evaluator for objects
    ty : Ty -> obj
    -- evaluator for morphisms
    id : {a: Ty} -> g (ty a) (ty a)
    comp : {a, b, c : Ty} -> g (ty b) (ty c) -> g (ty a) (ty b) -> g (ty a) (ty c)
    prod : {a, b, c : Ty} -> g (ty c) (ty a) -> g (ty c) (ty b) -> g (ty c) (ty (a :*: b))
    fst : {a, b: Ty} -> g (ty (a :*: b)) (ty a)
    snd : {a, b :Ty} -> g (ty (a :*: b)) (ty b)
    coprod : {a, b, c : Ty} -> g (ty a) (ty c) -> g (ty b) (ty c) -> g (ty (a :+: b)) (ty c)
    left : {a, b : Ty} -> g (ty a) (ty (a :+: b))
    right : {a, b : Ty} -> g (ty b) (ty (a :+: b))
    apply : {a, b : Ty} -> g (ty ((a ~> b) :*: a)) (ty b) 
    curry : {a, b, c : Ty} -> g (ty (a :*: b)) (ty c) -> g (ty a) (ty (b ~> c))
    uncurry : {a, b, c : Ty} -> g (ty a) (ty (b ~> c)) -> g (ty (a :*: b)) (ty c) 
    terminal : {a : Ty} -> g (ty a) (ty Unit)
    -- evaluator for primitives
    e : g (ty Unit) (ty N)
    mult : g (ty (N :*: N)) (ty N)

  public export 
  eval' : (b : BCC g) -> TypedBCC Prims ty1 ty2 -> g (b.ty ty1) (b.ty ty2) 
  eval' alg (Prim E) = alg.e  
  eval' alg (Prim Mult) = alg.mult 
  eval' alg (Prim _) = ?zz
  eval' alg Id  = alg.id 
  eval' alg (Comp f g) = alg.comp (eval' alg f) (eval' alg g) 
  eval' alg (ProdI f g) = alg.prod (eval' alg f) (eval' alg g) 
  eval' alg Fst = alg.fst
  eval' alg Snd = alg.snd
  eval' alg (CoprodI f g) = alg.coprod (eval' alg f) (eval' alg g)
  eval' alg InL = alg.left  
  eval' alg InR = alg.right
  eval' alg Apply = alg.apply
  eval' alg (Curry f) = alg.curry (eval' alg f) 
  eval' alg (Uncurry f) = alg.uncurry (eval' alg f)  
  eval' alg Terminal = alg.terminal
  eval' alg _ = ?xy
