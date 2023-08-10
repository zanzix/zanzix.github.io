-- TODO: manually get these
import Data.List.Elem 

-- start with Type -> Type -> Type, and say how we move to a transformer instead?

data BCC : (Type -> Type -> Type) -> Type -> Type -> Type where
  Id : BCC p a a
  Prim : k a b -> BCC k a b
--  Comp 


-- Bicartesian Closed Category 


-- define the free BCC
{--
Free datatype for CCCs
Free BiCCC type
data (↣) ∷ * → * → * where
  -- Category
  Id      ∷ a ↣ a
  (:∘)    ∷ (b ↣ c) → (a ↣ b) → (a ↣ c)
  -- Products
  Exl     ∷ a × b ↣ a
  Exr     ∷ a × b ↣ b
  (:△)    ∷ (a ↣ b) → (a ↣ c) → (a ↣ b × c)
  -- Coproducts
  Inl     ∷ a ↣ a + b
  Inr     ∷ b ↣ a + b
  (:▽)    ∷ (b ↣ a) → (c ↣ a) → (b + c ↣ a)
  -- Exponentials
  Apply   ∷ (a ⇨ b) × a ↣ b
  Curry   ∷ (a × b ↣ c) → (a ↣ (b ⇨ c))
  Uncurry ∷ (a ↣ (b ⇨ c)) → (a × b ↣ c)
  -- Primitives
  Prim    ∷ Prim (a → b) → (a ↣ b)
  Const   ∷ Prim       b  → (a ↣ b)

data FreeCartesian k a b where
I :: FreeCartesian k a a
(:◦:) :: FreeCartesian k b c →FreeCartesian k a b
→FreeCartesian k a c 
Embed :: k a b→FreeCartesian k a b
(:△:) :: FreeCartesian k a b→FreeCartesian k a c
→FreeCartesian k a (b ⊗ c)
P1 :: FreeCartesian k (a ⊗ b) a
P2 :: FreeCartesian k (a ⊗ b) b
--}



  -- bicartesian closed category
  {--
  class Category k where
    id  ∷ a `k` a
    (∘) ∷ (b `k` c) → (a `k` b) → (a `k` c)
  
  class Category k ⇒ ProductCat k where
    exl ∷ (a × b) `k` a
    exr ∷ (a × b) `k` b
    (△) ∷ (a `k` c) → (a `k` d) → (a `k` (c × d))
  
  (×) ∷ ProductCat k ⇒ (a `k` c) → (b `k` d) → (a × b `k` c × d)
  f × g = f ∘ exl △ g ∘ exr
  
  first ∷ ProductCat k ⇒ (a `k` c) → ((a × b) `k` (c × b))
  first f = f × Id
  
  second ∷ ProductCat k ⇒ (b `k` d) → ((a × b) `k` (a × d))
  second g = Id × g
  
  class Category k ⇒ CoproductCat k where
    inl ∷ a `k` (a + b)
    inr ∷ b `k` (a + b)
    (▽) ∷ (a `k` c) → (b `k` c) → ((a + b) `k`  c)
  
  (×) ∷ ProductCat k ⇒ 
        (a `k` c) → (b `k` d) → ((a × b) `k` (c * d))
  f × g = f ∘ exl △ g ∘ exr
  
  apply   ∷ (a ⇨ b) × a ↝ b
  curry   ∷ (a × b ↝ c) → (a ↝ (b ⇨ c))
  uncurry ∷ (a ↝ (b ⇨ c)) → (a × b ↝ c)
  
  

-- define Records
record Category where 

{-- Classes

module Classes 

public export
record Graph where
    constructor MkGraph
    obj : Type
    hom : obj -> obj -> Type
    homs : List obj -> obj -> Type
    natObj : obj 
    uObj : obj 
    pairObj : obj -> obj -> obj 
    sumObj : obj -> obj -> obj 
    expObj : obj -> obj -> obj 

public export 
record Morphs (g : Graph) where 
    constructor MkMorphs 
    unitArr : {ctx : g.obj} -> g.hom ctx g.uObj
    toExpArr : {a, b : g.obj} -> g.hom a b -> g.hom g.uObj (g.expObj a b)
    -- TODO: Is this iotta-abstraction? or admissible in iota?

--    constArr : {ctx : g.obj} -> g.hom g.uObj ctx
--    envArr : {ctx : g.obj} -> g.hom
  
    idArr : {o : g.obj} -> g.hom o o
    compArr : {a, b, c : g.obj} -> g.hom a b -> g.hom b c -> g.hom a c 
    apArr : {ctx, a, b : g.obj} -> g.hom ctx (g.expObj a b) -> g.hom ctx a -> g.hom ctx b
    mkPair : {ctx, a, b : g.obj} -> g.hom ctx a -> g.hom ctx b -> g.hom ctx (g.pairObj a b)
    proj1 : {ctx, a, b : g.obj} -> g.hom ctx (g.pairObj a b) -> g.hom ctx a
    proj2 : {ctx, a, b : g.obj} -> g.hom ctx (g.pairObj a b) -> g.hom ctx b

public export 
record Functor (c, d : Graph) where
    constructor MkFunctor
    oMap : c.obj -> d.obj 
    hMap : {x, y : c.obj} -> c.hom x y -> d.hom (oMap x) (oMap y)
--    expMap : {x, y : c.obj} -> c.hom 
--    expMap : {x, y : c.obj} -> c.hom x y -> d.hom (oMap x) (oMap y)
--    -> d.expObj (oMap x) (oMap y)

public export
record MultiGraph where
    constructor MkGraph
    obj : Type
    unitObj : obj
    natObj : obj
    hom : List obj -> obj -> Type

public export
record MultiCat (c : MultiGraph) where 
    constructor MkMultiCategory
    idHom   : {x : c.obj} -> c.hom [x] x 
    compHom : {y, z : c.obj} -> {xs, ys : List c.obj} -> c.hom xs y -> c.hom (y :: ys) z -> c.hom (xs ++ ys) z
    -- in cartesian lambda calc, then xs == ys, so they are idempotent

public export
record Bicategory where 
    -- https://benediktahrens.gitlab.io/talks/TYPES2018.pdf
    -- uses 2-cells
    
-- todo: Semantics 
--- Functions with Products
---- representation List Type <-> (Type, ..., Type)
---- Substitution - replace one 'Type' with 'List Type', getting (Type, [Type], .., Type) ) and merge, doing [[Type]] -> [Type]
---- Var = Pure : Type -> List Type
--- Diagrams


--}



data Ty = U | N | Imp Ty Ty | Prod Ty Ty | Sum Ty Ty
-- TODO: define infix combinators

{--- STLC 

infixr 5 ~>
public export
(~>) : Ty -> Ty -> Ty
(~>) = Imp

evalTy : Ty -> Type 
evalTy N = Nat 
evalTy U = ()
evalTy (Imp t1 t2) = (evalTy t1) -> (evalTy t2)
evalTy (Prod t1 t2) = (evalTy t1, evalTy t2)
evalTy (Sum t1 t2) = Either (evalTy t1) (evalTy t2) 

infixr 5 :::
data Env : List Ty -> Type where
    CNil  : Env Nil
    (:::) : evalTy t -> Env g -> Env (t :: g)

lookup : Elem t g -> Env g -> evalTy t
lookup = ?xx 

extend : {t : Ty} -> (env : Env ctxt) -> (obj : evalTy t) -> Env (t::ctxt)
extend env obj = obj ::: env

-- TODO: check De Bruijn library: https://github.com/jfdm/idris-containers/blob/master/Data/DeBruijn.idr

public export 
data Term : List Ty -> Ty -> Type where
    -- often times people will use Ctx = List Ty as short-hand, but since we're going to look at many different calculi with their own unique notion of context, I like to be explicit here
    Var : {a : Ty} -> {g : List Ty} -> Elem a g -> Term g a
    Lam : {a, b : Ty} -> Term (a::g) b -> Term g (a ~> b)
    -- this is the most interesting rule as it shows a manipulation of contexts - the free variable 'a' is taken from the context and bound in the term
    -- TODO: replace '::' with a comonadic 'Pop' that takes a variable from the stack
    App : {a, b : Ty} -> Term g (a ~> b) -> Term g a -> Term g b

    Pair : {a, b : Ty} -> Term g a -> Term g b -> Term g (Prod a b)
    Fst  : {a, b : Ty} -> Term g (Prod a b) -> Term g a
    Snd  : {a, b : Ty} -> Term g (Prod a b) -> Term g b
    -- Standard rules for products in a cartesian category
    -- another interesting rule, we take a Sum of a b, and two terms - each with a hole corresponding to one part of the sum - and get a result of plugging them in 
    TT   : Term g U
    Let : {s : Ty} -> Term ctx s -> Term (s :: ctx) t -> Term ctx t
    -- A lot of introductory tutorials eschew Let because it seems to be just syntactic sugar for application, but this is only true for (CBV - double check). 
    -- For reasons that we will cover later, this is the most important rule, as it distills composing two terms together          

namespace ToType 
-- TODO: rewrite to use \env => f env, in order to show the similarity with toCategory
-- TODO: also interpret 'Env g', to be similar with toCategory
    eval : {g : List Ty} -> Term g t -> (Env g -> (evalTy t))
    eval (Var v) env = lookup v env
    eval (Lam t) env = \x => (eval t) (x ::: env)
    eval (App t1 t2) env = (eval t1 env) (eval t2 env)
    eval (Pair t1 t2) env = (eval t1 env, eval t2 env)
    eval (Fst t) env = fst (eval t env)
    eval (Snd t) env = snd (eval t env)
    eval (Let t c) env = eval c (extend env (eval t env))
    eval (TT) env = ()


eval : Category c => {g : List Ty} -> Term g t -> c (Env g) (evalTy t)
eval = ?und 


-- Lookup in a List of tuples: p107: https://www.proquest.com/openview/f6499782ef4cbb9800b8ac26aecef733/1?pq-origsite=gscholar&cbl=18750&diss=y
-- lookup : List (String, Val) → String → Maybe Val

-- Patterns:   Lam    ∷ Pat a → E b → E (a ⇨ b)

--}


-- To Category

-- eval : Category c => {g : List Ty} -> Term g t -> c (Env g) (evalTy t)


{-- p7, uses distributive law of Maybe and LC: https://www.slideshare.net/ekmett/revisiting-combinators-edward-kmett

-- TODO: translate Agda code
{--
lambda : ∀ {f} → Comb (σ :: Γ) τ f → Comb Γ (σ ⇒ τ) (λ env x → f (Cons x env))
lambda S = App K S
lambda K = App K K
lambda I = App K I
lambda (App t1 t2) = App (App S (lambda t1)) (lambda t2)
lambda (Var Top) = I
lambda (Var (Pop i)) = App K (Var i)

translate : (t : Term Γ σ) → Comb Γ σ J t K
translate (App t1 t2) = App (translate t1) (translate t2)
translate (Lam t) = lambda (translate t)
translate (Var i) = Var i

--}

{-- ToArrows?
--eval : (Arrow c, Closed c) => Term xs -> c (Env xs Val) Val
-- eval : (Arrow c, Strong c) => Term xs -> c (Env xs Val) Val
-- eval (Var s {p}) = arr ((flip lookupTerm) p)
-- eval (Lam x e) = arr (\env => Fun (arr (\v => (x, v) : env) >>> eval e))
-- eval (App e1 e2) = ((eval e1 >>> arr (\(Fun f) => f)) &&& eval e2) >>> ?app  -- ((eval s1) &&& (eval s2)) >>> mult 
-- -- ^replace 'app' with the closed instance for it

Conal, line 67: Patterns and Combinators: https://github.com/conal/lambda-ccc/blob/master/src/LambdaCCC/ToCCC.hs
--}