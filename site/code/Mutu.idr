module Data.First.Mutu 

import Algebra.Indexed.Fix
import Algebra.Indexed.Algebra
import Kan.Indexed.Coyoneda

import Data.Fin 

-- Blog tip: Going up a level also cleans up the types massively, ie
{--
data ScopeCo : (Type -> Type) -> (Type -> Type) -> Type -> Type where
  PureS   : v -> ScopeCo f g v 
  ThenS   : f x -> (x -> ScopeCo f g v) -> ScopeCo f g v
  EnterS : g y -> (y -> ScopeCo f g x) -> (x -> ScopeCo f g a) -> ScopeCo f g a
--  it might actually be possible to rewrite the nested bind into Coyoneda form, but double check

-- Pattern functor 
data ScopeCoF : (Type -> Type) -> (Type -> Type) -> (Type -> Type) -> Type -> Type where 
  VarSF   : a -> ScopeCoF f g gam a 
  ThenSF  : f x   -> (x -> g a) -> ScopeCoF f g gam a 
  EnterSF : gam x -> (x -> g n) -> (n -> g a) -> ScopeCoF f g gam a

  https://lotz84.github.io/recursion-algorithms/Algorithms/List/BasicOperations/Reverse.html
--}

-- Not parametric, has a fixed parameter
data ListF : (Bool -> Type) -> (Bool -> Type) where 
  NilF : ListF r False
  ConsF : Nat -> r False -> ListF r False

-- hmmm, i have lost the ability to recurse on a value
-- i'd like to regain that. 


List1 : Bool -> Type  
List1 = Mu ListF 

exList : List1 False
exList = In $ NilF

exList1 : List1 False
exList1 = In $ ConsF (In $ ValIn 2) (exList)

listAlg : Algebra (Coyoneda ListF) EvalTy
listAlg (Coyo cont NilF) = 0
listAlg (Coyo cont (ConsF a b)) = 1 + (cont b)


-- Connor's version - unfortunately, constructing 't True' and 't False' is pretty difficult.
data ListBoo : (Bool -> Type) -> Type where 
  NilBoo : ListBoo t 
  ConsBoo : t True -> t False -> ListBoo t

data MonadBoo : (Bool -> (Type -> Type)) -> (Type -> Type) where 
  PureBoo : {a : Type} -> a -> MonadBoo t a 
  BindBoo : t True (t False a) -> MonadBoo t a 

data Inn : Type -> Type -> Bool -> Type where 
  InT : t -> Inn t f True
  InF : f -> Inn t f False

boo1 : ListBoo t
boo1 = ?s

inNil : Inn t (ListBoo p) False
inNil = InF NilBoo 

inVal : Inn Nat f True 
inVal = InT 5

--- Other file

data Pos = Val | Expr 

EvalTy : Pos -> Type 
EvalTy Val = Nat 
EvalTy Expr = Nat 

-- | Second attempt, w/o a pattern 
data ListVal : Type -> (Pos -> Type) where 
  NilV : ListVal a Expr
  ConsV : a -> ListVal a Expr -> ListVal a Expr

-- | Second attempt, pattern functor
data ListB : Type -> (Pos -> Type) -> (Pos -> Type) where 
  NilP : ListB a r Expr
  ConsP : a -> r Expr -> ListB a r Expr

-- | Third attempt, fully indexed
data ListF : (Pos -> Type) -> (Pos -> Type) where 
  NilF : ListF r Expr
  ValF : EvalTy Val -> ListF t Val
  ConsF : r Val -> r Expr -> ListF r Expr
  AppendF : r Expr -> r Expr -> ListF r Expr 
-- TODO: Change to more informative names, maybe Val and Expr 
-- pros and cons of representations. parametricity = more informative, but creates more syntactic noise, and we dont need the dangling parameter all the time
-- it's nice to have type annotations for recursive positions vs values

-- Blog tip: Contrast this to the definition of ListF as a standard pattern functor:
-- Blog tip: do this for free monads (and maybe free arrows) as well

{--
data ListF : Type -> Type -> Type) where 
  NilF : ListF a b
  ValF : a -> ListF a b
  ConsF : a -> b -> ListF a b
  AppendF : b -> b -> ListF a b 
--}

List2 : Type -> Pos -> Type 
List2 a = Mu (ListB a) 

exb : List2 a Expr 
exb = In NilP

exb2 : List2 Nat Expr 
exb2 = In $ ConsP 6 exb
 
parAlg : Algebra (Coyoneda (ListB Nat)) EvalTy
parAlg (Coyo cont NilP) = 0 
parAlg (Coyo cont (ConsP a b)) =  1 + (cont b)
parAlg _ = ?o2 -- 1 + (cont b)
-- TODO: try with K instead of EvalTy


-- BoolArith, an example with multiple types. Plays well with indexing for multiple positions 
--- https://tyde.systems/post/2019-12-04-razor/

data RTy = BOOL | NAT 

interpTy : RTy -> Type
interpTy NAT  = Nat
interpTy BOOL = Bool 

data BoolArith : RTy -> Type where 
  V : interpTy type -> BoolArith type 
  Add : BoolArith t -> BoolArith t -> BoolArith t

evalBA : BoolArith t -> interpTy t 
evalBA (V t) = t
evalBA (Add e1 e2) = ?ap (evalBA e1) (evalBA e2)  

-- to do this, i need to inspect the type, see the rest of blog post

data BoolArith1 : RTy -> Type where 
  V1 : interpTy type -> BoolArith1 type 
  AddNat : BoolArith1 NAT -> BoolArith1 NAT -> BoolArith1 NAT
  Conj : BoolArith1 BOOL -> BoolArith1 BOOL -> BoolArith1 BOOL 

evalBA1 : BoolArith1 t -> interpTy t 
evalBA1 (V1 t) = t
evalBA1 (AddNat e1 e2) = (evalBA1 e1) + (evalBA1 e2)  
evalBA1 (Conj e1 e2) = (evalBA1 e1) && (evalBA1 e2)  


data BoolArithF : (RTy -> Type) -> (RTy -> Type) where 
  VF : interpTy type -> BoolArithF r type
  AddF : r NAT -> r NAT -> BoolArithF r NAT
  ConjF : r BOOL -> r BOOL -> BoolArithF r BOOL 

-- Blog tip: if RTy = Type then this reduces to a functor (Type -> Type) -> (Type -> Type)
---- if RTy = () then this reduces to Type -> Type

-- TODO: Can this be combined with the other indexing, ie two mutually recursive types? Feels like it's already mutually recursive

-- TODO: Hm, recover List as a special case of BoolArith? 
-- Ah, I need to give an interpreter for Bool that includes the underlying data-type
-- damn, this solves the problem from yesterday, doesn't it?


{--
  ExampleI : RazorT INT
  ExampleI = Add (V 5) (V 4)

  ExampleF : RazorT REAL
  ExampleF = Add (V 5.0) (V 4.0)
--}

-- | Monads

-- | No pattern functor
data MonadVal : (Type -> Type) -> (Pos -> Type -> Type) where
  PureV : {a:Type} -> MonadVal f Expr a
  BindV : MonadVal f Val (MonadVal f Expr a) -> MonadVal f Expr a

-- | Pattern functor
data MonadPat : (Type -> Type) -> (Pos -> Type -> Type) -> Pos -> Type -> Type where 
  PureP : {a:Type} -> a -> MonadPat f r Expr a
  BindP : {a:Type} -> f (r Expr a) -> MonadPat f r Expr a
  BindP1 : {a:Type} -> r Val (r Expr a) -> MonadPat f r Expr a
---- ok this might be the best one...
-- for the blog, explain how ListB is a generalisation of ListF where we go from (Type) to (Pos -> Type)
-- OH, wait, my Operad type is kind of similar to this, right?

data Operad : (Type -> Type) -> (Nat -> Type -> Type) where 
  InOp : Fin n -> Operad f n a 
  LetOp : f a -> Operad f (S n) a -> Operad f n a

  -- we keep (Type -> Type) since we'll keep the underlying carrier
  -- but add Fin n, to keep track of variables
  -- this does look like MonadVal! Wow. So the 'free operad' would be the pattern functor over this

  -- not sure if these are correct, but essentially InOp embeds a value, LetOp embeds a functorial layer and binds it to a variable

opEx : Operad List 2 Nat 
opEx = LetOp (5 :: Nil) (InOp FZ) 

data OperadF : (Type -> Type) -> (Nat -> Type -> Type) -> Nat -> Type -> Type where
  InOpF : Fin n -> OperadF f r n a
  LetOpF : f a -> r (S n) a -> OperadF f r n a
--  CompOpF : f (r (S n) a) -> OperadF f r n a
  -- version with functor composition

-- Parametric and indexed
data ArrF : (Type -> Type -> Type) -> (Pos -> (Type -> Type -> Type)) -> (Pos -> (Type -> Type -> Type)) where 
  IdA : {a: Type} -> ArrF g r Expr a a
  CompA : {a, b: Type} ->  g b c -> r Expr a b -> ArrF g r Expr a b

-- Fully indexed
using (a: Type,
       b: Type,
       c: Type)

  data ArrF1 : (Pos -> (Type -> Type -> Type)) -> (Pos -> (Type -> Type -> Type)) where 
    IdA1 : ArrF1 r Expr a a
    --InArrF1 - need a way to create r Val
    CompA1 : r Val b c -> r Expr a b -> ArrF1 r Expr a c
    AppendF1 : r Expr b c -> r Expr a b -> ArrF1 r Expr a c 



data Mog = Term | PTerm | Graph | PGraph

data Ty : Type where  
  Base : Ty 
  U : Ty
  M : Ty -> Ty

EvalEdge : Mog -> (Ty -> Ty -> Type) 
EvalEdge _ t b = Ty -> Ty
--EvalEdge Term =   (\a,b=> a -> b) 
--EvalEdge PTerm =  (\a,b=> a -> b) 
--EvalEdge Graph =  (\a,b=> a -> b) 
--EvalEdge PGraph = (\a,b=> a -> b) 

-- Moggi, w/o parametricity 

data MogF : (Mog -> (Ty -> Ty -> Type)) -> (Mog -> (Ty -> Ty -> Type)) where 
  VarF : (b:Ty) -> MogF r Term U b 
  ValMF : r PTerm g a -> MogF r Term g (M a) 
  WrapF : r Term g a -> MogF r PTerm g a 
  LetValF : r Term g (M a) -> r PTerm a b -> MogF r PTerm g b
  InValF : EvalEdge Graph a b -> MogF r Term a b
  InCompF : EvalEdge PGraph a b -> MogF r PTerm a b

-- TODO: Try the parametric version

-- LNL Types

data LNL = CTerm | LTerm | CGraph | LGraph

data Kind = Pop | Star 

data KTy : Kind -> Type where 
  BaseC : KTy Star 
  BaseL : KTy Pop
  LProd : KTy Pop -> KTy Pop -> KTy Pop 
  CProd : KTy Star -> KTy Star -> KTy Star
  GTy : KTy Pop -> KTy Star 
  FTy : KTy Star -> KTy Pop
  N : KTy Pop
  E : KTy Star

EvalLNL : LNL  -> (KTy k1 -> KTy k2 -> Type) 
EvalLNL _ t b  = ?s -- KTy k1 -> KTy k2 
  
data LNLF : (LNL -> (KTy k1 -> KTy k2 -> Type)) -> (LNL -> (KTy k3 -> KTy k4 -> Type)) where 
  -- blog tip: the kinds are not preserved, otherwise it would be too restrictive
  IdC : LNLF r CTerm a a
  IdL : LNLF r LTerm a a
  GG  : r LTerm N d -> LNLF r CTerm E (GTy d)
  FF  : r CTerm g a -> LNLF r LTerm N (FTy a)
  Der : r CTerm g (GTy a) -> LNLF r LTerm N a 
  InC : EvalLNL CGraph a b -> LNLF r CTerm a b
  InL : EvalLNL LGraph a b -> LNLF r LTerm a b

--  CompL 
--  CompC 
--  LetValL 
--Letval : Split l ll lr -> LTerm g ll (F a) -> LTerm (a::g) lr b -> LTerm g l b

-- TODO: DILL, which looks like Moggi + LNL https://github.com/clayrat/modal-types/blob/master/src/Linear/DILL.idr  
-- TODO: Do the version where Linear terms have both contexts - can this be done using a mixed product, so as to not change the top-level types?

-- TODO: Then do MuMuTilde, w/o contexts, but where both terms depend on each other

-- TODO: IxOperad : (Ty -> Type) -> Nat -> Ty -> Type

-- TODO: IxOperadF : (Ty -> Type) -> (Nat -> Ty -> Type) -> Nat -> Ty -> Type

-- TODO: make RTy inductive, ie add products 
-- TODO: make RTy parametric over a base type
-- TODO: make RTy include Kinds - can I add polymorphism?
-- TODO: ArrF which is using multiple types of graphs

{-- Attempt w/o using mutually inductive types
data Kind = Pop | Star 

using (o: Type,
      a : o,
      b : o,
      c : o,
      g1 : o -> o -> Type,
      g2 : o -> o -> Type,
      r : Kind -> (o -> o -> Type))

  data CatF : (g1, g2 : o -> o -> Type) -> (Kind -> (o -> o -> Type)) -> (Kind -> (o -> o -> Type)) where 
    Id1 : CatF g1 g2 r Star a a
    Id2 : CatF g1 g2 r Pop a a
    Comp1 : g1 b c -> r Star a b -> CatF g1 g2 r Star a b
    Comp2 : g2 b c -> r Pop a b -> CatF g1 g2 r Pop a b
    LetVal : r Star b c -> r Pop a b -> CatF g1 g2 r Pop a c


data Ty : Type -> Kind -> Type where 
  BaseC : a -> Ty a Star 
  BaseL : a -> Ty a Pop
  LProd : Ty a Pop -> Ty a Pop -> Ty a Pop 
  CProd : Ty a Star -> Ty a Star -> Ty a Star
  GTy : Ty a Pop -> Ty a Star 
  FTy : Ty a Star -> Ty a Pop

--using (o: Type,
--      a : Ty o k,
--      b : Ty o k,
--      c : Ty o k,
--      g1 : Ty o k -> Ty o k -> Type,
--      g2 : Ty o k -> Ty o k -> Type,
--      r : Kind -> (Ty o k -> Ty o k -> Type))
--  
--  data LNL : (g1: Ty o Star -> Ty o Star -> Type) -> (g2 : Ty o k -> Ty o k -> Type) -> (Kind -> (Ty o k -> Ty o k -> Type)) -> (Kind -> (Ty o k -> Ty o k -> Type)) where 
--    Id1L : LNL g1 g2 r Star a a
--    Id2L : LNL g1 g2 r Pop a a
--    Comp1L : g1 b c -> r Star a b -> LNL g1 g2 r Star a b
--    Comp2L : g2 b c -> r Pop a b -> LNL g1 g2 r Pop a b
--    GG  : r Pop a d -> LNL g1 g2 r Star a (FTy d)
--    Der : r Star a (GTy b) ->  LNL g1 g2 r Pop a b

data LNL : (g1: Ty o Star -> Ty o Star -> Type) -> (g2 : Ty o k -> Ty o k -> Type) -> (Kind -> (Ty o k -> Ty o k -> Type)) -> (Kind -> (Ty o k -> Ty o k -> Type)) where 
  Id1L : LNL g1 g2 r Star a a
  Id2L : LNL g1 g2 r Pop a a
  Comp1L : g1 b c -> r Star a b -> LNL g1 g2 r Star a b
--}

{-- Attempt w/o parametricity

data Ty : Kind -> Type where 
  BaseC : Ty Star 
  BaseL : Ty Pop
  LProd : Ty Pop -> Ty Pop -> Ty Pop 
  CProd : Ty Star -> Ty Star -> Ty Star
  GTy : Ty Pop -> Ty Star 
  FTy : Ty Star -> Ty Pop

data CatLNL : (g1, g2 : Ty k -> Ty k -> Type) -> (Kind -> (Ty k -> Ty k -> Type)) -> (Kind -> (Ty k -> Ty k -> Type)) where 
  Id1L : CatLNL g1 g2 r Star a a
  Id2L : CatLNL g1 g2 r Pop a a
  Comp1L : g1 b c -> r Star a b -> CatLNL g1 g2 r Star a b
--  Comp2 : g2 b c -> r Pop a b -> CatF g1 g2 r Pop a b
  LetValL : r Star a (FTy b) -> r Pop b c -> CatLNL g1 g2 r Pop a c

--    LetValL : r Star g (FTy c) -> r Pop c b -> LNL g1 g2 r Pop g c
--    GG  : r Pop a d -> LNL g1 g2 r Star a (GTy d)
--    Der : r Star a (GTy b) ->  LNL g1 g2 r Pop a b
--Letval : Term g (G a) -> PTerm a b -> PTerm g b
--}





--data Values : (Ty o -> Ty o -> Type) -> (Ty o -> Ty o -> Type) -> (Ty o -> Ty o -> Type) where
--  VId  : Values h k a a
--  VComp : h b c -> k a b -> Values h k a c
--  
--data Comps : (Ty o -> Ty o -> Type) -> (Ty o -> Ty o -> Type) -> (Ty o -> Ty o -> Type) where
--  CId : Comps h k a a
--  CComp : h b c -> h a b -> Comps h h a c
--  LetVal : h b c -> k a b -> Comps h k a c

{-- NbE, mutual-recursion style

  indexes twice, by the branch and by the variable scope
  this could be a good way to combine this approach with my free multicategories

data NN :: ∗ → ({Nat,Bool} → ∗) where
Lam :: NN x {S n, T} → NN x {n, T}
Neu :: NN x {n, F} → NN x {n, T}
Par :: x → NN x {n, F}
Var :: Fin {n } → NN x {n, F}
App :: NN x {n, F} → NN x {n, T} → NN x {n, F}


rename :: (α → β) → (NorN α →· NorN β)
rename r (Lam t) = Lam (rename r t)
rename r (Neu t) = Neu (rename r t)
rename r (Par x) = Par (r x)
rename r (Var i) = Var i
rename r (App f s) = App (rename r f ) (rename r s)


--}
--Type -> Type -> Type 
--(Bool1 -> Type -> Type) -> (Bool1 -> Type -> Type)


--(Type -> Type) -> (Type -> Type) -> (Type -> Type)
--(MonadK -> (Type -> Type) -> (Type -> Type)) -> (MonadK -> (Type -> Type) -> (Type -> Type)) 




{--  Trash?

data ListF1 : ((Bool1, Type) -> Type) -> ((Bool1, Type) -> Type) where 
  ValF : a -> ListF1 r (Val1, a) 
  NilF1 : ListF1 r (Rec1, a)
  ConsF1 : r (Val1, a) -> r (Rec1, a) -> ListF1 r (Rec1, a)
  ConsA : a -> r (Rec1, a) -> ListF1 r (Rec1, a)

data ListF2 : (Bool1 -> Type -> Type) -> Bool1 -> Type -> Type where 
  ValF2 : a -> ListF2 r Val1 a 
  NilF2 : ListF2 r Rec1 a
  ConsF2 : r Val1 a -> r Rec1 a -> ListF2 r Rec1 a

List3 : (Bool1, Type) -> Type 
List3 = Mu ListF1

exList3 : List3 (Rec1, a)
exList3 = In NilF1

exList4 : List3 (Rec1, Nat)
exList4 = In $ ConsF1 (In $ ValF 2) exList3 

-- Monad trash:
data MonadF : (MonadK -> (Type -> Type) -> (Type -> Type)) -> (MonadK -> (Type -> Type) -> (Type -> Type)) where 
  PureF : {a: Type} -> a -> MonadF r BindK f a
  Wrap : f a -> MonadF r PureK f a
  BindF : {a: Type} -> MonadF r PureK f (MonadF r BindK f a) -> MonadF r BindK f a
  BindComp : {a: Type} -> Compose (MonadF r PureK f) (MonadF r BindK f) a -> MonadF r BindK f a

  -- Temporary make f=g? since their types should be Type->Type anyway...
-- can I lose the extra type parameter?
--data MonadF : (MonadK -> (Type -> Type)) -> (MonadK -> (Type -> Type)) where 
--  PureF : {a: Type} -> a -> MonadF r BindK a
--  Wrap : f a -> MonadF r PureK a
--  BindF : {a: Type} -> MonadF r PureK (MonadF r BindK a) -> MonadF r BindK a
--  BindComp : {a: Type} -> Compose (MonadF r PureK) (MonadF r BindK) a -> MonadF r BindK a


-- do an example of mutually recursive type, ie forests/trees

--data ListF : Type -> Type -> Type where 
--  Nil : ListF a b
--  Cons : a -> b -> ListF a b 

-- Muturec: https://www.andres-loeh.de/Rec/MutualRec.pdf
-- also same example in Loh: https://dreixel.net/research/pdf/gpif.pdf


{--
data PFAST ::(∗AST → ∗) → (∗AST → ∗) where
ConstF ::Int → PFAST r Expr
AddF ::r Expr → r Expr → PFAST r Expr
MulF ::r Expr → r Expr → PFAST r Expr
EVarF ::r Var → PFAST r Expr
LetF ::r Decl → r Expr → PFAST r Expr
BindF ::r Var → r Expr → PFAST r Decl
SeqF ::r Decl → r Decl → PFAST r Decl
VF ::String → PFAST r Var


-- Oleg, for type-checking: https://oleg.fi/gists/posts/2020-08-03-mutually-recursive-traversals.html
{--



data PFAST ::(∗AST → ∗) → (∗AST → ∗) where

{--
Example with lambda terms and patterns: https://gist.github.com/AndrasKovacs/af856be6cf816e08da95
data ExprType = ExprTy | PatTy

data ExprF (k :: ExprType -> *) (i :: ExprType) where
  
  -- "Expr" tagged family of constructors
  EIntF :: Int -> ExprF k ExprTy
  ELamF :: k PatTy -> k ExprTy -> ExprF k ExprTy

  -- "PatTy" tagged familfy of constructors
  PAsF  :: String -> k ExprTy -> ExprF k PatTy

type Expr = IxFix ExprF

--}
{--
data AST:: ∗AST → ∗ where
Expr::AST Expr
Decl ::AST Decl
Var ::AST Var

data PFAST ::(∗AST → ∗) → (∗AST → ∗) where
ConstF ::Int → PFAST r Expr
AddF ::r Expr → r Expr → PFAST r Expr
MulF ::r Expr → r Expr → PFAST r Expr
EVarF ::r Var → PFAST r Expr
LetF ::r Decl → r Expr → PFAST r Expr
BindF ::r Var → r Expr → PFAST r Decl
SeqF ::r Decl → r Decl → PFAST r Decl
VF ::String → PFAST r Var

Ok I actually see this now
we use an extra index, and this index is carried around to show if we change categories
  this does allow recursion on more than one sort, hm
  neat
  and, like in connor's work, we use indexing to generalise bifunctors to n functors

  I wonder if I can actually simplify my original bifunctor code, since I can now index the recursor and non-recursor?
    i need a reference that really explains this idea, since i realised this is a blindspot of mine


    data ListF : Type -> Type -> Type where 
    Nil : ListF a b
    Cons : a -> b -> ListF a b 

    right, there are two parameters - one for the values inside the container, one for the recursor itself
    but the values are not mutually recursive with the rest of the list, so we miss this
    if we want there to be both, we'd need to add another type parameter, I think?
    and the first one would always be filled anyway by the values, so we'd get a type
    
    data ListB : Type -> Type -> Type -> Type where 
      Nil : ListB val rec decl 
      Cons : val -> rec -> ListF val rec decl 
      Let : decl -> rec -> ListF val rec decl
    
    partially apply values
    ListB Nat : Type -> Type -> Type
    and then send to MuB

    I *might* be able to subsume values-vs-recursor into this higher-order approach
    that would simplify my types in one way, but complicate in another
    I think I'd like to experiment with this approach, as it might be possible to do this parametrically over a multi-functor in a better type system, thus removing both syntactical overheads

  data Expr e d = 
    Con_Int Int
  | Var String
  | If e e e
  | Apply e e
  | Where e d

  data Decls d e = 
    Dec d String e
  | None

  with mutually recursive types, they are both dependent on each other, so both use the other as a type parameter

  hmmm, i think i could do an example for ListB, FreeB, and ProfB
  it might be that using this kind of indexing is actually clearer in general
  replacing all of my higher-bifunctors with functors
  right, like extra annotations, rather than mental type-inference.
  plus, it'd give the user the ability to do extra type-checking rather than memorise variables
  
--}

--    (Type             ->  Type)                      -> Type 
--
--    ((o -> o -> Type) -> (o -> o -> Type)) -> o -> o -> Type
--
--    (Type -> Type -> Type) -> (Type -> Type -> Type) -> Type
--
--    (((o -> o -> Type) -> (o -> o -> Type)) -> o -> o -> Type) -> (((o -> o -> Type) -> (o -> o -> Type)) -> o -> o -> Type) -> ((o -> o -> Type) -> (o -> o -> Type)) -> o -> o -> Type

{-
data Fix2 : (Type -> Type -> Type) -> (Type -> Type -> Type) -> Type where 
    FixIn : f (Fix2 f g) (Fix2 g f) -> Fix2 f g
  
  --    (Type                  -> (Type                ) -> Type 
  --    (Type -> Type -> Type) -> (Type -> Type -> Type) -> Type
  
  --    (Type -> Type)         -> (Type -> Type)         -> Type -> Type
  --    ((Type -> Type) -> (Type -> Type) -> Type -> Type) -> ((Type -> Type) -> (Type -> Type) -> Type -> Type) -> Type -> Type
  
  --    ((Type -> Type -> Type) -> (Type -> Type -> Type) -> Type -> Type -> Type)
  -- ((Type -> Type -> Type) -> (Type -> Type -> Type) -> Type -> Type -> Type) -> ((Type -> Type -> Type) -> (Type -> Type -> Type) -> Type -> Type -> Type) -> Type -> Type -> Type
  
  data Free : ((Type -> Type) -> (Type -> Type) -> Type -> Type) -> ((Type -> Type) -> (Type -> Type) -> Type -> Type) -> Type -> Type where
    InFree : {a : Type} -> f (Free f g) (Free g f) a -> Free f g a 
  --  InFree : f (Fix2 f g) (Fix2 g f) -> Fix2 f g
  --  In : {a : Type} -> f (Mu f) a -> Mu f a
  
  data Arr : ((Type -> Type -> Type) -> (Type -> Type -> Type) -> Type -> Type -> Type) -> ((Type -> Type -> Type) -> (Type -> Type -> Type) -> Type -> Type -> Type) -> Type -> Type -> Type where 
    InArr : {a, b : Type} -> f (Arr f g) (Arr g f) a b -> Arr f g a b
    
  
  
  data Expr a b = 
      Const Int
    | Add a a
    | Let b a
  
  data Decl a b = 
      Var b
    | Seq a a
  
  ex1 : Fix2 Expr Decl
  ex1 = FixIn (Const 2)
  
  ex2 : Fix2 Expr Decl
  ex2 = FixIn (Add ex1 ex1)
  
  ex3 : Fix2 Expr Decl
  ex3 = FixIn (Add ex1 ex1)
  
  ex4 : Fix2 Expr Decl
  ex4 = FixIn (Let (FixIn $ Var (FixIn $ Const 5)) (FixIn (Const 4)))
  
  
  
  
  -- p23, swiestra, fold for bifunctors, vs fold for functors: https://www.cs.tufts.edu/~nr/cs257/archive/doaitse-swierstra/AFP3.pdf
