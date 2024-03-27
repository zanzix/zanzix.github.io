import Data.Fin 

namespace Fix 
-- Conat: https://www.cse.chalmers.se/~nad/publications/danielsson-definitional-interpreters-complexity/Conat.html
namespace Church 

namespace Mendler 
-- mana :: (forall y. (x -> y) -> x -> f y) -> x -> Fix f

namespace FixH 
-- https://bartoszmilewski.com/2018/08/20/recursion-schemes-for-higher-algebras/

namespace Cofree 
-- (Stream, head, cosubst) is a comonad relative to eq : Type → Setoid.
-- a :< (f (Cofree f a))
  data Op : (Type -> Type) -> Type -> Type where 
--    Var : Op f n -> Fin n
    Extend : f m -> ((Op f m -> f n) -> f n) -> Op f n
-- unfold :: Functor f => (b -> (a, f b)) -> b -> Cofree f a


-- unfold : (b -> a) -> (b -> f b) -> b -> Cofree f a 
{--
Looks like Mu:

data Cofree f b = Node b (f (Cofree f b))
data Mu f = In (f (Mu f ))

Ah, just a product
--}

-- Unfold as memoise: http://blog.sigfpe.com/2014/05/cofree-meets-free.html
--- > memoiseComonad f w = Cofree (extract w) (fmap (memoiseComonad f) (f (duplicate w)))


-- Comonadic array: http://blog.sigfpe.com/2008/03/comonadic-arrays.html
-- Distributivity for pointer: https://hackage.haskell.org/package/category-extras-0.44.1/docs/Control-Comonad-Pointer.html
-- Called CArray here: https://www.cs.kent.ac.uk/people/staff/dao7/publ/codo-notation-orchard-ifl12.pdf
-- https://cs.ioc.ee/~tarmo/tsem10/orchard-slides.pdf
-- Structural vs Indexical pointers - zippers vs arrays
-- Comonad transformer version: https://hackage.haskell.org/package/comonad-extras-4.0.1/docs/Control-Comonad-Store-Pointer.html
namespace Cofreer 

namespace Ran 
-- Covector, p10: https://cs.ioc.ee/types15/slides/bizjak-grathwohl-clouston-mogelberg-birkedal-slides.pdf
-- delayed substitutions for type - modules? let?
  data Op : (Nat -> Type) -> Nat -> Type where 
    Extend : Fin n -> ((Op f m -> Fin n) -> f m) -> Op f n

    --Freest j f v -> Ran j f (Freest j f v)
namespace Ideal 
  data Comonoid : Nat -> Type where 
    Counit : Comonoid 0 
    Comult : Comonoid 2 

  data Op : (Nat -> Type) -> Nat -> Type where 
    Ex : Fin n -> (Op f n -> Fin m) -> Op f m
    

-- Pairing: https://blog.functorial.com/posts/2017-07-13-Equalizers-of-Comonads.html