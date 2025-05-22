{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module Exercises where

import Data.Kind (Type)
import Data.Void (Void)
import GHC.Generics (Generic (..))
import qualified GHC.Generics as G
import GHC.TypeLits (ErrorMessage (..), Symbol, TypeError)

{- ONE -}

-- | Recall an old friend, the 'Newtype' class:
class (old ~ New old) => Newtype (new :: Type) (old :: Type) where
  type New old
  wrap :: old -> new
  unwrap :: new -> old

-- | a. Can we add a functional dependency to this class?

-- | b. Why can't we add two?

{- TWO -}

-- | Let's go back to a problem we had in the last exercise, and imagine a very
-- simple cache in IO. Uncomment the following:
class (index ~ I entity) => CanCache (entity :: Type) (index :: Type) (f :: Type -> Type) where
  type I entity
  store :: entity -> f ()
  load :: index -> f (Maybe entity)

-- | a. Uh oh - there's already a problem! Any @entity@ type should have a
-- fixed type of id/@index@, though... if only we could convince GHC... Could
-- you have a go?

-- | b. @IO@ is fine, but it would be nice if we could choose the functor when
-- we call @store@ or @load@... can we parameterise it in some way?

-- | c. Is there any sort of functional dependency that relates our
-- parameterised functor to @entity@ or @index@? If so, how? If not, why not?

{- THREE -}

-- | Let's re-introduce one of our old favourites:
data Nat = Z | S Nat

-- | When we did our chapter on @TypeFamilies@, we wrote an @Add@ family to add
-- two type-level naturals together. If we do a side-by-side comparison of the
-- equivalent "class-based" approach:
class (Add' x y ~ z) => Add (x :: Nat) (y :: Nat) (z :: Nat)

type family Add' (x :: Nat) (y :: Nat) :: Nat where
  Add' Z y = y
  Add' (S x) y = S (Add' x y)

-- | We see here that there are parallels between classes and type families.
-- Type families produce a result, not a constraint, though we could write
-- @Add' x y ~ z => ...@ to mean the same thing as @Add x y z => ...@. Also,
-- the result of a type family is determined by its inputs - something we can
-- express as a functional dependency!

-- | a. Write the two required instances for the 'Add' class by
-- pattern-matching on the first argument. Remember that instances can have
-- constraints, and this is how we do recursion!
instance Add Z y y

instance (Add x y z) => Add (S x) y (S z)

-- | b. By our analogy, a type family has only "one functional dependency" -
-- all its inputs to its one output. Can we write _more_ functional
-- dependencies for @Add@? Aside from @x y -> z@?

-- | c. We know with addition, @x + y = z@ implies @y + x = z@ and @z - x = y@.
-- This should mean that any pair of these three variables should determine the
-- other! Why couldn't we write all the possible functional dependencies that
-- /should/ make sense?

{- FOUR -}

data Proxy (a :: k) = Proxy

-- | As we all know, type signatures are /not/ documentation. This is really
-- because the names of types are far too confusing. To that end, we can give
-- our types friendlier names to make the coding experience less intimidating:
class (x :: k) `IsNamed` (label :: Symbol) | x -> label, label -> x where
  fromName :: Proxy x -> Proxy label
  fromName _ = Proxy

  toName :: Proxy label -> Proxy x
  toName _ = Proxy

-- | Now we have this class, we can get to work!
instance Int `IsNamed` "Dylan"

instance IO `IsNamed` "Barbara"

instance Float `IsNamed` "Kenneth"

-- | a. In our glorious new utopia, we decide to enact a law that says, "No two
-- types shall have the same name". Similarly, "No type shall have two names".
-- Is there a way to get GHC to help us uphold the law?

-- | b. Write the identity function restricted to types named "Kenneth".

-- | c. Can you think of a less-contrived reason why labelling certain types
-- might be useful in real-world code?

{- FIVE -}

-- | Here's a fun little class:
class Omnipresent (r :: Symbol) (s :: k) | -> r s

-- | Here's a fun little instance:
instance Omnipresent "Tom!" 1

-- | a. Is there a way to enforce that no other instance of this class can ever
-- exist? Do we /need/ variables on the left-hand side of a functional
-- dependency arrow?

-- | b. Can you think of a time you would ever want this guarantee? Is this
-- "trick" something you can think of a practical reason for doing? Perhaps if
-- we added a method to the class? (Very much an open question).

-- | c. Add another similarly-omnipresent parameter to this type class.

{- SIX -}

-- | You knew it was coming, didn't you?
data HList (xs :: [Type]) where
  HNil :: HList '[]
  HCons :: x -> HList xs -> HList (x ': xs)

data SNat (n :: Nat) where
  SZ :: SNat 'Z
  SS :: SNat n -> SNat ('S n)

-- | a. Write a function (probably in a class) that takes an 'SNat' and an
-- 'HList', and returns the value at the 'SNat''s index within the 'HList'.
class (IndexF n xs ~ x) => Index (n :: Nat) (x :: Type) (xs :: [Type]) where
  index :: HList xs -> SNat n -> x

type family IndexF n xs where
  IndexF Z (x ': xs) = x
  IndexF (S n) (y ': xs) = IndexF n xs
  IndexF n '[] = Void

instance Index Z x (x ': xs) where
  index (HCons x _) _ = x

instance (Index n x xs) => Index (S n) x (y ': xs) where
  index (HCons _ xs) (SS n) = index xs n

instance (TypeError (Text "index out of bound")) => Index n Void '[] where
  index _ _ = error "unreachable"

-- >>> index (HCons 123 (HCons True (HCons "123" HNil))) (SS (SS SZ))
-- >>> index (HCons 123 (HCons True (HCons "123" HNil))) (SS SZ)
-- "123"
-- True

-- >>> index (HCons 123 (HCons True (HCons "123" HNil))) (SS (SS (SS SZ)))
-- index out of bound
-- In the expression:
--   index (HCons 123 (HCons True (HCons "123" HNil))) (SS (SS (SS SZ)))
-- In an equation for `it_aeYrc':
--     it_aeYrc
--       = index
--           (HCons 123 (HCons True (HCons "123" HNil))) (SS (SS (SS SZ)))

-- | b. Add the appropriate functional dependency.

-- | c. Write a custom type error!

-- | d. Implement 'take' for the 'HList'.
type family TakeF n xs where
  TakeF Z xs = '[]
  TakeF (S n) (x ': xs) = x ': TakeF n xs
  TakeF (S n) '[] = '[]

class (TakeF n xs ~ ys) => Take n xs ys where
  take :: SNat n -> HList xs -> HList ys

instance Take Z xs '[] where
  take _ _ = HNil

instance (Take n xs ys) => Take (S n) (x ': xs) (x ': ys) where
  take (SS n) (HCons x xs) = HCons x (Exercises.take n xs)

instance Take (S n) '[] '[] where
  take _ _ = HNil

instance (Show x, Show (HList xs)) => Show (HList (x ': xs)) where
  show (HCons x xs) = show x ++ " : " ++ show xs

instance Show (HList '[]) where
  show HNil = "HNil"

-- >>> Exercises.take (SS (SS (SS (SS SZ)))) (HCons 1 (HCons True (HCons "123" HNil)))
-- >>> Exercises.take (SS (SS (SS SZ))) (HCons 1 (HCons True (HCons "123" HNil)))
-- >>> Exercises.take (SS (SS SZ)) (HCons 1 (HCons True (HCons "123" HNil)))
-- >>> Exercises.take (SS SZ) (HCons 1 (HCons True (HCons "123" HNil)))
-- >>> Exercises.take SZ (HCons 1 (HCons True (HCons "123" HNil)))
-- 1 : True : "123" : HNil
-- 1 : True : "123" : HNil
-- 1 : True : HNil
-- 1 : HNil
-- HNil

{- SEVEN -}

-- | Recall our variant type:
data Variant (xs :: [Type]) where
  Here :: x -> Variant (x ': xs)
  There :: Variant xs -> Variant (y ': xs)

-- | We previously wrote a function to "inject" a value into a variant:
type family InjectF x xs :: Bool where
  InjectF x (x ': xs) = True
  InjectF x (y ': xs) = False
  InjectF x '[] = False

class (InjectF x xs ~ b) => Inject (b :: Bool) (x :: Type) (xs :: [Type]) where
  inject :: x -> Variant xs

instance (Show x, Show (Variant xs)) => Show (Variant (x ': xs)) where
  show (Here x) = "Here " ++ show x
  show (There xs) = "There (" ++ show xs ++ ")"

instance Show (Variant '[]) where
  show _ = error "Unreachable"

instance Inject True x (x ': xs) where
  inject = Here

instance (InjectF x (y ': xs) ~ False, Inject (InjectF x xs) x xs) => Inject False x (y ': xs) where
  inject = There . inject

instance (TypeError (Text "type not found"), InjectF x '[] ~ False) => Inject False x '[] where
  inject = error "unreachable"

test0 = inject True :: Variant [Bool, Int, String]

test1 = inject (3 :: Int) :: Variant [Bool, Int, String]

test2 = inject "123" :: Variant [Bool, Int, String]

-- >>> test0
-- >>> test1
-- >>> test2
-- Here True
-- There (Here 3)
-- There (There (Here "123"))

-- >>> inject () :: Variant [Bool, Int, String]
-- type not found
-- In the expression: inject () :: Variant [Bool, Int, String]
-- In an equation for `it_aeWl4':
--     it_aeWl4 = inject () :: Variant [Bool, Int, String]

type family ProjectF x xs where
  ProjectF x (x ': xs) = xs
  ProjectF x (y ': xs) = y ': ProjectF x xs
  ProjectF x '[] = '[]

class (ProjectF x xs ~ ys) => Project x xs ys where
  project :: Proxy x -> Variant xs -> Either x (Variant ys)

instance Project x (x ': xs) xs where
  project _ (Here x) = Left x
  project _ (There xs) = Right xs

instance (ProjectF x (y ': xs) ~ y ': ProjectF x xs, Project x xs ys) => Project x (y ': xs) (y ': ys) where
  project _ (Here x) = Right (inject x)
  project p (There xs) = There <$> project p xs

instance (ProjectF x '[] ~ '[], TypeError (Text "type not found")) => Project x '[] '[] where
  project = error "unreachable"

test5 = inject (Just 1 :: Maybe Int) :: Variant [Bool, Double, String, Maybe Int, ()]

-- >>> :t project (Proxy :: Proxy Bool) test5
-- >>> project (Proxy :: Proxy Bool) test5
-- >>> :t project (Proxy :: Proxy Double) test5
-- >>> project (Proxy :: Proxy Double) test5
-- >>> :t project (Proxy :: Proxy String) test5
-- >>> project (Proxy :: Proxy String) test5
-- >>> :t project (Proxy :: Proxy (Maybe Int)) test5
-- >>> project (Proxy :: Proxy (Maybe Int)) test5
-- >>> :t project (Proxy :: Proxy ()) test5
-- >>> project (Proxy :: Proxy ()) test5
-- project (Proxy :: Proxy Bool) test5 :: Either Bool (Variant '[Double, String, Maybe Int, ()])
-- Right There (There (Here Just 1))
-- project (Proxy :: Proxy Double) test5 :: Either Double (Variant '[Bool, String, Maybe Int, ()])
-- Right There (There (Here Just 1))
-- project (Proxy :: Proxy String) test5 :: Either String (Variant '[Bool, Double, Maybe Int, ()])
-- Right There (There (Here Just 1))
-- project (Proxy :: Proxy (Maybe Int)) test5 :: Either (Maybe Int) (Variant '[Bool, Double, [Char], ()])
-- Left (Just 1)
-- project (Proxy :: Proxy ()) test5 :: Either () (Variant '[Bool, Double, [Char], Maybe Int])
-- Right There (There (There (Here Just 1)))

-- >>> project (Proxy :: Proxy ()) test2
-- type not found
-- In the expression: project (Proxy :: Proxy ()) test2
-- In an equation for `it_aeUlG':
--     it_aeUlG = project (Proxy :: Proxy ()) test2

-- type not found
-- In the expression: project (Proxy :: Proxy ()) test2
-- In an equation for `it_aLU1m':
--     it_aLU1m = project (Proxy :: Proxy ()) test2
-- /excluding/ that type:
--
-- @
--   project (Proxy :: Proxy Bool) (inject True :: Variant '[Int, String, Bool])
--     === Left Bool :: Either Bool (Variant '[Int, String])
-- @

{- EIGHT -}

-- | It would be nice if I could update a particular index of an HList by
-- providing an index and a (possibly-type-changing) function. For example:
--
-- @
--   update (SS SZ) length (HCons True (HCons "Hello" HNil))
--     === HCons True (HCons 5 HNil)
-- @

-- | Write the type class required to implement this function, along with all
-- its instances and functional dependencies.
-- class Update (n :: Nat) (x :: Type) (y :: Type) (xs :: [Type]) (ys :: [Type]) where
type family UpdateF n y xs :: [Type] where
  UpdateF Z y (x ': xs) = y ': xs
  UpdateF (S n) y (x ': xs) = x ': UpdateF n y xs
  UpdateF Z y '[] = '[]
  UpdateF (S n) y '[] = '[]

class (UpdateF n y xs ~ ys) => Update (n :: Nat) (x :: Type) (y :: Type) (xs :: [Type]) (ys :: [Type]) where
  update :: SNat n -> (x -> y) -> HList xs -> HList ys

instance (x ~ z, UpdateF Z y (z ': xs) ~ (y ': xs)) => Update Z x y (z ': xs) (y ': xs) where
  update _ f (HCons x xs) = HCons (f x) xs

instance (Update n x y xs ys, UpdateF (S n) y (z ': xs) ~ z ': UpdateF n y xs) => Update (S n) x y (z ': xs) (z ': ys) where
  update (SS n) f (HCons x xs) = HCons x (update n f xs)

instance (UpdateF n y '[] ~ '[]) => Update n x y '[] '[] where
  update _ _ _ = HNil

test4 = HCons (123 :: Int) $ HCons True $ HCons "123" HNil

-- >>> :t test4
-- >>> test4
-- >>> update SZ (+ (1 :: Int)) test4
-- >>> update (SS SZ) not test4
-- >>> update (SS (SS SZ)) length test4
-- >>> update (SS (SS (SS SZ))) (+ (1 :: Int)) test4
-- test4 :: HList '[Int, Bool, String]
-- 123 : True : "123" : HNil
-- 124 : True : "123" : HNil
-- 123 : False : "123" : HNil
-- 123 : True : 3 : HNil
-- 123 : True : "123" : HNil

{- NINE -}

-- | If you've made it this far, you're more than capable of digesting and
-- understanding some advanced GHC docs! Read the documentation at
-- http://hackage.haskell.org/package/base-4.12.0.0/docs/GHC-Generics.html, and
-- keep going until you hit 'Generic1' - we won't worry about that today.

-- | We can write a little function to get the name of a type as a type-level
-- symbol like so:
class NameOf (x :: Type) (name :: Symbol) | x -> name

instance (GNameOf (Rep x) name) => NameOf x name

-- | We then have to implement this class that examines the generic tree...
class GNameOf (rep :: Type -> Type) (name :: Symbol) | rep -> name

instance GNameOf (G.D1 ('G.MetaData name a b c) d) name

-- | Write a function to get the names of the constructors of a type as a
-- type-level list of symbols.
type family ConstructorNameOfF (x :: Type) :: [Symbol] where
  ConstructorNameOfF x = GConstructorNameOfF (Rep x)

type family GConstructorNameOfF (rep :: Type -> Type) :: [Symbol] where
  GConstructorNameOfF (G.D1 a b) = GListConstructorNameOfF b

type family GListConstructorNameOfF (rep :: Type -> Type) :: [Symbol] where
  GListConstructorNameOfF G.V1 = '[]
  GListConstructorNameOfF (G.C1 (G.MetaCons name b c) d) = '[name]
  GListConstructorNameOfF (G.C1 (G.MetaCons name b c) d G.:+: x) = name ': GListConstructorNameOfF x

class (ConstructorNameOfF x ~ y) => ConstructorNameOf x y

instance (ConstructorNameOfF x ~ y, GConstructorNameOf (Rep x) y) => ConstructorNameOf x y

class (GConstructorNameOfF x ~ y) => GConstructorNameOf x y

instance (GListConstructorNameOf z y) => GConstructorNameOf (G.D1 a z) y

class (GListConstructorNameOfF x ~ y) => GListConstructorNameOf x y

instance GListConstructorNameOf G.V1 '[]

instance GListConstructorNameOf (G.C1 (G.MetaCons name b c) d) '[name]

instance (GListConstructorNameOf x names) => GListConstructorNameOf (G.C1 (G.MetaCons name b c) d G.:+: x) (name ': names)

-- ConstructorNameOfF (Either x y) :: [Symbol]
-- = '["Left", "Right"]
-- ConstructorNameOfF () :: [Symbol]
-- = '["()"]
-- ConstructorNameOfF Void :: [Symbol]
-- = '[]
-- ConstructorNameOfF () :: [Symbol]
-- = '["()"]
-- ConstructorNameOfF Void :: [Symbol]
-- = '[]

{- TEN -}

-- | In the standard library, we have a series of @liftA*@ functions, such as
-- 'liftA2', 'liftA3', 'liftA4'... wouldn't it be nice if we just had /one/
-- function called 'lift' that generalised all these?
--
-- liftA1 :: Applicative f => (a -> b) -> f a -> f b
-- liftA1 = lift
--
-- liftA2 :: Applicative f => (a -> b -> c) -> f a -> f b -> f c
-- liftA2 = lift
--
--
-- liftA3 :: Applicative f => (a -> b -> c -> d) -> f a -> f b -> f c -> f d
-- liftA3 = lift

-- | Write this function, essentially generalising the f <$> a <*> b <*> c...
-- pattern. It may help to see it as pure f <*> a <*> b <*> c..., and start
-- with a function like this:
lift :: (Applicative f, Lift f i o) => i -> o
lift = lift' . pure

type family LiftF f i where
  LiftF f ((->) a b) = f a -> LiftF f b
  LiftF f a = f a

type family CalcF o where
  CalcF (f i -> o) = CalcF o
  CalcF (f i) = f

-- class (Applicative f) => Lift f i o | o -> f, f i -> o where
class (Applicative f, LiftF f i ~ o, CalcF o ~ f) => Lift f i o where
  lift' :: f i -> o

instance
  ( Applicative f,
    LiftF f i ~ f i,
    CalcF (f i) ~ f
  ) =>
  Lift f i (f i)
-- instance
--   {-# INCOHERENT #-} (Applicative f, f i ~ o) =>
--   Lift f i o
  where
  lift' = id

instance
  ( Lift f b o',
    LiftF f (a -> b) ~ (f a -> o'),
    CalcF (f a -> o') ~ CalcF o',
    Applicative f
  ) =>
  Lift f (a -> b) (f a -> o')
  -- (Applicative f, Lift f b o', (f a -> o') ~ o) => Lift f (a -> b) o
  where
  lift' fa = lift' . (fa <*>)

-- >>> :t lift (++)
-- >>> lift (++) [[2,3,4],[5,6]] [[7],[8,9,10],[11]]
-- lift (++) :: (CalcF (f [a]) ~ f, Applicative f) => f [a] -> f [a] -> f [a]
-- [[2,3,4,7],[2,3,4,8,9,10],[2,3,4,11],[5,6,7],[5,6,8,9,10],[5,6,11]]

-- >>> :t lift foldr
-- >>> lift foldr [(+), (*), const] [1,2,3] [[4,5,6],[7,8]]
-- lift foldr
--   :: (Lift f b (LiftF f b), Foldable t) =>
--      f (a -> b -> b) -> f b -> f (t a) -> LiftF f b
-- [16,16,17,17,18,18,120,56,240,112,360,168,4,7,4,7,4,7]

-- | @class Lift f i o ... where lift' :: ...@ is your job! If you get this
-- right, perhaps with some careful use of @INCOHERENT@, equality constraints,
-- and functional dependencies, you should be able to get some pretty amazing
-- type inference:
