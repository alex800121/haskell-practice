{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE RankNTypes #-}

module Exercises where

import Data.Kind (Constraint, Type)
import Data.Void (Void)
import GHC.Generics (Generic (..))
import qualified GHC.Generics as G
import GHC.TypeLits (ErrorMessage (..), Symbol, TypeError)

{- ONE -}

-- | Recall an old friend, the 'Newtype' class:
class old ~ Old new => Newtype (new :: Type) (old :: Type) where
  type Old new
  wrap :: old -> new
  unwrap :: new -> old

-- | a. Can we add a functional dependency to this class?

-- | b. Why can't we add two?

{- TWO -}

-- | Let's go back to a problem we had in the last exercise, and imagine a very
-- simple cache in IO. Uncomment the following:
class CanCache (entity :: Type) (index :: Type) (m :: Type -> Type) | entity -> index where
  store :: entity -> m ()
  load :: index -> m (Maybe entity)

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

class Add (x :: Nat) (y :: Nat) (z :: Nat) | x y -> z
instance Add Z y y
instance Add x y z => Add (S x) y (S z)

-- | We see here that there are parallels between classes and type families.
-- Type families produce a result, not a constraint, though we could write
-- @Add' x y ~ z => ...@ to mean the same thing as @Add x y z => ...@. Also,
-- the result of a type family is determined by its inputs - something we can
-- express as a functional dependency!

-- | a. Write the two required instances for the 'Add' class by
-- pattern-matching on the first argument. Remember that instances can have
-- constraints, and this is how we do recursion!

data Vec (n :: Nat) (a :: k) where
  VNil :: Vec 'Z a
  VCons :: a -> Vec n a -> Vec ('S n) a

type family All (c :: k -> Constraint) (xs :: [k]) :: Constraint where
  All _ '[] = ()
  All c (x ': xs) = (c x, All c xs)

deriving instance (Show a) => Show (Vec n a)

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
idKenneth :: (a `IsNamed` "Kenneth") => a -> a
idKenneth = id

-- | c. Can you think of a less-contrived reason why labelling certain types
-- might be useful in real-world code?

{- FIVE -}

-- | Here's a fun little class:
class Omnipresent (r :: Symbol) (s :: Nat) | -> r s

-- | Here's a fun little instance:
instance Omnipresent "Tom!" 'Z

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
class Index (n :: Nat) (xs :: [Type]) where
  type At n xs :: Type
  index :: SNat n -> HList xs -> At n xs

instance Index 'Z (x ': xs) where
  type At 'Z (x ': xs) = x
  index _ (HCons x _) = x

instance (Index n xs) => Index ('S n) (y ': xs) where
  type At ('S n) (y ': xs) = At n xs
  index (SS n) (HCons _ ys) = index n ys

instance (TypeError (Text "Out of index")) => Index n '[] where
  type At n '[] = Void
  index = error "unreachable"

-- | b. Add the appropriate functional dependency.

-- | c. Write a custom type error!

-- | d. Implement 'take' for the 'HList'.
class Take (n :: Nat) (xs :: [Type]) where
  type Taken n xs :: [Type]
  take :: SNat n -> HList xs -> HList (Taken n xs)

instance Take 'Z xs where
  type Taken 'Z xs = '[]
  take _ _ = HNil

instance Take n '[] where
  type Taken n '[] = '[]
  take _ _ = HNil

instance (Take n xs) => Take ('S n) (x ': xs) where
  type Taken ('S n) (x ': xs) = x ': Taken n xs
  take (SS n) (HCons x xs) = HCons x (Exercises.take n xs)

{- SEVEN -}

-- | Recall our variant type:
deriving instance (All Show xs) => Show (Variant xs)

data Variant (xs :: [Type]) where
  Here :: x -> Variant (x ': xs)
  There :: Variant xs -> Variant (y ': xs)

-- | We previously wrote a function to "inject" a value into a variant:

type family Project x xs where
  Project x '[] = '[]
  Project x (x ': xs) = xs
  Project x (y ': xs) = y ': Project x xs

class (ys ~ Project x xs) => Inject (x :: Type) (xs :: [Type]) (ys :: [Type]) where
  inject :: x -> Variant xs
  project :: Proxy x -> Variant xs -> Either x (Variant ys)

instance {-# OVERLAPPING #-} (Project x (x ': xs) ~ xs) => Inject x (x ': xs) xs where
  inject = Here
  project _ (Here x) = Left x
  project _ (There xs) = Right xs

instance (Project x (y ': xs) ~ y ': Project x xs, Inject x xs ys) => Inject x (y ': xs) (y ': ys) where
  inject = There . inject
  project _ (Here x) = Right (inject x)
  project p (There xs) = There <$> project p xs

instance (TypeError (Text "The given type \"" :<>: ShowType x :<>: Text "\" is not in the Variant")) => Inject x '[] '[] where
  inject = error "unreachable"
  project = error "unreachable"

-- | Write a function to "project" a value /out of/ a variant. In other words,
-- I would like a function that takes a proxy of a type, a variant containing
-- that type, and returns /either/ a value of that type /or/ the variant
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
deriving instance (All Show xs) => Show (HList xs)

class Update (n :: Nat) (x :: Type) (y :: Type) (xs :: [Type]) where
  type Updated n x y xs :: [Type]
  update :: SNat n -> (x -> y) -> HList xs -> HList (Updated n x y xs)

instance x ~ z => Update 'Z x y (z ': xs) where
  type Updated 'Z x y (z ': xs) = y ': xs
  update _ f (HCons x xs) = HCons (f x) xs

instance Update n x y xs => Update ('S n) x y (z ': xs) where
  type Updated ('S n) x y (z ': xs) = z ': Updated n x y xs
  update (SS n) f (HCons z xs) = HCons z (update n f xs)

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

class ConstructorNameOf (x :: Type) (names :: [Symbol]) | x -> names
instance GConstructorNameOf (Rep x) names => ConstructorNameOf x names
class GConstructorNameOf (rep :: Type -> Type) (names :: [Symbol]) | rep -> names
instance GConstructorNameOf constructors names => GConstructorNameOf (G.D1 m constructors) names
instance GConstructorNameOf xs names => GConstructorNameOf (G.C1 (G.MetaCons name a b) c G.:+: xs) (name ': names)
instance GConstructorNameOf (G.C1 (G.MetaCons name a b) c) '[name]
instance GConstructorNameOf G.V1 '[]

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

-- lift :: (Applicative f, Lift f i o) => i -> o
-- lift = lift' . pure

-- | @class Lift f i o ... where lift' :: ...@ is your job! If you get this
-- right, perhaps with some careful use of @INCOHERENT@, equality constraints,
-- and functional dependencies, you should be able to get some pretty amazing
-- type inference:
--
-- >>> :t lift (++)
-- lift (++) :: Applicative f => f [a] -> f [a] -> f [a]

type family GetApplicative (a :: Type) :: Type -> Type where
  GetApplicative (f a -> o) = f
  GetApplicative (f a) = f

type family GetOutcome f i where
  GetOutcome f (a -> b) = f a -> GetOutcome f b
  GetOutcome f a = f a

class (Applicative f, f ~ GetApplicative o, o ~ GetOutcome f i) => Lift f i o where
  lift' :: f i -> o

instance (Applicative f, Lift f b o, o' ~ (f a -> o)) => Lift f (a -> b) o' where
  lift' fs xs = lift' (fs <*> xs)

instance {-# INCOHERENT #-} (Applicative f, o ~ f a, GetApplicative (f a) ~ f, GetOutcome f a ~ f a) => Lift f a o where
  lift' = id

lift :: (Applicative f, Lift f i o) => i -> o
lift = lift' . pure
