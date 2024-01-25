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

module Exercises where

import Data.Kind (Constraint, Type)
import Data.Void (Void)
import GHC.Generics (Generic (..))
import qualified GHC.Generics as G
import GHC.TypeLits (ErrorMessage (..), Natural, Symbol, TypeError)

{- ONE -}

-- | Recall an old friend, the 'Newtype' class:
class Newtype (new :: Type) where
  type Old new :: Type
  wrap :: Old new -> new
  unwrap :: new -> Old new

-- | a. Can we add a functional dependency to this class?

-- | b. Why can't we add two?

{- TWO -}

-- | Let's go back to a problem we had in the last exercise, and imagine a very
-- simple cache in IO. Uncomment the following:
class CanCache (entity :: Type) where
  type Index entity :: Type
  type Cache entity :: Type -> Type
  store :: entity -> Cache entity ()
  load :: index -> Cache entity (Maybe entity)

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

instance (Add' Z y ~ y) => Add Z y y

instance (Add x y z, z ~ Add' x y) => Add (S x) y (S z)

-- | We see here that there are parallels between classes and type families.
-- Type families produce a result, not a constraint, though we could write
-- @Add' x y ~ z => ...@ to mean the same thing as @Add x y z => ...@. Also,
-- the result of a type family is determined by its inputs - something we can
-- express as a functional dependency!

-- | a. Write the two required instances for the 'Add' class by
-- pattern-matching on the first argument. Remember that instances can have
-- constraints, and this is how we do recursion!

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
class (FromName x ~ label, ToName label ~ x) => (x :: k) `IsNamed` (label :: Symbol) where
  fromName :: Proxy x -> Proxy label
  fromName _ = Proxy

  toName :: Proxy label -> Proxy x
  toName _ = Proxy

type family FromName (x :: k) :: Symbol

type family ToName (x :: Symbol) :: k

type instance FromName Int = "Dylan"

type instance ToName "Dylan" = Int

type instance FromName IO = "Barbara"

type instance ToName "Barbara" = IO

type instance FromName Float = "Kenneth"

type instance ToName "Kenneth" = Float

-- | Now we have this class, we can get to work!
instance Int `IsNamed` "Dylan"

instance IO `IsNamed` "Barbara"

instance Float `IsNamed` "Kenneth"

-- | a. In our glorious new utopia, we decide to enact a law that says, "No two
-- types shall have the same name". Similarly, "No type shall have two names".
-- Is there a way to get GHC to help us uphold the law?

-- | b. Write the identity function restricted to types named "Kenneth".
idKenneth :: (x `IsNamed` "Kenneth") => x -> x
idKenneth = id

-- | c. Can you think of a less-contrived reason why labelling certain types
-- might be useful in real-world code?

{- FIVE -}

-- | Here's a fun little class:
class (Omni ~ r, Omni' ~ s) => Omnipresent (r :: Symbol) (s :: Natural)

type family Omni :: Symbol

type family Omni' :: Natural

type instance Omni = "Tom!"

type instance Omni' = 123

-- type instance Omni = "Sam!"

-- | Here's a fun little instance:
instance Omnipresent "Tom!" 123

-- instance Omnipresent "Sam!"

-- | a. Is there a way to enforce that no other instance of this class can ever
-- exist? Do we /need/ variables on the left-hand side of a functional
-- dependency arrow?

-- | b. Can you think of a time you would ever want this guarantee? Is this
-- "trick" something you can think of a practical reason for doing? Perhaps if
-- we added a method to the class? (Very much an open question).

-- | c. Add another similarly-omnipresent parameter to this type class.

{- SIX -}

-- | You knew it was coming, didn't you?
type family Every (c :: k -> Constraint) (xs :: [k]) :: Constraint where
  Every _ '[] = ()
  Every c (x ': xs) = (c x, Every c xs)

data HList (xs :: [Type]) where
  HNil :: HList '[]
  HCons :: x -> HList xs -> HList (x ': xs)

deriving instance (Every Show xs) => Show (HList xs)

data SNat (n :: Nat) where
  SZ :: SNat 'Z
  SS :: SNat n -> SNat ('S n)

-- | a. Write a function (probably in a class) that takes an 'SNat' and an
-- 'HList', and returns the value at the 'SNat''s index within the 'HList'.
class (At' n xs ~ x) => At (n :: Nat) (xs :: [Type]) (x :: Type) where
  at :: SNat n -> HList xs -> x

type family At' (n :: Nat) (xs :: [Type]) :: Type where
  At' Z (x ': _) = x
  At' (S n) (_ ': xs) = At' n xs
  At' _ '[] = Void

-- | b. Add the appropriate functional dependency.
instance At Z (x ': xs) x where
  at _ (HCons x _) = x

instance (At n xs x) => At (S n) (y ': xs) x where
  at (SS n) (HCons _ xs) = at n xs

instance (TypeError (Text "Out of bound")) => At n '[] Void where
  at = error "Unreachable"

-- >>> at (SS (SS SZ)) (HCons 123 (HCons "hello" (HCons True (HCons () HNil))))
-- True

-- >>> at (SS (SS (SS (SS SZ)))) (HCons 123 (HCons "hello" (HCons True (HCons () HNil))))
-- Out of bound
-- In the expression:
--   at
--     (SS (SS (SS (SS SZ))))
--     (HCons 123 (HCons "hello" (HCons True (HCons () HNil))))
-- In an equation for `it_ajjBY':
--     it_ajjBY
--       = at
--           (SS (SS (SS (SS SZ))))
--           (HCons 123 (HCons "hello" (HCons True (HCons () HNil))))

-- | c. Write a custom type error!

-- | d. Implement 'take' for the 'HList'.

{- SEVEN -}

-- | Recall our variant type:
data Variant (xs :: [Type]) where
  Here :: x -> Variant (x ': xs)
  There :: Variant xs -> Variant (y ': xs)

deriving instance (Every Show xs) => Show (Variant xs)

-- | We previously wrote a function to "inject" a value into a variant:
class Inject (x :: Type) (xs :: [Type]) where
  inject :: x -> Variant xs

instance {-# OVERLAPPING #-} Inject x (x ': xs) where
  inject = Here

instance
  (Inject x xs) =>
  Inject x (y ': xs)
  where
  inject = There . inject

class (ProjectH x xs ~ ys) => Project (x :: Type) (xs :: [Type]) (ys :: [Type]) where
  project :: Proxy x -> Variant xs -> Either x (Variant ys)

type family ProjectH (x :: Type) (xs :: [Type]) :: k where
  ProjectH x (x ': xs) = xs
  ProjectH x (y ': xs) = y ': ProjectH x xs
  ProjectH x '[] = '[]

instance Project x (x ': xs) xs where
  project _ (Here x) = Left x
  project _ (There xs) = Right xs

instance (Project x xs ys, ProjectH x (y ': xs) ~ (y ': ys)) => Project x (y ': xs) (y ': ys) where
  project _ (Here x) = Right (inject x)
  project p (There xs) = There <$> project p xs

instance (TypeError (Text "The type " :<>: ShowType x :<>: Text " is not in the Variaint")) => Project x '[] '[] where
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

-- >>> project (Proxy :: Proxy Bool) (inject True :: Variant '[Int, String, Bool])
-- Left True

-- >>> project (Proxy :: Proxy String) (inject True :: Variant '[Int, String, Bool])
-- Right (There (Here True))

-- >>> project (Proxy :: Proxy String) (inject "Hello" :: Variant '[Int, String, Bool])
-- Left "Hello"

-- >>> project (Proxy :: Proxy Double) (inject "Hello" :: Variant '[Int, String, Bool])
-- The type Double is not in the Variaint
-- In the expression:
--   project
--     (Proxy :: Proxy Double)
--     (inject "Hello" :: Variant '[Int, String, Bool])
-- In an equation for `it_ajhLy':
--     it_ajhLy
--       = project
--           (Proxy :: Proxy Double)
--           (inject "Hello" :: Variant '[Int, String, Bool])

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
type family UpdateH (n :: Nat) (x :: Type) (y :: Type) (xs :: [Type]) :: [Type] where
  UpdateH Z x y (x ': xs) = y ': xs
  UpdateH (S n) x y (z ': xs) = z ': UpdateH n x y xs
  UpdateH n x y (z ': xs) = z ': xs
  UpdateH n x y '[] = '[]

class (UpdateH n x y xs ~ ys, At n xs x, At n ys y) => Update (n :: Nat) (x :: Type) (y :: Type) (xs :: [Type]) (ys :: [Type]) where
  update :: SNat n -> (x -> y) -> HList xs -> HList ys

instance Update Z x y (x ': xs) (y ': xs) where
  update _ f (HCons x xs) = HCons (f x) xs

instance (Update n x y xs ys) => Update (S n) x y (z ': xs) (z ': ys) where
  update (SS n) f (HCons x xs) = HCons x (update n f xs)

-- >>> update (SS SZ) length (HCons True (HCons "Hello" HNil))
-- HCons True (HCons 5 HNil)

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

type family CalcOut f i where
  CalcOut f (a -> b) = f a -> CalcOut f b
  CalcOut f a = f a

type family CalcF o where
  CalcF (a -> b) = CalcF b
  CalcF (f b) = f

class (f ~ CalcF o, o ~ CalcOut f i) => Lift f i o where
  lift' :: (Applicative f) => f i -> o

instance (o ~ CalcOut f b, Lift f b o) => Lift f (a -> b) (f a -> o) where
  lift' fab fa = lift' (fab <*> fa)

instance (CalcF (f a) ~ f, CalcOut f a ~ f a) => Lift f a (f a) where
  lift' = id

-- | @class Lift f i o ... where lift' :: ...@ is your job! If you get this
-- right, perhaps with some careful use of @INCOHERENT@, equality constraints,
-- and functional dependencies, you should be able to get some pretty amazing
-- type inference:
--
-- >>> lift (++) (Just "123") Nothing
-- Nothing

-- >>> lift (++) (Just "123") (Just "234")
-- Just "123234"

-- >>> lift (++) ["123", "456"] ["234", "567"]
-- ["123234","123567","456234","456567"]

-- >>> lift (+ (2 :: Int)) [2, 4, 6]
-- [4,6,8]

-- >>> lift Just [2 :: Int, 4, 6]
-- [Just 2,Just 4,Just 6]

