{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

-- {-# LANGUAGE UndecidableInstances #-}

module Exercises where

import Data.Kind (Constraint, Type)
import Data.Map (Map)
import Data.Proxy (Proxy (..))
import GHC.TypeLits (ErrorMessage (..), TypeError)
import Data.IntMap (IntMap)

{- ONE -}

-- | Consider the following types:
newtype MyInt = MyInt Int

newtype YourInt = YourInt Int

-- | As Haskell programmers, we love newtypes, so it would be super useful if
-- we could define a class that relates a newtype to the type it wraps, while
-- also giving us functions to get between them (we can call them 'wrap' and
-- 'unwrap').

-- | a. Write the class!
class Newtype new where
  type Old new :: Type
  wrap :: Old new -> new
  unwrap :: new -> Old new

-- | b. Write instances for 'MyInt' and 'YourInt'.
instance Newtype MyInt where
  type Old MyInt = Int
  wrap = MyInt
  unwrap (MyInt i) = i

instance Newtype YourInt where
  type Old YourInt = Int
  wrap = YourInt
  unwrap (YourInt i) = i

-- | c. Write a function that adds together two values of the same type,
-- providing that the type is a newtype around some type with a 'Num' instance.
add :: (Newtype new, Num (Old new)) => new -> new -> new
add x y = wrap (unwrap x + unwrap y)

-- | d. We actually don't need @MultiParamTypeClasses@ for this if we use
-- @TypeFamilies@. Look at the section on associated type instances here:
-- https://wiki.haskell.org/GHC/Type_families#Associated_type_instances_2 -
-- rewrite the class using an associated type, @Old@, to indicate the
-- "unwrapped" type. What are the signatures of 'wrap' and 'unwrap'?

{- TWO -}

-- | Who says we have to limit ourselves to /types/ for our parameters? Let's
-- look at the definition of 'traverse':
traverse1 :: (Traversable t, Applicative f) => (a -> f b) -> t a -> f (t b)
traverse1 = traverse

-- | This is all very well, but we often don't need @f@ to be an 'Applicative'.
-- For example, let's look at the good ol' 'Identity' type:
newtype Identity a = Identity a
  deriving (Functor) -- LANGUAGE DeriveFunctor

instance Foldable Identity where
  foldMap f (Identity x) = f x

instance Traversable Identity where
  traverse f (Identity x) = Identity <$> f x

-- | We can see that, in the @Traversable@ instance, we don't actually use
-- @pure@ /or/ @(<*>)@ - we only use @<$>@! It would be nice if we could have a
-- better @Traversable@ class that takes both the @t@ type /and/ the constraint
-- we want on the @f@...

-- | a. Write that little dazzler! What error do we get from GHC? What
-- extension does it suggest to fix this?
class Wanderable t where
  type C t :: (Type -> Type) -> Constraint
  wander :: (C t f) => (a -> f b) -> t a -> f (t b)

-- | b. Write a 'Wanderable' instance for 'Identity'.
instance Wanderable Identity where
  type C Identity = Functor
  wander f (Identity x) = Identity <$> f x

-- | c. Write 'Wanderable' instances for 'Maybe', '[]', and 'Proxy', noting the
-- differing constraints required on the @f@ type. '[]' might not work so well,
-- and we'll look at /why/ in the next part of this question!
instance Wanderable Maybe where
  type C Maybe = Applicative
  wander _ Nothing = pure Nothing
  wander f (Just x) = Just <$> f x

instance Wanderable [] where
  type C [] = Applicative
  wander _ [] = pure []
  wander f (x : xs) = (:) <$> f x <*> wander f xs

instance Wanderable Proxy where
  type C Proxy = Applicative
  wander _ _ = pure Proxy

-- | d. Assuming you turned on the extension suggested by GHC, why does the
-- following produce an error? Using only the extensions we've seen so far, how
-- could we solve this, perhaps in a way that involves another parameter to the
-- 'wander' function? A parameter whose type could be annotated? (Don't worry -
-- we'll see in later chapters that there are neater solutions to this
-- problem!)

-- test = wander Just [1, 2, 3]
-- >>> wander Just [1, 2, 3]
-- Just [1,2,3]

{- THREE -}

data Nat = Z | S Nat

data SNat (n :: Nat) where
  SZ :: SNat 'Z
  SS :: SNat n -> SNat ('S n)

-- | In the @DataKinds@ chapter, we wrote the 'SmallerThan' data type, which
-- we'll call 'Fin' from now on:
data Fin (limit :: Nat) where
  FZ :: Fin ('S n)
  FS :: Fin n -> Fin ('S n)

-- | We can write a class to take an 'SNat' to a 'Fin' using
-- @MultiParamTypeClasses@. We can even use @TypeOperators@ to give our class a
-- more intuitive name:
class (x :: Nat) < (y :: Nat) where
  convert :: SNat x -> Fin y
  invert :: Fin y -> Maybe (SNat x)

-- | a. Write the instance that says @Z@ is smaller than @S n@ for /any/ @n@.
instance Z < S n where
  convert SZ = FZ
  invert FZ = Just SZ
  invert _ = Nothing

-- | b. Write an instance that says, if @x@ is smaller than @y@, then @S x@ is
-- smaller than @S y@.
instance (x < y) => S x < S y where
  convert (SS x) = FS (convert x)
  invert (FS x) = SS <$> invert x
  invert _ = Nothing

-- | c. Write the inverse function for the class definition and its two
-- instances.

-- >>> :set -XStandaloneDeriving
-- >>> :set -XTypeApplications
-- >>> deriving instance Show (SNat n)
-- >>> deriving instance Show (Fin n)
-- >>> invert @(S (S (S Z))) (FS (FS FZ) :: Fin (S (S (S (S Z)))))
-- >>> invert @(S (S Z)) (FS (FS FZ) :: Fin (S (S (S (S Z)))))
-- Nothing
-- Just (SS (SS SZ))
{- FIVE -}

-- | It wouldn't be a proper chapter without an @HList@, would it?
data HList (xs :: [Type]) where
  HNil :: HList '[]
  HCons :: x -> HList xs -> HList (x ': xs)

instance Show (HList '[]) where
  show HNil = "HNil"

instance (Show x, Show (HList xs)) => Show (HList (x ': xs)) where
  show (HCons x xs) = show x ++ " : " ++ show xs

-- In fact, you know what? You can definitely write an HList by now – I'll
-- just put my feet up and wait here until you're done!

-- | Consider the following class for taking the given number of elements from
-- the front of an HList:
type family Take (n :: Nat) (xs :: [Type]) :: [Type] where
  Take Z xs = '[]
  Take (S n) '[] = '[]
  Take (S n) (x ': xs) = x ': Take n xs

class (Take n xs ~ ys) => HTake (n :: Nat) (xs :: [Type]) (ys :: [Type]) where
  htake :: SNat n -> HList xs -> HList ys

-- | a. Write an instance for taking 0 elements.
instance HTake Z xs '[] where
  htake SZ xs = HNil

-- | b. Write an instance for taking a non-zero number. You "may" need a
-- constraint on this instance.
instance (HTake n xs ys) => HTake (S n) (x ': xs) (x ': ys) where
  htake (SS n) (HCons x xs) = HCons x (htake n xs)

-- | c. What case have we forgotten? How might we handle it?
instance HTake (S n) '[] '[] where
  htake _ _ = HNil

-- >>> x = HCons True $ HCons 123 $ HCons "string" HNil
-- >>> htake (SS SZ) x
-- >>> htake (SS (SS SZ)) x
-- >>> htake (SS (SS (SS SZ))) x
-- >>> htake (SS (SS (SS (SS SZ)))) x
-- True : HNil
-- True : 123 : HNil
-- True : 123 : "string" : HNil
-- True : 123 : "string" : HNil

{- SIX -}

-- | We could also imagine a type class to "pluck" types out of @HList@:
class Pluck (x :: Type) (xs :: [Type]) where
  pluck :: HList xs -> x

-- | a. Write an instance for when the head of @xs@ is equal to @x@.
instance {-# OVERLAPPING #-} Pluck x (x ': xs) where
  pluck (HCons x _) = x

-- | b. Write an instance for when the head /isn't/ equal to @x@.
instance (Pluck x xs) => Pluck x (y ': xs) where
  pluck (HCons _ xs) = pluck xs

-- | c. Using [the documentation for user-defined type
-- errors](http://hackage.haskell.org/package/base-4.11.1.0/docs/GHC-TypeLits.html#g:4)
-- as a guide, write a custom error message to show when you've recursed
-- through the entire @xs@ list (or started with an empty @HList@) and haven't
-- found the type you're trying to find.
instance (TypeError (Text "The type " :<>: ShowType x :<>: Text " is not in the given list.")) => Pluck x '[] where
  pluck = error "unreachable"

-- | d. Making any changes required for your particular HList syntax, why
-- doesn't the following work? Hint: try running @:t 3@ in GHCi.

-- >>> pluck (HCons 123 (HCons True HNil)) :: Bool
-- >>> pluck (HCons (123 :: Int) (HCons True HNil)) :: Int
-- True
-- 123

{- SEVEN -}

-- | A variant is similar to an 'Either', but generalised to any non-zero
-- number of parameters. Typically, we define it with two parameters: @Here@
-- and @There@. These tell us which "position" our value inhabits:

-- >>> [ Here True, There (Here 3), There (There (Here "hello")) ] :: [Variant '[Bool, Int, String]]
-- [Here True,There (Here 3),There (There (Here "hello"))]

-- >>> [ inject True, inject (3 :: Int), inject "Hello" ] :: [Variant '[Bool, Int, String]]
-- [Here True,There (Here 3),There (There (Here "Hello"))]

-- >>> [ inject True, inject (3 :: Int), inject "Hello" ] :: [Variant '[Bool, Double, String]]
-- The type Int is not in the given variant.
-- In the expression: inject (3 :: Int)
-- In the expression:
--     [inject True, inject (3 :: Int), inject "Hello"] ::
--       [Variant '[Bool, Double, String]]
-- In an equation for `it_apeWT':
--     it_apeWT
--       = [inject True, inject (3 :: Int), inject "Hello"] ::
--           [Variant '[Bool, Double, String]]

-- | a. Write the 'Variant' type to make the above example compile.
data Variant (xs :: [Type]) where
  Here :: x -> Variant (x ': xs)
  There :: Variant xs -> Variant (x ': xs)

instance (Show x, Show (Variant xs)) => Show (Variant (x ': xs)) where
  show (Here x) = "Here " ++ show x
  show (There xs) = "There (" ++ show xs ++ ")"

instance Show (Variant '[]) where
  show = error "unreachable"

-- | b. The example is /fine/, but there's a lot of 'Here'/'There' boilerplate.
-- Wouldn't it be nice if we had a function that takes a type, and then returns
-- you the value in the right position? Write it! If it works, the following
-- should compile: @[inject True, inject (3 :: Int), inject "hello"]@.
class Inject x xs where
  inject :: x -> Variant xs

instance {-# OVERLAPPING #-} Inject x (x ': xs) where
  inject = Here

instance (Inject x xs) => Inject x (y ': xs) where
  inject x = There (inject x)

instance (TypeError (Text "The type " :<>: ShowType x :<>: Text " is not in the given variant.")) => Inject x '[] where
  inject = error "unreachable"

-- | c. Why did we have to annotate the 3? This is getting frustrating... do
-- you have any (not necessarily good) ideas on how we /could/ solve it?

{- EIGHT -}

-- | As engineers, we are wont to over-think day-to-day problems in order to
-- justify our existence to scrum masters. As such, we are compelled to visit
-- our friendly neighbourhood angel investor with a new idea: given the weather
-- and rough temperature, our web2.0, blockchain-ready app - chil.ly - will
-- tell you whether or not you need a coat. Let's start by defining our inputs:
data Weather = Sunny | Raining

data Temperature = Hot | Cold

-- ... and some singletons, why not?

data SWeather (w :: Weather) where
  SSunny :: SWeather 'Sunny
  SRaining :: SWeather 'Raining

data STemperature (t :: Temperature) where
  SHot :: STemperature 'Hot
  SCold :: STemperature 'Cold

-- | Now, our app is going to be ready-for-scale, B2B, and proven with zero
-- knowledge, so we want type safety /at the core/. Naturally, we've defined
-- the relationship between the two domains as a type class.
class Coat (a :: Weather) (b :: Temperature) where
  doINeedACoat :: SWeather a -> STemperature b -> Bool

-- | It's early days, and we're just building an MVP, but there are some rules
-- that /everyone/ knows, so they should be safe enough!

-- No one needs a coat when it's sunny!
instance {-# INCOHERENT #-} Coat Sunny b where doINeedACoat _ _ = False

-- It's freezing out there - put a coat on!
instance Coat a Cold where doINeedACoat _ _ = True

-- | Several months pass, and your app is used by billions of people around the
-- world. All of a sudden, your engineers encounter a strange error:
test :: Bool
test = doINeedACoat SSunny SCold

-- | Clearly, our data scientists never thought of a day that could
-- simultaneously be sunny /and/ cold. After months of board meetings, a
-- decision is made: you /should/ wear a coat on such a day. Thus, the
-- __second__ rule is a higher priority.

-- | a. Uncomment the above, and add OVERLAPPING and/or OVERLAPPABLE pragmas
-- to prioritise the second rule. Why didn't that work? Which step of the
-- instance resolution process is causing the failure?

-- | b. Consulting the instance resolution steps, which pragma /could/ we use
-- to solve this problem? Fix the problem accordingly.

-- | c. In spite of its scary name, can we verify that our use of it /is/
-- undeserving of the first two letters of its name?

{- NINE -}

-- | The 'Show' typeclass has two instances with which we're probably quite
-- familiar:

-- instance Show a => Show [a]
-- instance           Show String

-- | a. Are these in conflict? When?

-- | b. Let's say we want to define an instance for any @f a@ where the @f@ is
-- 'Foldable', by converting our type to a list and then showing that. Is there
-- a pragma we can add to the first 'Show' instance above so as to preserve
-- current behaviour? Would we need /more/ pragmas than this?

-- | c. Somewhat confusingly, we've now introduced incoherence: depending on
-- whether or not I've imported this module, 'show' will behave in different
-- ways. Your colleague suggests that your use of pragmas is the root issue
-- here, but they are missing the bigger issue; what have we done? How could we
-- have avoided it?

{- TEN -}

-- | Let's imagine we have some types in our codebase:
newtype UserId = UserId Int

data User = User
  { id :: UserId,
    knownAs :: String
  }

newtype CommentId = CommentId Int

data Comment = Comment
  { id :: CommentId,
    author :: UserId,
    text :: String
  }

data Status = Blocked | Deleted

-- | In order to better facilitate mobile devices, we now want to introduce
-- caching. I start work, and eventually slide a pull request into your DMs:
class UserCache where
  storeUser :: User -> Map UserId User -> Map UserId User
  loadUser :: Map UserId User -> UserId -> Either Status User

class CommentCache where
  storeComment :: Comment -> Map CommentId Comment -> Map CommentId Comment
  loadComment :: Map CommentId Comment -> CommentId -> Maybe Comment

-- | "This is silly", you exclaim. "These classes only differ in three ways! We
-- could write this as a multi-parameter type class!"

-- | a. What are those three ways? Could we turn them into parameters to a
-- typeclass? Do it!
class Cacheable content where
  type Id content :: Type
  type Result content :: Type -> Type
  type Cache content :: Type -> Type
  store :: content -> Cache content content -> Cache content content
  load :: Cache content content -> Id content -> Result content content

instance Cacheable User where
  type Id User = UserId
  type Result User = Either Status
  type Cache User = IntMap
  store = undefined
  load = undefined

instance Cacheable Comment where
  type Id Comment = CommentId
  type Result Comment = Maybe
  type Cache Comment = IntMap
  store = undefined
  load = undefined

-- | b. Write instances for 'User' and 'Comment', and feel free to implement
-- them as 'undefined' or 'error'. Now, before uncommenting the following, can
-- you see what will go wrong? (If you don't see an error, try to call it in
-- GHCi...)

oops cache = load cache (UserId (123 :: Int))

-- | c. Do we know of a sneaky trick that would allow us to fix this? Possibly
-- involving constraints? Try!
