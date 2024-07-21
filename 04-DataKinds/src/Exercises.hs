{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}

module Exercises where

import Data.Function ((&))
import Data.Kind (Type)
import GHC.TypeLits (ErrorMessage (..), TypeError)

{- ONE -}

-- | One of the restrictions around classes that we occasionally hit is that we
-- can only have one instance for a type. There are, for example, two good
-- candidates for a monoid instance when we think about 'Integer':
data IntegerMonoid = Sum | Product

-- | a. Write a newtype around 'Integer' that lets us choose which instance we
-- want.
newtype NInt (a :: IntegerMonoid) = NInt {getInt :: Int}

-- | b. Write the two monoid instances for 'Integer'.
instance Semigroup (NInt Sum) where
  a <> b = NInt $ getInt a + getInt b

instance Semigroup (NInt Product) where
  a <> b = NInt $ getInt a * getInt b

instance Monoid (NInt Sum) where
  mempty = NInt 0

instance Monoid (NInt Product) where
  mempty = NInt 1

-- | c. Why do we need @FlexibleInstances@ to do this?

{- TWO -}

-- | We can write a type that /is/ of kind 'Type', but has no value-level
-- members. We usually call this type 'Void':
data Void -- No constructors!

-- | a. If we promote this with DataKinds, can we produce any /types/ of kind
-- 'Void'?

-- | b. What are the possible type-level values of kind 'Maybe Void'?

-- | c. Considering 'Maybe Void', and similar examples of kinds such as
-- 'Either Void Bool', why do you think 'Void' might be a useful kind?

{- THREE -}

-- | a. Write a GADT that holds strings or integers, and keeps track of how
-- many strings are present. Note that you might need more than 'Nil' and
-- 'Cons' this time...
data Nat = Z | S Nat

data StringAndIntList (stringCount :: Nat) (intCount :: Nat) where
  SINil :: StringAndIntList Z Z
  SCons :: String -> StringAndIntList s i -> StringAndIntList (S s) i
  ICons :: Int -> StringAndIntList s i -> StringAndIntList s (S i)

-- | b. Update it to keep track of the count of strings /and/ integers.

-- | c. What would be the type of the 'head' function?
class NoZero (a :: Nat) (b :: Nat)

instance NoZero (S a) b

instance NoZero a (S b)

instance (TypeError (Text "Both zero")) => NoZero Z Z

headSI :: (NoZero a b) => StringAndIntList a b -> Either String Int
headSI SINil = error "unreachable"
headSI (SCons s _) = Left s
headSI (ICons i _) = Right i

-- >>> headSI (SCons "123" SINil)
-- >>> headSI (ICons 123 SINil)
-- Left "123"
-- Right 123

-- >>> headSI SINil
-- Both zero
-- In the expression: headSI SINil
-- In an equation for `it_a6Ln0': it_a6Ln0 = headSI SINil

{- FOUR -}

-- | When we talked about GADTs, we discussed existentials, and how we could
-- only know something about our value if the context told us:
data Showable where
  Showable :: (Show a) => a -> Showable

-- | a. Write a GADT that holds something that may or may not be showable, and
-- stores this fact in the type-level.
data MaybeShowable (isShowable :: Bool) where
  IsShowable :: (Show a) => a -> MaybeShowable True
  IsNotShowable :: a -> MaybeShowable False

-- ...

-- | b. Write a 'Show' instance for 'MaybeShowable'. Your instance should not
-- work unless the type is actually 'show'able.
instance Show (MaybeShowable True) where
  show (IsShowable x) = show x

-- | c. What if we wanted to generalise this to @Constrainable@, such that it
-- would work for any user-supplied constraint of kind 'Constraint'? How would
-- the type change? What would the constructor look like? Try to build this
-- type - GHC should tell you exactly which extension you're missing.
data Constrainable c where
  Constrainable :: (c a) => a -> Constrainable c

{- FIVE -}

-- | Recall our list type:
data List a = Nil | Cons a (List a)

-- | a. Use this to write a better 'HList' type than we had in the @GADTs@
-- exercise. Bear in mind that, at the type-level, 'Nil' and 'Cons' should be
-- "ticked". Remember also that, at the type-level, there's nothing weird about
-- having a list of types!
data HList (types :: List Type) where
  HNil :: HList Nil
  HCons :: x -> HList xs -> HList (Cons x xs)

-- | b. Write a well-typed, 'Maybe'-less implementation for the 'tail' function
-- on 'HList'.
hTail :: HList (Cons x xs) -> HList xs
hTail (HCons _ xs) = xs

-- | c. Could we write the 'take' function? What would its type be? What would
-- get in our way?
hTake :: Int -> HList ys -> (forall xs. HList xs -> r) -> r
hTake _ HNil f = f HNil
hTake n (HCons x xs) f
  | n <= 0 = f HNil
  | otherwise = hTake (n - 1) xs (f . HCons x)

{- SIX -}

-- | Here's a boring data type:
data BlogAction (roles :: [Role]) where
  AddBlog :: BlogAction [Admin, Moderator, User]
  DeleteBlog :: BlogAction '[Admin]
  AddComment :: BlogAction [Admin, Moderator, User]
  DeleteComment :: BlogAction [Admin, Moderator]

-- | a. Two of these actions, 'DeleteBlog' and 'DeleteComment', should be
-- admin-only. Extend the 'BlogAction' type (perhaps with a GADT...) to
-- express, at the type-level, whether the value is an admin-only operation.
-- Remember that, by switching on @DataKinds@, we have access to a promoted
-- version of 'Bool'!

-- | b. Write a 'BlogAction' list type that requires all its members to be
-- the same "access level": "admin" or "non-admin".
data BlogActionList (isSafe :: [Role]) where
  BAList :: [BlogAction b] -> BlogActionList b

-- | c. Let's imagine that our requirements change, and 'DeleteComment' is now
-- available to a third role: moderators. Could we use 'DataKinds' to introduce
-- the three roles at the type-level, and modify our type to keep track of
-- this?
data Role = Admin | Moderator | User

{- SEVEN -}

-- | When we start thinking about type-level Haskell, we inevitably end up
-- thinking about /singletons/. Singleton types have a one-to-one value-type
-- correspondence - only one value for each type, only one type for each value.
-- A simple example is '()', whose only value is '()'. 'Bool' is /not/ a
-- singleton, because it has multiple values.

-- We can, however, /build/ a singleton type for 'Bool':

data SBool (value :: Bool) where
  SFalse :: SBool 'False
  STrue :: SBool 'True

-- | a. Write a singleton type for natural numbers:
data SNat (value :: Nat) where
  SZ :: SNat Z
  SS :: SNat n -> SNat (S n)

-- ...

-- | b. Write a function that extracts a vector's length at the type level:
length :: Vector n a -> SNat n
length VNil = SZ
length (VCons _ xs) = SS (Exercises.length xs)

-- | c. Is 'Proxy' a singleton type?
data Proxy a = Proxy

{- EIGHT -}

-- | Let's imagine we're writing some Industry Haskell™, and we need to read
-- and write to a file. To do this, we might write a data type to express our
-- intentions:
data Program (open :: Bool) result where
  OpenFile :: Program True result -> Program False result
  WriteFile :: String -> Program True result -> Program True result
  ReadFile :: (String -> Program True result) -> Program True result
  CloseFile :: Program False result -> Program True result
  Exit :: result -> Program False result

-- | We could then write a program like this to use our language:
myApp :: Program False Bool
myApp =
  OpenFile $
    WriteFile "HEY" $
      ReadFile (\contents ->
          if contents == "WHAT"
            then WriteFile "... bug?" $ CloseFile $ Exit False
            else CloseFile $ Exit True)

-- | ... but wait, there's a bug! If the contents of the file equal "WHAT", we
-- forget to close the file! Ideally, we would like the compiler to help us: we
-- could keep track of whether the file is open at the type level!
--
-- - We should /not/ be allowed to open a file if another file is currently
-- open.
--
-- - We should /not/ be allowed to close a file unless a file is open.
--
-- If we had this at the type level, the compiler should have been able to tell
-- us that the branches of the @if@ have different types, and this program
-- should never have made it into production. We should also have to say in the
-- type of 'myApp' that, once the program has completed, the file will be
-- closed.

-- | Improve the 'Program' type to keep track of whether a file is open.  Make
-- sure the constructors respect this flag: we shouldn't be able to read or
-- write to the file unless it's open. This exercise is a bit brain-bending;
-- why? How could we make it more intuitive to write?

-- | EXTRA: write an interpreter for this program. Nothing to do with data
-- kinds, but a nice little problem.
interpret :: Program b a -> IO a
interpret (OpenFile next) = putStrLn "opening file" >> interpret next
interpret (WriteFile s next) = putStrLn ("writing to file: " ++ s) >> interpret next
interpret (ReadFile f) = putStrLn "input: " >> getLine >>= interpret . f
interpret (CloseFile next) = putStrLn "closing file" >> interpret next
interpret (Exit b) = putStrLn "exiting" >> pure b

{- NINE -}

-- | Recall our vector type:
data Vector (n :: Nat) (a :: Type) where
  VNil :: Vector 'Z a
  VCons :: a -> Vector n a -> Vector ('S n) a

-- | Imagine we want to write the '(!!)' function for this vector. If we wanted
-- to make this type-safe, and avoid 'Maybe', we'd have to have a type that can
-- only hold numbers /smaller/ than some type-level value.

-- | a. Implement this type! This might seem scary at first, but break it down
-- into Z and S cases. That's all the hint you need :)
data SmallerThan (limit :: Nat) where
  STZ :: SmallerThan (S n)
  STS :: SmallerThan n -> SmallerThan (S n)

-- ...

-- | b. Write the '(!!)' function:
(!!) :: Vector n a -> SmallerThan n -> a
VCons x _ !! STZ = x
VCons _ xs !! STS n = xs Exercises.!! n

-- >>> VCons True (VCons False VNil) Exercises.!! STS STZ
-- False

-- >>> VCons True (VCons False VNil) Exercises.!! STS (STS STZ)
-- Couldn't match type 'S n0_a6KzP[tau:1] with 'Z
-- Expected: SmallerThan 'Z
--   Actual: SmallerThan ('S n0_a6KzP[tau:1])
-- In the first argument of `STS', namely `STZ'
-- In the first argument of `STS', namely `(STS STZ)'
-- In the second argument of `(!!)', namely `STS (STS STZ)'

-- | c. Write a function that converts a @SmallerThan n@ into a 'Nat'.
toNat :: SmallerThan a -> Nat
toNat STZ = Z
toNat (STS n) = S (toNat n)
