{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Exercises where

import Data.Kind (Constraint, Type)

-- | Before we get started, let's talk about the @TypeOperators@ extension. All
-- this does is allow us to write types whose names are operators, and write
-- regular names as infix names with the backticks, as we would at the value
-- level.

{- ONE -}

data Nat = Z | S Nat

-- | a. Use the @TypeOperators@ extension to rewrite the 'Add' family with the
-- name '+':
type family (a :: Nat) + (b :: Nat) :: Nat where
  Z + b = b
  (S a) + b = S (a + b)

-- | b. Write a type family '**' that multiplies two naturals using '(+)'. Which
-- extension are you being told to enable? Why?
data SNat (value :: Nat) where
  SZ :: SNat 'Z
  SS :: SNat n -> SNat ('S n)

-- | c. Write a function to add two 'SNat' values.
(+) :: SNat a -> SNat b -> SNat (a + b)
SZ + b = b
(SS a) + b = SS (a Exercises.+ b)

{- TWO -}

data Vector (count :: Nat) (a :: Type) where
  VNil :: Vector 'Z a
  VCons :: a -> Vector n a -> Vector ('S n) a

-- | a. Write a function that appends two vectors together. What would the size
-- of the result be?
append :: Vector m a -> Vector n a -> Vector (m + n) a
append VNil ys = ys
append (VCons x xs) ys = VCons x (append xs ys)

-- | b. Write a 'flatMap' function that takes a @Vector n a@, and a function
-- @a -> Vector m b@, and produces a list that is the concatenation of these
-- results. This could end up being a deceptively big job.
type family (a :: Nat) ** (b :: Nat) :: Nat where
  Z ** b = Z
  (S a) ** b = b + (a ** b)

flatMap :: Vector n a -> (a -> Vector m b) -> Vector (n ** m) b
flatMap VNil _ = VNil
flatMap (VCons x xs) f = append (f x) (flatMap xs f)

{- THREE -}

-- | a. More boolean fun! Write the type-level @&&@ function for booleans.
type family (a :: Bool) && (b :: Bool) :: Bool where
  'False && _ = 'False
  'True && b = b

-- | b. Write the type-level @||@ function for booleans.
type family (a :: Bool) || (b :: Bool) :: Bool where
  'True || _ = 'True
  'False || b = b

-- | c. Write an 'All' function that returns @'True@ if all the values in a
-- type-level list of boleans are @'True@.
type family All (xs :: [Bool]) :: Bool where
  All '[] = 'True
  All (x ': xs) = x && All xs

{- FOUR -}

-- | a. Nat fun! Write a type-level 'compare' function using the promoted
-- 'Ordering' type.
type family Compare (a :: Nat) (b :: Nat) :: Ordering where
  Compare Z Z = EQ
  Compare Z _ = LT
  Compare _ Z = GT
  Compare (S a) (S b) = Compare a b

-- | b. Write a 'Max' family to get the maximum of two natural numbers.
type family Max (a :: Nat) (b :: Nat) :: Nat where
  Max Z Z = Z
  Max Z b = b
  Max a Z = a
  Max (S a) (S b) = S (Max a b)

-- | c. Write a family to get the maximum natural in a list.
type family Maximum (xs :: [Nat]) :: Maybe Nat where
  Maximum '[] = Nothing
  Maximum (x ': xs) = Just (MaximumH x xs)

type family MaximumH (x :: Nat) (xs :: [Nat]) :: Nat where
  MaximumH x '[] = x
  MaximumH m (x ': xs) = MaximumH (Max m x) xs

{- FIVE -}

data Tree = Empty | Node Tree Nat Tree

-- | Write a type family to insert a promoted 'Nat' into a promoted 'Tree'.
type family Insert (n :: Nat) (t :: Tree) :: Tree where
  Insert n Empty = Node Empty n Empty
  Insert n (Node l m r) = InsertH (Compare n m) n m l r

type family InsertH (o :: Ordering) (n :: Nat) (m :: Nat) (l :: Tree) (r :: Tree) :: Tree where
  InsertH GT n m l r = Node l m (Insert n r)
  InsertH _ n m l r = Node (Insert n l) m r

{- SIX -}

-- | Write a type family to /delete/ a promoted 'Nat' from a promoted 'Tree'.
type family Delete (n :: Nat) (t :: Tree) :: Tree where
  Delete _ Empty = Empty
  Delete n (Node l m r) = DeleteH (Compare n m) n m l r

type family DeleteH (o :: Ordering) (n :: Nat) (m :: Nat) (l :: Tree) (r :: Tree) :: Tree where
  DeleteH LT n m l r = Node (Delete n l) m r
  DeleteH GT n m l r = Node l m (Delete n r)
  DeleteH EQ _ _ Empty r = r
  DeleteH EQ _ _ (Node ll lm lr) r = BuildL (DeleteFindMax ll lm lr) r

type family BuildL (l :: (Nat, Tree)) (r :: Tree) :: Tree where
  BuildL '(m, l) r = Node l m r

type family DeleteFindMax (l :: Tree) (m :: Nat) (r :: Tree) :: (Nat, Tree) where
  DeleteFindMax l m Empty = '(m, l)
  DeleteFindMax l m (Node rl rm rr) = DeleteFindMaxH l m (DeleteFindMax rl rm rr)

type family DeleteFindMaxH (l :: Tree) (m :: Nat) (r :: (Nat, Tree)) :: (Nat, Tree) where
  DeleteFindMaxH l m '(rm, r) = '(rm, Node l m r)

{- SEVEN -}

-- | With @TypeOperators@, we can use regular Haskell list syntax on the
-- type-level, which I think is /much/ tidier than anything we could define.
data HList (xs :: [Type]) where
  HNil :: HList '[]
  HCons :: x -> HList xs -> HList (x ': xs)

-- | Write a function that appends two 'HList's.
type family (xs :: [Type]) ++ (ys :: [Type]) :: [Type] where
  '[] ++ ys = ys
  (x ': xs) ++ ys = x ': (xs ++ ys)

(++) :: HList xs -> HList ys -> HList (xs ++ ys)
HNil ++ ys = ys
HCons x xs ++ ys = HCons x (xs Exercises.++ ys)

{- EIGHT -}

-- | Type families can also be used to build up constraints. There are, at this
-- point, a couple things that are worth mentioning about constraints:
--
-- - As we saw before, '()' is the empty constraint, which simply has "no
--   effect", and is trivially solved.
--
-- - Unlike tuples, constraints are "auto-flattened": ((a, b), (c, (d, ())) is
--   exactly equivalent to (a, b, c, d). Thanks to this property, we can build
--   up constraints using type families!
type family CAppend (x :: Constraint) (y :: Constraint) :: Constraint where
  CAppend x y = (x, y)

-- | a. Write a family that takes a constraint constructor, and a type-level
-- list of types, and builds a constraint on all the types.
type family Every (c :: Type -> Constraint) (x :: [Type]) :: Constraint where
  Every _ '[] = ()
  Every c (x ': xs) = (c x, Every c xs)

-- ...

-- | b. Write a 'Show' instance for 'HList' that requires a 'Show' instance for
-- every type in the list.
deriving instance (Every Show xs) => Show (HList xs)

-- >>> HCons "123" (HCons True (HCons 123 HNil))
-- HCons "123" (HCons True (HCons 123 HNil))

-- | c. Write an 'Eq' instance for 'HList'. Then, write an 'Ord' instance.
-- Was this expected behaviour? Why did we need the constraints?
deriving instance (Every Eq xs) => Eq (HList xs)

deriving instance (Every Eq xs, Every Ord xs) => Ord (HList xs)

{- NINE -}

-- | a. Write a type family to calculate all natural numbers up to a given
-- input natural.
type family UpTo (n :: Nat) :: [Nat] where
  UpTo n = UpToH '[] n

type family UpToH (xs :: [Nat]) (n :: Nat) :: [Nat] where
  UpToH acc Z = Z ': acc
  UpToH acc (S n) = UpToH (S n ': acc) n

-- | b. Write a type-level prime number sieve.
type family Prime (n :: Nat) :: [Nat] where
  Prime n = Seive (Drop (S (S Z)) (UpTo n))

type family Drop (n :: Nat) (xs :: [Nat]) :: [Nat] where
  Drop Z xs = xs
  Drop _ '[] = '[]
  Drop (S n) (x ': xs) = Drop n xs

type family Seive (xs :: [Nat]) :: [Nat] where
  Seive '[] = '[]
  Seive (x ': xs) = x ': Seive (DropMod x xs)

type family DropMod (n :: Nat) (xs :: [Nat]) :: [Nat] where
  DropMod _ '[] = '[]
  DropMod n (x ': xs) = DropModH n x n x (DropMod n xs)

type family DropModH (o :: Nat) (ox :: Nat) (n :: Nat) (x :: Nat) (xs :: [Nat]) :: [Nat] where
  DropModH o _ Z Z xs = xs
  DropModH o ox Z x xs = DropModH o ox o x xs
  DropModH o ox (S _) Z xs = ox ': xs
  DropModH o ox (S n) (S x) xs = DropModH o ox n x xs

-- | c. Why is this such hard work?
data (a :: [Nat]) :=: (b :: [Nat]) where
  Refl :: a :=: a

testPrime :: Prime S15 :=: [S2, S3, S5, S7, S11, S13]
testPrime = Refl

type S1 = S Z

type S2 = S S1

type S3 = S S2

type S4 = S S3

type S5 = S S4

type S6 = S S5

type S7 = S S6

type S8 = S S7

type S9 = S S8

type S10 = S S9

type S11 = S S10

type S12 = S S11

type S13 = S S12

type S14 = S S13

type S15 = S S14
