{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
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
type family a + b where
  Z + b = b
  S a + b = S (a + b)

-- | b. Write a type family '**' that multiplies two naturals using '(+)'. Which
-- extension are you being told to enable? Why?
type family a ** b where
  Z ** b = Z
  S a ** b = b + (a ** b)

data SNat (value :: Nat) where
  SZ :: SNat 'Z
  SS :: SNat n -> SNat ('S n)

-- | c. Write a function to add two 'SNat' values.
add :: SNat a -> SNat b -> SNat (a + b)
add SZ b = b
add (SS a) b = SS (add a b)

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
flatMap :: Vector n a -> (a -> Vector m b) -> Vector (n ** m) b
flatMap VNil _ = VNil
flatMap (VCons x xs) f = f x `append` flatMap xs f

{- THREE -}

-- | a. More boolean fun! Write the type-level @&&@ function for booleans.
type family (a :: Bool) && (b :: Bool) :: Bool where
  False && _ = False
  True && b = b

-- | b. Write the type-level @||@ function for booleans.
type family (a :: Bool) || (b :: Bool) :: Bool where
  True || _ = True
  False || b = b

-- | c. Write an 'All' function that returns @'True@ if all the values in a
-- type-level list of boleans are @'True@.
type family All (xs :: [Bool]) :: Bool where
  All '[] = True
  All (x ': xs) = x && All xs

{- FOUR -}

-- | a. Nat fun! Write a type-level 'compare' function using the promoted
-- 'Ordering' type.
type family Compare (a :: Nat) (b :: Nat) :: Ordering where
  Compare Z Z = EQ
  Compare (S _) Z = GT
  Compare Z (S _) = LT
  Compare (S a) (S b) = Compare a b

-- | b. Write a 'Max' family to get the maximum of two natural numbers.
type family Max (a :: Nat) (b :: Nat) :: Nat where
  Max Z b = b
  Max (S a) Z = S a
  Max (S a) (S b) = S (Max a b)

-- | c. Write a family to get the maximum natural in a list.
type family Maximum (xs :: [Nat]) :: Maybe Nat where
  Maximum '[] = Nothing
  Maximum (x ': xs) = Just (MaximumH x xs)

type family MaximumH (x :: Nat) (xs :: [Nat]) :: Nat where
  MaximumH x '[] = x
  MaximumH x (y ': ys) = MaximumH (Max x y) ys

{- FIVE -}

data Tree = Empty | Node Tree Nat Tree

-- | Write a type family to insert a promoted 'Nat' into a promoted 'Tree'.
type family Insert (n :: Nat) (t :: Tree) :: Tree where
  Insert n Empty = Node Empty n Empty
  Insert n (Node l c r) = InsertH (Compare n c) n l c r

type family InsertH (o :: Ordering) (n :: Nat) (l :: Tree) (c :: Nat) (r :: Tree) :: Tree where
  InsertH GT n l c r = Node l c (Insert n r)
  InsertH _ n l c r = Node (Insert n l) c r

{- SIX -}

-- | Write a type family to /delete/ a promoted 'Nat' from a promoted 'Tree'.
type family Delete (n :: Nat) (t :: Tree) :: Tree where
  Delete n Empty = Empty
  Delete n (Node l c r) = DeleteH (Compare n c) n l c r

type family DeleteH (o :: Ordering) (n :: Nat) (l :: Tree) (c :: Nat) (r :: Tree) :: Tree where
  DeleteH LT n l c r = Node (Delete n l) c r
  DeleteH GT n l c r = Node l c (Delete n r)
  DeleteH EQ n l c r = Merge l r

type family Merge (l :: Tree) (r :: Tree) :: Tree where
  Merge Empty r = r
  Merge (Node ll lc lr) r = MergeH (FindMax ll lc lr) r

type family MergeH (l :: (Tree, Nat)) (r :: Tree) :: Tree where
  MergeH '(l, c) r = Node l c r

type family FindMax (l :: Tree) (c :: Nat) (r :: Tree) :: (Tree, Nat) where
  FindMax l c Empty = '(l, c)
  FindMax l c (Node rl rc rr) = FindMaxH l c (FindMax rl rc rr)

type family FindMaxH (l :: Tree) (c :: Nat) (r :: (Tree, Nat)) :: (Tree, Nat) where
  FindMaxH l c '(r, m) = '(Node l c r, m)

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

appendH :: HList xs -> HList ys -> HList (xs ++ ys)
appendH HNil ys = ys
appendH (HCons x xs) ys = HCons x (appendH xs ys)

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

-- | b. Write a 'Show' instance for 'HList' that requires a 'Show' instance for
-- every type in the list.
instance (Every Show xs) => Show (HList xs) where
  show HNil = "Nil"
  show (HCons x xs) = show x ++ " : " ++ show xs

-- | c. Write an 'Eq' instance for 'HList'. Then, write an 'Ord' instance.
-- Was this expected behaviour? Why did we need the constraints?
instance (Every Eq xs) => Eq (HList xs) where
  HNil == HNil = True
  HCons x xs == HCons y ys = x == y && xs == ys

instance (Every Eq xs, Every Ord xs) => Ord (HList xs) where
  compare HNil HNil = EQ
  compare (HCons x xs) (HCons y ys) = compare x y <> compare xs ys

{- NINE -}

-- | a. Write a type family to calculate all natural numbers up to a given
-- input natural.
type family UpTo (n :: Nat) :: [Nat] where
  UpTo n = UpToH Z n

type family UpToH (a :: Nat) (n :: Nat) :: [Nat] where
  UpToH a Z = '[a]
  UpToH a (S n) = a ': UpToH (S a) n

-- | b. Write a type-level prime number sieve.
type family PrimeUpTo (n :: Nat) :: [Nat] where
  PrimeUpTo n = Seive (Drop S2 (UpTo n))

type family Drop (n :: Nat) (xs :: [k]) :: [k] where
  Drop Z xs = xs
  Drop (S n) (_ ': xs) = Drop n xs

type family Seive (ns :: [Nat]) :: [Nat] where
  Seive '[] = '[]
  Seive (x ': xs) = x ': Seive (SeiveH x xs)

type family SeiveH (n :: Nat) (ns :: [Nat]) :: [Nat] where
  SeiveH n '[] = '[]
  SeiveH n (x ': xs) = SeiveHH (Remove n n x) x (SeiveH n xs)

type family Remove (o :: Nat) (n :: Nat) (x :: Nat) :: Bool where
  Remove o Z Z = True
  Remove o Z (S x) = Remove o o (S x)
  Remove o (S n) Z = False
  Remove o (S n) (S x) = Remove o n x

type family SeiveHH (b :: Bool) (x :: Nat) (xs :: [Nat]) :: [Nat] where
  SeiveHH True _ xs = xs
  SeiveHH False x xs = x ': xs

-- | c. Why is this such hard work?
data (x :: k0) :=: (y :: k1) where
  Refl :: x :=: x

testPrime ::
  PrimeUpTo S50
    :=: '[S2, S3, S5, S7, S11, S13, S17, S19, S23, S29, S31, S37, S41, S43, S47]
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

type S16 = S S15

type S17 = S S16

type S18 = S S17

type S19 = S S18

type S20 = S S19

type S21 = S S20

type S22 = S S21

type S23 = S S22

type S24 = S S23

type S25 = S S24

type S26 = S S25

type S27 = S S26

type S28 = S S27

type S29 = S S28

type S30 = S S29

type S31 = S S30

type S32 = S S31

type S33 = S S32

type S34 = S S33

type S35 = S S34

type S36 = S S35

type S37 = S S36

type S38 = S S37

type S39 = S S38

type S40 = S S39

type S41 = S S40

type S42 = S S41

type S43 = S S42

type S44 = S S43

type S45 = S S44

type S46 = S S45

type S47 = S S46

type S48 = S S47

type S49 = S S48

type S50 = S S49
