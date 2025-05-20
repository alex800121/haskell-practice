{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoStarIsType #-}

module Exercises where

import Data.Kind (Constraint, Type)
import GHC.TypeLits (ErrorMessage (..), TypeError)

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
  S a + b = S (a + b)

-- | b. Write a type family '**' that multiplies two naturals using '(+)'. Which
-- extension are you being told to enable? Why?
data SNat (value :: Nat) where
  SZ :: SNat 'Z
  SS :: SNat n -> SNat ('S n)

-- | c. Write a function to add two 'SNat' values.
addSNat :: SNat n -> SNat m -> SNat (n + m)
addSNat (SS n) m = SS (addSNat n m)
addSNat SZ m = m

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
type family (a :: Nat) * (b :: Nat) :: Nat where
  S a * b = b + (a * b)
  Z * b = Z

flatMap :: Vector n a -> (a -> Vector m b) -> Vector (n * m) b
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
  Max (S a) Z = S a
  Max Z b = b
  Max (S a) (S b) = S (Max a b)

-- | c. Write a family to get the maximum natural in a list.
type family Maximum (xs :: [Nat]) where
  Maximum '[x] = x
  Maximum (x ': xs) = Max x (Maximum xs)

{- FIVE -}

data Tree = Empty | Node Tree Nat Tree

-- | Write a type family to insert a promoted 'Nat' into a promoted 'Tree'.
type family Insert (n :: Nat) (t :: Tree) :: Tree where
  Insert n Empty = Node Empty n Empty
  Insert n (Node l c r) = InsertHelper (Compare n c) n l c r

type family InsertHelper (o :: Ordering) (n :: Nat) (l :: Tree) (c :: Nat) (r :: Tree) :: Tree where
  InsertHelper GT n l c r = Node l c (Insert n r)
  InsertHelper _ n l c r = Node (Insert n l) c r

{- SIX -}

-- | Write a type family to /delete/ a promoted 'Nat' from a promoted 'Tree'.
type family Delete (n :: Nat) (t :: Tree) :: Tree where
  Delete n Empty = Empty
  Delete n (Node l c r) = DeleteHelper (Compare n c) n l c r

type family DeleteHelper (o :: Ordering) (n :: Nat) (l :: Tree) (c :: Nat) (r :: Tree) where
  DeleteHelper LT n l c r = Node (Delete n l) c r
  DeleteHelper GT n l c r = Node l c (Delete n r)
  DeleteHelper EQ n l c r = FixTree l r

type family FixTree (l :: Tree) (r :: Tree) where
  FixTree Empty r = r
  FixTree (Node ll lc lr) r = RebuildL (GetMax ll lc lr) r

type family RebuildL (l :: (Nat, Tree)) (r :: Tree) :: Tree where
  RebuildL '(c, l) r = Node l c r

type family GetMax (l :: Tree) (c :: Nat) (r :: Tree) :: (Nat, Tree) where
  GetMax l c Empty = '(c, l)
  GetMax l c (Node rl rc rr) = RebuildR (GetMax rl rc rr) l c

type family RebuildR (r :: (Nat, Tree)) (l :: Tree) (c :: Nat) where
  RebuildR '(m, r) l c = '(m, Node l c r)

{- SEVEN -}

-- | With @TypeOperators@, we can use regular Haskell list syntax on the
-- type-level, which I think is /much/ tidier than anything we could define.
data HList (xs :: [Type]) where
  HNil :: HList '[]
  HCons :: x -> HList xs -> HList (x ': xs)

-- | Write a function that appends two 'HList's.
type family (xs :: [k]) ++ (ys :: [k]) :: [k] where
  '[] ++ ys = ys
  (x ': xs) ++ ys = x ': (xs ++ ys)

hAppend :: HList xs -> HList ys -> HList (xs ++ ys)
hAppend HNil ys = ys
hAppend (HCons x xs) ys = HCons x (hAppend xs ys)

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
instance (Every Show xs) => Show (HList xs) where
  show HNil = "[]"
  show (HCons x xs) = show x ++ " : " ++ show xs

-- | c. Write an 'Eq' instance for 'HList'. Then, write an 'Ord' instance.
-- Was this expected behaviour? Why did we need the constraints?
instance (Every Eq xs) => Eq (HList xs) where
  HCons x xs == HCons y ys = x == y && xs == ys
  HNil == HNil = True

{- NINE -}

-- | a. Write a type family to calculate all natural numbers up to a given
-- input natural.
type family UpTo (n :: Nat) :: [Nat] where
  UpTo n = UpToHelper '[] n

type family UpToHelper (xs :: [Nat]) (n :: Nat) :: [Nat] where
  UpToHelper xs Z = xs
  UpToHelper xs (S n) = UpToHelper (S n ': xs) n

-- | b. Write a type-level prime number sieve.
type family Sieve (n :: Nat) :: [Nat] where
  Sieve n = SieveHelper (Drop (S Z) (UpTo n))

type family SieveHelper (xs :: [Nat]) :: [Nat] where
  SieveHelper '[] = '[]
  SieveHelper (x ': xs) = x ': SieveHelper (Filter x xs)

type family Filter (x :: Nat) (xs :: [Nat]) :: [Nat] where
  Filter _ '[] = '[]
  Filter x (y ': ys) = DropBy (Mod x x y) y (Filter x ys)

type family Mod o x y :: Bool where
  Mod o Z Z = True
  Mod o (S x) Z = False
  Mod o Z (S y) = Mod o o (S y)
  Mod o (S x) (S y) = Mod o x y

type family DropBy (b :: Bool) (oy :: Nat) (ys :: [Nat]) :: [Nat] where
  DropBy True oy ys = ys
  DropBy False oy ys = oy ': ys

type family Drop (n :: Nat) (xs :: [k]) :: [k] where
  Drop Z xs = xs
  Drop _ '[] = '[]
  Drop (S n) (x ': xs) = Drop n xs

data x :=: y where
  Refl :: x :=: x

test ::
  [S2, S3, S5, S7, S11, S13, S17, S19, S23, S29, S31, S37, S41, S43, S47, S53, S59, S61, S67, S71, S73, S79]
    :=: Sieve S80
test = Refl

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
type S51 = S S50
type S52 = S S51
type S53 = S S52
type S54 = S S53
type S55 = S S54
type S56 = S S55
type S57 = S S56
type S58 = S S57
type S59 = S S58
type S60 = S S59
type S61 = S S60
type S62 = S S61
type S63 = S S62
type S64 = S S63
type S65 = S S64
type S66 = S S65
type S67 = S S66
type S68 = S S67
type S69 = S S68
type S70 = S S69
type S71 = S S70
type S72 = S S71
type S73 = S S72
type S74 = S S73
type S75 = S S74
type S76 = S S75
type S77 = S S76
type S78 = S S77
type S79 = S S78
type S80 = S S79

-- | c. Why is this such hard work?
