{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE GADTs         #-}
{-# LANGUAGE TypeFamilies  #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE PolyKinds #-}
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
  S a + b = S (a + b)

-- | b. Write a type family '**' that multiplies two naturals using '(+)'. Which
-- extension are you being told to enable? Why?

type family (a :: Nat) ** (b :: Nat) :: Nat where
  a ** Z = Z
  a ** S b = a + (a ** b)

data SNat (value :: Nat) where
  SZ :: SNat 'Z
  SS :: SNat n -> SNat ('S n)

-- | c. Write a function to add two 'SNat' values.

(+) :: SNat a -> SNat b -> SNat (a + b)
SZ + b = b
SS a + b = SS (a Exercises.+ b)

{- TWO -}

data Vector (count :: Nat) (a :: Type) where
  VNil  :: Vector 'Z a
  VCons :: a -> Vector n a -> Vector ('S n) a

-- | a. Write a function that appends two vectors together. What would the size
-- of the result be?

append :: Vector m a -> Vector n a -> Vector (m + n) a
append VNil ys = ys
append (VCons x xs) ys = VCons x (append xs ys)

-- | b. Write a 'flatMap' function that takes a @Vector n a@, and a function
-- @a -> Vector m b@, and produces a list that is the concatenation of these
-- results. This could end up being a deceptively big job.

flatMap :: Vector n a -> (a -> Vector m b) -> Vector (m ** n) b
flatMap VNil _ = VNil
flatMap (VCons x xs) f = append (f x) (flatMap xs f)


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

type family All (list :: [Bool]) :: Bool where
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
  Max a Z = a
  Max (S a) (S b) = S (Max a b)

-- | c. Write a family to get the maximum natural in a list.

type family Maximum (list :: [Nat]) :: Nat where
  Maximum (x ': xs) = Maximum' x xs

type family Maximum' (x :: Nat) (xs :: [Nat]) :: Nat where
  Maximum' x '[] = x
  Maximum' x (y ': ys) = Maximum' (Max x y) ys

{- FIVE -}

data Tree = Empty | Node Tree Nat Tree

-- | Write a type family to insert a promoted 'Nat' into a promoted 'Tree'.

type family Insert (a :: Nat) (t :: Tree) :: Tree where
  Insert a Empty = Node Empty a Empty
  Insert a (Node l c r) = Insert' (Compare a c) a (Node l c r)

type family Insert' (o :: Ordering) (a :: Nat) (t :: Tree) :: Tree where
  Insert' GT a (Node l c r) = Node l c (Insert a r)
  Insert' _ a (Node l c r) = Node (Insert a l) c r

{- SIX -}

-- | Write a type family to /delete/ a promoted 'Nat' from a promoted 'Tree'.

type family Delete (a :: Nat) (t :: Tree) :: Tree where
  Delete _ Empty = Empty
  Delete a (Node l c r) = Delete' (Compare a c) a (Node l c r)

type family Delete' (o :: Ordering) (a :: Nat) (t :: Tree) :: Tree where
  Delete' LT a (Node l c r) = Node (Delete a l) c r
  Delete' GT a (Node l c r) = Node l c (Delete a r)
  Delete' EQ _ (Node Empty _ r) = r
  Delete' EQ _ (Node l _ Empty) = l
  Delete' EQ _ (Node (Node ll lc lr) _ r) = Fix ll lc lr r

type family Fix (ll :: Tree) (lc :: Nat) (lr :: Tree) (r :: Tree) where
  Fix ll lc Empty r = Node ll lc r
  Fix ll lc (Node rl rc rr) r = Fix (Node ll lc rl) rc rr r

{- SEVEN -}

-- | With @TypeOperators@, we can use regular Haskell list syntax on the
-- type-level, which I think is /much/ tidier than anything we could define.

data HList (xs :: [Type]) where
  HNil  :: HList '[]
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

-- | b. Write a 'Show' instance for 'HList' that requires a 'Show' instance for
-- every type in the list.

instance Every Show xs => Show (HList xs) where
  show HNil = "[]"
  show (HCons x xs) = '[' : show x Prelude.++ show' xs Prelude.++ "]"
    where
      show' :: Every Show xs => HList xs -> String
      show' HNil = ""
      show' (HCons x xs) = ',' : show x Prelude.++ show' xs

-- | c. Write an 'Eq' instance for 'HList'. Then, write an 'Ord' instance.
-- Was this expected behaviour? Why did we need the constraints?

instance Every Eq xs => Eq (HList xs) where
  HNil == HNil = True
  HCons x xs == HCons y ys = x == y && xs == ys

instance (Every Eq xs, Every Ord xs) => Ord (HList xs) where
  compare HNil HNil = EQ
  compare (HCons x xs) (HCons y ys) = compare x y <> compare xs ys

{- NINE -}

-- | a. Write a type family to calculate all natural numbers up to a given
-- input natural.

-- | b. Write a type-level prime number sieve.

-- | c. Why is this such hard work?

type family Prime (n :: Nat) :: [Nat] where
  Prime n = Sieve (Drop (S (S Z)) (NatList Z n))

type family Drop (n :: Nat) (xs :: [k]) :: [k] where
  Drop Z xs = xs
  Drop _ '[] = '[]
  Drop (S n) (x ': xs) = Drop n xs

type family NatList (n :: Nat) (m :: Nat) :: [Nat] where
  NatList n Z = '[n]
  NatList n (S m) = n ': NatList ('S n) m

type family Sieve (xs :: [Nat]) :: [Nat] where
  Sieve '[] = '[]
  Sieve (x ': xs) = x ': Sieve (Sieve' x xs)

type family Sieve' (n :: Nat) (xs :: [Nat]) :: [Nat] where
  Sieve' _ '[] = '[]
  Sieve' n (x ': xs) = FilterDiv (DivZero n n x) n x xs

type family FilterDiv (b :: Bool) (n :: Nat) (x :: Nat) (xs :: [Nat]) :: [Nat] where
  FilterDiv 'True n _ xs = Sieve' n xs
  FilterDiv 'False n x xs = x ': Sieve' n xs

type family DivZero (n :: Nat) (n' :: Nat) (x :: Nat) :: Bool where
  DivZero _ 'Z 'Z = 'True
  DivZero _ ('S n) 'Z = 'False
  DivZero n 'Z ('S x) = DivZero n n ('S x)
  DivZero n ('S n') ('S x) = DivZero n n' x

type N0  = 'Z
type N1  = 'S N0
type N2  = 'S N1
type N3  = 'S N2
type N4  = 'S N3
type N5  = 'S N4
type N6  = 'S N5
type N7  = 'S N6
type N8  = 'S N7
type N9  = 'S N8
type N10 = 'S N9
type N11 = 'S N10
type N12 = 'S N11
type N13 = 'S N12
type N14 = 'S N13
type N15 = 'S N14
type N16 = 'S N15
type N17 = 'S N16
type N18 = 'S N17
type N19 = 'S N18
type N20 = 'S N19
type N21 = 'S N20
type N22 = 'S N21
type N23 = 'S N22
type N24 = 'S N23
type N25 = 'S N24
type N26 = 'S N25
type N27 = 'S N26
type N28 = 'S N27
type N29 = 'S N28
type N30 = 'S N29
type N31 = 'S N30

-- Little test...
data (x :: [Nat]) :~~: (y :: [Nat]) where
  NRefl :: x :~~: x

test :: Prime N31 :~~: '[ N2, N3, N5, N7, N11, N13, N17, N19, N23, N29, N31 ]
test = NRefl
