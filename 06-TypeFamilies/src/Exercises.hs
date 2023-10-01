{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

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
type family (a :: Nat) ** (b :: Nat) :: Nat where
  Z ** a = Z
  (S a) ** b = b + (a ** b)

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
append VNil b = b
append (VCons x xs) b = VCons x (append xs b)

-- | b. Write a 'flatMap' function that takes a @Vector n a@, and a function
-- @a -> Vector m b@, and produces a list that is the concatenation of these
-- results. This could end up being a deceptively big job.
flatMap :: Vector n a -> (a -> Vector m b) -> Vector (n ** m) b
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
type family All (bs :: [Bool]) :: Bool where
  All '[] = True
  All (x ': xs) = x && All xs

type family Filter (p :: k -> Bool) (xs :: [k]) :: [k] where
  Filter _ '[] = '[]
  Filter p (x ': xs) = Filter' (p x) x (Filter p xs)

type family Filter' (b :: Bool) (x :: k) (xs :: [k]) :: [k] where
  Filter' True x xs = x ': xs
  Filter' False _ xs = xs

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
  Max Z n = n
  Max n Z = n
  Max (S a) (S b) = S (Max a b)

-- | c. Write a family to get the maximum natural in a list.
type family Maximum (xs :: [Nat]) :: Maybe Nat where
  Maximum '[] = Nothing
  Maximum '[x] = Just x
  Maximum xs = Just (Maximum' xs)

type family Maximum' (xs :: [Nat]) :: Nat where
  Maximum' '[x] = x
  Maximum' (x ': xs) = Max x (Maximum' xs)

{- FIVE -}

data Tree = Empty | Node Tree Nat Tree

-- | Write a type family to insert a promoted 'Nat' into a promoted 'Tree'.
type family Insert (x :: Nat) (t :: Tree) :: Tree where
  Insert x Empty = Node Empty x Empty
  Insert x (Node l c r) = Insert' (Compare x c) x l c r

type family Insert' (o :: Ordering) (x :: Nat) (l :: Tree) (c :: Nat) (r :: Tree) where
  Insert' LT x l c r = Node (Insert x l) c r
  Insert' EQ x l c r = Node (Insert x l) c r
  Insert' GT x l c r = Node l c (Insert x r)

{- SIX -}

-- | Write a type family to /delete/ a promoted 'Nat' from a promoted 'Tree'.
type family Delete (x :: Nat) (t :: Tree) :: Tree where
  Delete _ Empty = Empty
  Delete x (Node l c r) = Delete' (Compare x c) x l c r

type family Delete' (o :: Ordering) (x :: Nat) (l :: Tree) (c :: Nat) (r :: Tree) :: Tree where
  Delete' LT x l c r = Node (Delete x l) c r
  Delete' GT x l c r = Node l c (Delete x r)
  Delete' EQ _ Empty _ r = r
  Delete' EQ _ (Node ll lc lr) _ r = Reconstruct (DeleteFindMax ll lc lr) r

type family Reconstruct (l :: (Nat, Tree)) (r :: Tree) :: Tree where
  Reconstruct '(x, l) r = Node l x r

type family DeleteFindMax (l :: Tree) (c :: Nat) (r :: Tree) :: (Nat, Tree) where
  DeleteFindMax l c Empty = '(c, l)
  DeleteFindMax l c (Node rl rc rr) = Reconstruct' l c (DeleteFindMax rl rc rr)

type family Reconstruct' (l :: Tree) (c :: Nat) (r :: (Nat, Tree)) :: (Nat, Tree) where
  Reconstruct' l c '(x, r) = '(x, Node l c r)

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

appendHList :: HList xs -> HList ys -> HList (xs ++ ys)
appendHList HNil ys = ys
appendHList (HCons x xs) ys = HCons x $ appendHList xs ys

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

class (Every c x) => EveryC c x

instance (Every c x) => EveryC c x

-- ...

-- | b. Write a 'Show' instance for 'HList' that requires a 'Show' instance for
-- every type in the list.
instance (EveryC Show xs) => Show (HList xs) where
  show HNil = "[]"
  show (HCons x xs) = show x ++ ':' : show xs

-- | c. Write an 'Eq' instance for 'HList'. Then, write an 'Ord' instance.
-- Was this expected behaviour? Why did we need the constraints?
instance (EveryC Eq xs) => Eq (HList xs) where
  HNil == HNil = True
  HCons x xs == HCons y ys = x == y && xs == ys

instance (EveryC Ord xs, EveryC Eq xs) => Ord (HList xs) where
  compare HNil HNil = EQ
  compare (HCons x xs) (HCons y ys) = compare x y <> compare xs ys

{- NINE -}

-- | a. Write a type family to calculate all natural numbers up to a given
-- input natural.
type family Upto (n :: Nat) :: [Nat] where
  Upto n = Upto' Z n

type family Upto' (a :: Nat) (b :: Nat) :: [Nat] where
  Upto' n n = '[n]
  Upto' a n = a ': Upto' (S a) n

-- | b. Write a type-level prime number sieve.

type family Sieve (n :: Nat) :: [Nat] where
  Sieve n = Sieve' (Drop (S (S Z)) (Upto n))

type family Sieve' (xs :: [Nat]) :: [Nat] where
  Sieve' '[] = '[]
  Sieve' (x ': xs) = x ': Sieve' (DropMod x xs)

type family DropMod (m :: Nat) (xs :: [Nat]) :: [Nat] where
  DropMod _ '[] = '[]
  DropMod m (x ': xs) = DropMod' (IsMod m m x) x (DropMod m xs)

type family DropMod' (b :: Bool) (x :: Nat) (xs :: [Nat]) :: [Nat] where
  DropMod' True x xs = xs
  DropMod' False x xs = x ': xs

type family IsMod (o :: Nat) (m :: Nat) (x :: Nat) :: Bool where
  IsMod _ Z Z = True
  IsMod _ (S _) Z = False
  IsMod o Z (S x) = IsMod o o (S x)
  IsMod o (S m) (S x) = IsMod o m x

type family Drop (a :: Nat) (b :: [k]) :: [k] where
  Drop Z xs = xs
  Drop _ '[] = '[]
  Drop (S n) (x ': xs) = Drop n xs

data x :==: y where
  Dict :: x :==: x

test :: Sieve S61 :==: '[S2, S3, S5, S7, S11, S13, S17, S19, S23, S29, S31, S37, S41, S43, S47, S53, S59, S61]
test = Dict

type S2 = S (S Z)
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
-- | c. Why is this such hard work?
