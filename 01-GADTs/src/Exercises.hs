{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
module Exercises where
import Data.Kind (Type)





{- ONE -}

-- | Let's introduce a new class, 'Countable', and some instances to match.
class Countable a where count :: a -> Int
instance Countable Int  where count   = id
instance Countable [a]  where count   = length
instance Countable Bool where count x = if x then 1 else 0

-- | a. Build a GADT, 'CountableList', that can hold a list of 'Countable'
-- things.

data CountableList where
  CountableNil :: CountableList
  CountableCons :: Countable a => a -> CountableList -> CountableList


-- | b. Write a function that takes the sum of all members of a 'CountableList'
-- once they have been 'count'ed.

countList :: CountableList -> Int
countList = go 0
  where
    go n CountableNil = n
    go n (CountableCons x xs) = go (n + count n) xs


-- | c. Write a function that removes all elements whose count is 0.

dropZero :: CountableList -> CountableList
dropZero = go id
  where
    go f CountableNil = f CountableNil
    go f (CountableCons x xs) = go (f . CountableCons x) xs

-- | d. Can we write a function that removes all the things in the list of type
-- 'Int'? If not, why not?

filterInts :: CountableList -> CountableList
filterInts = error "Contemplate me!"





{- TWO -}

-- | a. Write a list that can take /any/ type, without any constraints.

data AnyList where
  AnyNil :: AnyList
  AnyCons :: a -> AnyList -> AnyList

-- | b. How many of the following functions can we implement for an 'AnyList'?

reverseAnyList :: AnyList -> AnyList
reverseAnyList = go AnyNil
  where
    go l AnyNil = l
    go l (AnyCons x xs) = go (AnyCons x l) xs

filterAnyList :: (a -> Bool) -> AnyList -> AnyList
filterAnyList = undefined

lengthAnyList :: AnyList -> Int
lengthAnyList = go 0
  where
    go n AnyNil = n
    go n (AnyCons _ xs) = go (n + 1) xs

foldAnyList :: Monoid m => AnyList -> m
foldAnyList = undefined

isEmptyAnyList :: AnyList -> Bool
isEmptyAnyList AnyNil = True
isEmptyAnyList _ = False

instance Show AnyList where
  show xs = case xs of
    AnyNil -> "[]"
    AnyCons x xs -> "[Any" ++ show' xs ++ "]"
      where
        show' AnyNil = ""
        show' (AnyCons _ ys) = ", Any" ++ show' ys




{- THREE -}

-- | Consider the following GADT:

data TransformableTo output where
  TransformWith
    :: (input -> output)
    ->  input
    -> TransformableTo output

-- | ... and the following values of this GADT:

transformable1 :: TransformableTo String
transformable1 = TransformWith show 2.5

transformable2 :: TransformableTo String
transformable2 = TransformWith (uncurry (++)) ("Hello,", " world!")

-- | a. Which type variable is existential inside 'TransformableTo'? What is
-- the only thing we can do to it?
--
-- input

-- | b. Could we write an 'Eq' instance for 'TransformableTo'? What would we be
-- able to check?

instance Eq output => Eq (TransformableTo output) where
  TransformWith f1 x1 == TransformWith f2 x2 = f1 x1 == f2 x2

-- | c. Could we write a 'Functor' instance for 'TransformableTo'? If so, write
-- it. If not, why not?

instance Functor TransformableTo where
  fmap f (TransformWith g x) = TransformWith (f . g) x



{- FOUR -}

-- | Here's another GADT:

data EqPair where
  EqPair :: Eq a => a -> a -> EqPair

-- | a. There's one (maybe two) useful function to write for 'EqPair'; what is
-- it?

isEqual :: EqPair -> Bool
isEqual (EqPair a b) = a == b

-- | b. How could we change the type so that @a@ is not existential? (Don't
-- overthink it!)

data EqPair1 a where
  EqPair1 :: Eq a => a -> a -> EqPair1 a

-- | c. If we made the change that was suggested in (b), would we still need a
-- GADT? Or could we now represent our type as an ADT?

data EqPair2 a = Eq a => EqPair2 a a

{- FIVE -}

-- | Perhaps a slightly less intuitive feature of GADTs is that we can set our
-- type parameters (in this case @a@) to different types depending on the
-- constructor.

data MysteryBox a where
  EmptyBox  ::                                MysteryBox ()
  IntBox    :: Int    -> MysteryBox ()     -> MysteryBox Int
  StringBox :: String -> MysteryBox Int    -> MysteryBox String
  BoolBox   :: Bool   -> MysteryBox String -> MysteryBox Bool

-- | When we pattern-match, the type-checker is clever enough to
-- restrict the branches we have to check to the ones that could produce
-- something of the given type.

getInt :: MysteryBox Int -> Int
getInt (IntBox int _) = int

-- | a. Implement the following function by returning a value directly from a
-- pattern-match:

getInt' :: MysteryBox String -> Int
getInt' (StringBox _ x) = getInt x

-- | b. Write the following function. Again, don't overthink it!

countLayers :: MysteryBox a -> Int
countLayers EmptyBox = 0
countLayers (IntBox _ x) = 1 + countLayers x
countLayers (StringBox _ x) = 1 + countLayers x
countLayers (BoolBox _ x) = 1 + countLayers x

-- | c. Try to implement a function that removes one layer of "Box". For
-- example, this should turn a BoolBox into a StringBox, and so on. What gets
-- in our way? What would its type be?

type family Inner (a :: Type) :: Type where
  Inner Int = ()
  Inner String = Int
  Inner Bool = String

removeLayer :: MysteryBox a -> Maybe (MysteryBox (Inner a))
removeLayer EmptyBox = Nothing
removeLayer (IntBox _ x) = Just x
removeLayer (StringBox _ x) = Just x
removeLayer (BoolBox _ x) = Just x

{- SIX -}

-- | We can even use our type parameters to keep track of the types inside an
-- 'HList'!  For example, this heterogeneous list contains no existentials:

data HList a where
  HNil  :: HList ()
  HCons :: head -> HList tail -> HList (head, tail)

exampleHList :: HList (String, (Int, (Bool, ())))
exampleHList = HCons "Tom" (HCons 25 (HCons True HNil))

-- | a. Write a 'head' function for this 'HList' type. This head function
-- should be /safe/: you can use the type signature to tell GHC that you won't
-- need to pattern-match on HNil, and therefore the return type shouldn't be
-- wrapped in a 'Maybe'!

head :: HList (x, xs) -> x
head (HCons x _) = x

-- | b. Currently, the tuples are nested. Can you pattern-match on something of
-- type @HList (Int, String, Bool, ())@? Which constructor would work?

patternMatchMe :: HList (Int, String, Bool, ()) -> Int
patternMatchMe = undefined

-- | c. Can you write a function that appends one 'HList' to the end of
-- another? What problems do you run into?

type family Append (xs :: Type) (ys :: Type) :: Type where
  Append () ys = ys
  Append (x, xs) ys = (x, Append xs ys)

append :: HList xs -> HList ys -> HList (Append xs ys)
append HNil ys = ys
append (HCons x xs) ys = HCons x (append xs ys)

{- SEVEN -}

-- | Here are two data types that may help:

data Empty
data Branch left centre right

-- | a. Using these, and the outline for 'HList' above, build a heterogeneous
-- /tree/. None of the variables should be existential.

data HTree a where
  HTreeNil :: HTree Empty
  HTreeCons :: HTree left -> centre -> HTree right -> HTree (Branch left centre right)

-- | b. Implement a function that deletes the left subtree. The type should be
-- strong enough that GHC will do most of the work for you. Once you have it,
-- try breaking the implementation - does it type-check? If not, why not?

pruneLeft :: HTree (Branch left centre right) -> HTree (Branch Empty centre right)
pruneLeft (HTreeCons _ centre right) = HTreeCons HTreeNil centre right

-- | c. Implement 'Eq' for 'HTree's. Note that you might have to write more
-- than one to cover all possible HTrees. You might also need an extension or
-- two, so look out for something... flexible... in the error messages!
-- Recursion is your friend here - you shouldn't need to add a constraint to
-- the GADT!

instance (Eq (HTree left), Eq centre, Eq (HTree right)) => Eq (HTree (Branch left centre right)) where
  HTreeCons l1 c1 r1 == HTreeCons l2 c2 r2 = l1 == l2 && c1 == c2 && r1 == r2

instance Eq (HTree Empty) where
  _ == _ = True



{- EIGHT -}

-- | a. Implement the following GADT such that values of this type are lists of
-- values alternating between the two types. For example:
--
-- @
--   f :: AlternatingList Bool Int
--   f = ACons True (ACons 1 (ACons False (ACons 2 ANil)))
-- @

data AlternatingList a b where
  AlternatingNil :: AlternatingList a b
  AlternatingCons :: a -> AlternatingList b a -> AlternatingList a b

-- | b. Implement the following functions.

getFirsts :: AlternatingList a b -> [a]
getFirsts AlternatingNil = []
getFirsts (AlternatingCons x xs) = x : getSeconds xs

getSeconds :: AlternatingList a b -> [b]
getSeconds AlternatingNil = []
getSeconds (AlternatingCons _ xs) = getFirsts xs

-- | c. One more for luck: write this one using the above two functions, and
-- then write it such that it only does a single pass over the list.

foldValues :: (Monoid a, Monoid b) => AlternatingList a b -> (a, b)
foldValues AlternatingNil = (mempty, mempty)
foldValues (AlternatingCons x xs) = (x <> a, b)
  where
    (b, a) = foldValues xs



{- NINE -}

-- | Here's the "classic" example of a GADT, in which we build a simple
-- expression language. Note that we use the type parameter to make sure that
-- our expression is well-formed.

data Expr a where
  Equals    :: Expr Int  -> Expr Int            -> Expr Bool
  Add       :: Expr Int  -> Expr Int            -> Expr Int
  If        :: Expr Bool -> Expr a   -> Expr a  -> Expr a
  IntValue  :: Int                              -> Expr Int
  BoolValue :: Bool                             -> Expr Bool

-- | a. Implement the following function and marvel at the typechecker:

eval :: Expr a -> a
eval (IntValue i) = i
eval (BoolValue b) = b
eval (If c x y) = if eval c then eval x else eval y
eval (Add x y) = eval x + eval y
eval (Equals x y) = eval x == eval y

-- | b. Here's an "untyped" expression language. Implement a parser from this
-- into our well-typed language. Note that (until we cover higher-rank
-- polymorphism) we have to fix the return type. Why do you think this is?

data DirtyExpr
  = DirtyEquals    DirtyExpr DirtyExpr
  | DirtyAdd       DirtyExpr DirtyExpr
  | DirtyIf        DirtyExpr DirtyExpr DirtyExpr
  | DirtyIntValue  Int
  | DirtyBoolValue Bool

parse :: DirtyExpr -> Maybe (Expr Int)
parse (DirtyIntValue i) = Just (IntValue i)
parse (DirtyBoolValue _) = Nothing
parse (DirtyIf c x y) = parseBool c >>= \c -> parse x >>= \x -> parse y >>= \y -> return (If c x y)
parse (DirtyAdd x y) = parse x >>= \x -> parse y >>= \y -> return (Add x y)
parse (DirtyEquals _ _) = Nothing

parseBool :: DirtyExpr -> Maybe (Expr Bool)
parseBool (DirtyIntValue i) = Nothing
parseBool (DirtyBoolValue b) = Just (BoolValue b)
parseBool (DirtyIf c x y) = parseBool c >>= \c -> parseBool x >>= \x -> parseBool y >>= \y -> return (If c x y)
parseBool (DirtyAdd _ _) = Nothing
parseBool (DirtyEquals x y) = parse x >>= \x -> parse y >>= \y -> return (Equals x y)

-- | c. Can we add functions to our 'Expr' language? If not, why not? What
-- other constructs would we need to add? Could we still avoid 'Maybe' in the
-- 'eval' function?




{- TEN -}

-- | Back in the glory days when I wrote JavaScript, I could make a composition
-- list like @pipe([f, g, h, i, j])@, and it would pass a value from the left
-- side of the list to the right. In Haskell, I can't do that, because the
-- functions all have to have the same type :(

-- | a. Fix that for me - write a list that allows me to hold any functions as
-- long as the input of one lines up with the output of the next.

data TypeAlignedList a b where
  TypeAlignedNil :: TypeAlignedList a a
  TypeAlignedCons :: (a -> b) -> TypeAlignedList b c -> TypeAlignedList a c

-- | b. Which types are existential?

-- | c. Write a function to append type-aligned lists. This is almost certainly
-- not as difficult as you'd initially think.

composeTALs :: TypeAlignedList b c -> TypeAlignedList a b -> TypeAlignedList a c
composeTALs bc TypeAlignedNil = bc
composeTALs bc (TypeAlignedCons x xs) = TypeAlignedCons x (composeTALs bc xs)
