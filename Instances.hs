-- | Instances for Proposition.hs. This is code that is not trustworthy enough to
-- be in the kernel, and we limit our use of automatic Deriving in Proposition.hs to
-- just Eq. Exercise for the reader: if Theorem automatically derived Traversable,
-- how would this make the logic unsound?

module Instances where

import Control.Monad
import Data.Function
import Data.Monoid
import Data.Traversable

import Proposition

instance Functor Term where
  fmap = liftM

instance Applicative Term where
  pure = Var
  (<*>) = liftM2 ($)

instance Monad Term where
  tm >>= f = instTerm f tm

instance Foldable Term where
  foldMap = foldMapDefault

instance Traversable Term where
  traverse f (Var x)    = Var <$> f x
  traverse f (Not t)    = Not <$> traverse f t
  traverse f (a :=>: c) = (:=>:) <$> traverse f a <*> traverse f c

instance Ord a => Ord (Term a) where
  compare (Var x) (Var y)         = compare x y
  compare (Var x) _               = LT
  compare _ (Var y)               = GT
  compare (Not t) (Not t')        = compare t t'
  compare (Not _) _               = LT
  compare _ (Not _)               = GT
  compare (a :=>: c) (a' :=>: c') = compare a a' <> compare c c'

instance Show a => Show (Term a) where
  showsPrec _ (Var p) s             = showsPrec 11 p s
  showsPrec _ (Not (Var p)) s       = "~" ++ showsPrec 11 p s
  showsPrec _ (Not (Not p)) s       = "~" ++ shows (Not p) s
  showsPrec _ (Not p) s             = "~(" ++ shows p (")" ++ s)
  showsPrec _ ((p :=>: q) :=>: r) s =
    "(" ++ shows (p :=>: q) (")" ++ " ==> " ++ shows r s)
  showsPrec _ (p :=>: q) s          = shows p (" ==> " ++ shows q s)

instance Functor Theorem where
  fmap f = inst (pure . f)

instance Foldable Theorem where
  foldMap f = foldMap f . termOfTheorem

instance Eq a => Eq (Theorem a) where
  (==) = (==) `on` termOfTheorem

instance Show a => Show (Theorem a) where
  show thm = "|- " ++ show (termOfTheorem thm)

instance Eq Two where
  x == y = compare x y == EQ

instance Ord Two where
  compare X X = EQ
  compare X Y = LT
  compare Y X = GT
  compare Y Y = EQ

instance Show Two where
  show X = "X"
  show Y = "Y"

instance Eq Three where
  x == y = compare x y == EQ

instance Ord Three where
  compare P P = EQ
  compare P _ = LT
  compare _ P = GT
  compare Q Q = EQ
  compare Q _ = LT
  compare _ Q = GT
  compare R R = EQ

instance Show Three where
  show P = "P"
  show Q = "Q"
  show R = "R"
