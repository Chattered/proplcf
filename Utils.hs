module Utils (module Proposition, (/\), (\/), (<=>)
             ,destAnd, destEq, truth, false
             ,splitTwo, splitThree
             ,inst1, inst2, inst3, mp
             ,match, instM) where

import Control.Monad
import Data.Maybe (mapMaybe)

import Instances
import Proposition hiding (mp)
import qualified Proposition as P

infixl 4 \/
infixl 5 /\

-- | Syntax sugar for disjunction
(\/) :: Term a -> Term a -> Term a
p \/ q = Not p :=>: q

-- | Syntax sugar for conjunction
(/\) :: Term a -> Term a -> Term a
p /\ q  = Not (p :=>: Not q)

-- | Syntax sugar for equivalence
(<=>) :: Term a -> Term a -> Term a
p <=> q = (p :=>: q) /\ (q :=>: p)

-- | A destructor for conjunction
destAnd :: Term a -> (Term a, Term a)
destAnd (Not (p :=>: Not q)) = (p,q)

-- | A destructor for equality
destEq :: Term a -> (Term a, Term a)
destEq pq = let (p :=>: q, _) = destAnd pq in (p,q)

-- | Syntax sugar for truth
truth :: a -> Term a
truth x = Var x :=>: Var x

-- | Syntax sugar for false
false :: a -> Term a
false = Not . truth

-- | Exception throwing modus ponens
mp :: (Eq a, Show a) => Theorem a -> Theorem a -> Theorem a
mp imp ant =
  case P.mp imp ant of
  Just consequent -> consequent
  _ -> error ("MP: " ++ show [imp,ant])

-- | Instantiate the variable in a theorem drawn from a singleton alphabet.
inst1 :: Term a -> Theorem () -> Theorem a
inst1 p = inst (const p)

splitTwo :: a -> a -> Two -> a
splitTwo x y X = x
splitTwo x y Y = y

-- | Instantiate the two variables in a theorem drawn from the alphabet of two
-- symbols.
inst2 :: Term a -> Term a -> Theorem Two -> Theorem a
inst2 x y = inst (splitTwo x y)

splitThree :: a -> a -> a -> Three -> a
splitThree p q r P = p
splitThree p q r Q = q
splitThree p q r R = r

-- | Instantiate the three variables in a theorem drawn from the alphabet of three
-- symbols.
inst3 :: Term a -> Term a -> Term a -> Theorem Three -> Theorem a
inst3 p q r = inst (splitThree p q r)

-- | Instantiate variables in a theorem based additionally on an association list.
instM :: Eq a => (a -> Term b) -> [(a, Term b)] -> Theorem a -> Theorem b
instM dflt l = inst f
  where f p = maybe (dflt p) id (lookup p l)

-- | Match terms.
match :: (Eq a, Eq b) => Term a -> Term b -> Maybe [(a, Term b)]
match = m []
  where m is (Var p) t =
          case lookup p is of
            Nothing -> pure ((p, t) : is)
            Just t' | t == t' -> pure is
            _ -> mzero
        m is (Not t) (Not t')        = m is t t'
        m is (a :=>: c) (a' :=>: c') = m is a a' >>= \is' -> m is' c c'
        m _ _ _                      = mzero
