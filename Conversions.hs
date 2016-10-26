-- | Conversions for sequents.

module Conversions (Conv(..), convMP, antC, conclC, notC
                   ,thenC, allC, failC
                   ,orElseC, tryC
                   ,depthC
                   ,symC) where

import Control.Monad
import Data.Maybe

import Bootstrap hiding (matchMP, matchMPInst, concl, sequent)
import Sequent

-- | Conversions wrap functions which take terms and derive equations. Each
-- equation has an lhs which is the original term.
newtype Conv a = Conv { applyC :: Term a -> [Sequent a] }

-- | Use a conversion to rewrite a sequent
convMP :: (Ord a, Show a) => Conv a -> Sequent a -> [Sequent a]
convMP c thm = do eq  <- applyC c (concl thm)
                  let (l,r) = destEq (concl eq)
                  pure (mp (mp (inst2 l r (sequent eqMP)) eq) thm)

-- | Apply a conversion to the antcedent of a conditional
antC :: (Ord a, Show a) => Conv a -> Conv a
antC (Conv c) = Conv f
  where f (p :=>: q) =
          c p >>= maybeToList . matchMPInst (const q) (sequent substLeft)
        f _          = []

-- | Apply a conversion to the consequent of a conditional
conclC :: (Ord a, Show a) => Conv a -> Conv a
conclC (Conv c) = Conv f
  where f (p :=>: q) =
          c q >>= maybeToList . matchMPInst (const p) (sequent substRight)
        f _          = []

-- | Apply a conversion to the body of a negation
notC :: (Ord a, Show a) => Conv a -> Conv a
notC (Conv c) = Conv f
  where f (Not p) = c p >>= \eq ->
          let (l,r) = destEq (concl eq) in
          pure (mp (inst2 l r (sequent substNot)) eq)
        f _       = []

-- | Apply one conversion after another
thenC :: (Ord a,Show a) => Conv a -> Conv a -> Conv a
thenC c c' = Conv f
  where f t = do thm   <- applyC c t
                 let (x,y) = destEq (concl thm)
                 thm'  <- applyC c' y
                 let (y',z) = destEq (concl thm')
                 unless (y == y') (error ("Sequent thenC"))
                 pure (mp (mp (inst3 x y z (sequent trans)) thm) thm')

-- | The zero for orConv and identity for thenConv: always succeeds
allC :: Conv a
allC = Conv (\t -> return $ inst1 t (sequent reflEq))

-- | The identity for orConv and zero for thenConv: always fails
failC :: Conv a
failC = Conv (const [])

-- | Try the first conversion. If it produces no results, try the second.
orElseC :: Ord a => Conv a -> Conv a -> Conv a
orElseC c c' = Conv (\tm ->
                       let thms = applyC c tm in
                       if null thms then applyC c' tm else thms)

-- | Try a conversion. If it produces no results, do the trivial conversion.
tryC :: Ord a => Conv a -> Conv a
tryC = (`orElseC` allC)

-- | Apply a conversion bottom-up.
depthC :: (Ord a, Show a) => Conv a -> Conv a
depthC c = tryC (antC (depthC c))
           `thenC` tryC (conclC (depthC c))
           `thenC` tryC (notC (depthC c))
           `thenC` tryC c

-- | A conversion to switch the lhs and rhs of an equation.
symC :: Eq a => Conv a
symC = Conv c
  where c (Not ((p :=>: q) :=>: Not (r :=>: s))) | p == s && q == r =
          return $ inst2 p q (sequent symEq)
        c _                                      = []
