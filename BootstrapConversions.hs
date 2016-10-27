-- | Basic conversions and conversionals. Just enough to embed a Sequent calculus.

module BootstrapConversions where

import Control.Monad
import Data.Maybe

import Bootstrap hiding (matchMP, matchMPInst)
import Utils

-- | Given ⊦ P → Q and ⊦ R, attempt to match P and R, and then apply MP using an
-- instantiation for the other variables.
matchMPInst :: (Eq a, Eq b, Show b) =>
               (a -> Term b) -> Theorem a -> Theorem b -> [Theorem b]
matchMPInst inst imp ant =
  case (termOfTheorem imp, termOfTheorem ant) of
      (p :=>: q, p') ->
        maybeToList (fmap (\is -> mp (instM inst is imp) ant) (match p p'))
      _ -> []

-- | Conversions wrap functions which take terms and derive equations. Each
-- equation has an lhs which is the original term.
newtype Conv a = Conv { applyC :: Term a -> [Theorem a] }

-- | Use a conversion to rewrite a theorem.
convMP :: (Eq a, Show a) => Conv a -> Theorem a -> [Theorem a]
convMP c thm = do eq <- applyC c (termOfTheorem thm)
                  let (l,r) = destEq (termOfTheorem eq)
                  pure (mp (mp (inst2 l r eqMP) eq) thm)

-- | Apply a conversion to the consequent of a conditional.
conclC :: (Eq a, Show a) => Conv a -> Conv a
conclC (Conv c) = Conv f
  where f (p :=>: q) = c q >>= matchMPInst (const p) substRight
        f _          = []

-- | Apply one conversion after another.
thenC :: (Eq a, Show a) => Conv a -> Conv a -> Conv a
thenC c c' = Conv f
  where f t = do thm   <- applyC c t
                 let (x,y) = destEq (termOfTheorem thm)
                 thm'  <- applyC c' y
                 let (y',z) = destEq (termOfTheorem thm')
                 unless (y == y') (error "thenC")
                 pure (mp (mp (inst3 x y z trans) thm) thm')

-- | The zero for orConv and identity for thenConv: always succeeds.
allC :: Conv a
allC = Conv (\t -> return $ inst1 t reflEq)

-- | The identity for orConv and zero for thenConv: always fails.
failC :: Conv a
failC = Conv (const [])

-- | Apply all conversions in a sequence.
everyC :: (Eq a, Show a) => [Conv a] -> Conv a
everyC = foldl thenC allC

-- | Swap the first two hypotheses of a conditional.
swapC :: Conv a
swapC = Conv c
  where c (p :=>: q :=>: r) = return $ inst3 p q r swapT
        c _                 = []

-- | Uncurry the first two hypotheses of a conditional
uncurry2 :: Conv a
uncurry2 = Conv c
  where c (p :=>: q :=>: r) = return $ inst3 p q r Bootstrap.uncurry
        c _                 = []

-- | A conversion to switch the lhs and rhs of an equation.
symC :: Eq a => Conv a
symC = Conv c
  where c (Not ((p :=>: q) :=>: Not (r :=>: s))) | p == s && q == r =
          return $ inst2 p q symEq
        c _                                      = []

-- | Curry the first hypothesis
curry2 :: Conv a
curry2 = Conv c
  where c (Not (p :=>: Not q) :=>: r) =
          return $ inst3 p q r (head $ convMP symC Bootstrap.uncurry)
        c _                           = []
