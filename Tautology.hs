module Tautology where

import Data.Foldable

import Data.List
import Data.Maybe
import Bootstrap (conjI, truthThm, u, x, y, lemma1, notElim, dblNegElim
                 ,dblNegIntro, eqMP)
import qualified Bootstrap as B
import Sequent
import Conversions

-- | Conjunction introduction
conj :: (Ord a, Show a) => Sequent a -> Sequent a -> Sequent a
conj p q = mp (mp (inst2 (concl p) (concl q) (sequent conjI)) p) q

-- | Case analysis
cases :: (Ord a, Show a) => Term a -> Sequent a -> Sequent a -> Sequent a
cases p pCase notPCase =
  let q = concl pCase in
  let pThm = discharge p pCase in
  let notPThm = discharge (Not p) notPCase in
  if concl pCase == concl notPCase then
    mp (mp (inst2 p q (sequent B.cases)) pThm) notPThm
  else error ("cases" ++ show [pCase, notPCase])

-- | ⊢ ⊥ → P
eqElimThm :: Sequent Two
eqElimThm = mp (inst2 (fmap (const X) (truth X)) y (sequent notElim))
               (inst1 x (sequent truthThm))

-- | P ⊢ P ↔ ⊤
eqTruth :: Sequent Two
eqTruth = conj (discharge y (inst1 x (sequent truthThm)))
               (discharge (fmap (const X) (truth X)) (assume y))

-- | ¬P ⊢ P ↔ ⊥
eqFalse :: Sequent Two
eqFalse = conj (charge (inst2 y x (sequent lemma1))) (weaken (Not y) eqElimThm)

-- | Add a condition to the conclusion of a sequent.
addHyp :: (Show a, Ord a) => Term a -> Sequent a -> Sequent a
addHyp t = discharge t . weaken t

-- | ⊢ (⊤ → P) ↔ P
truth1 :: Sequent Two
truth1 =
  let l = discharge (truth X :=>: y) (mp (assume (truth X :=>: y))
                                      (inst1 x (sequent truthThm))) in
  let r = discharge y (addHyp (truth X) (assume y)) in
  conj l r

-- | ⊢ (⊥ → P) ↔ ⊤
truth2 :: Sequent Two
truth2 =
  let l = addHyp ((false X) :=>: y) (inst1 x (sequent truthThm)) in
  let r = addHyp (truth X) eqElimThm in
  conj l r

-- | ⊢ ¬⊥ ↔ ⊤
truth3 :: Sequent ()
truth3 =
  let l = inst1 (truth ()) (sequent dblNegElim) in
  let r = inst1 (truth ()) (sequent dblNegIntro) in
  conj l r

-- | Send Γ ⊢ P ↔ ⊤ to Γ ⊢ P
eqTElim :: (Show a, Ord a) =>
           Sequent (Maybe a) -> Maybe (Sequent (Maybe a))
eqTElim thm = do
  symthm <- listToMaybe (convMP symC thm)
  let (_,r) = destEq (concl symthm)
  let eqMP' = inst2 (truth Nothing) r (sequent eqMP)
  pure (mp (mp eqMP' symthm) (inst1 (pure Nothing) (sequent truthThm)))

-- | A tautology verifier.
tautology :: (Show b, Ord b) => Term b -> Maybe (Theorem b)
tautology tm =
  let jtm = Just <$> tm in
  let conv = (evalRow (nub $ toList jtm) []) in
  let seq = listToMaybe (applyC conv jtm) >>= eqTElim in
  let thm = seqThm <$> seq in
  (fmap.fmap) (\(Just x) -> x) thm
  where evalRow [] row =
          depthC (foldr orElseC allC (fmap matchConv' row)) `thenC` evalTaut
        evalRow (v:vs) row = Conv $ \tm ->
          let assumeV      = inst2 (pure Nothing) (pure v) eqTruth in
          let denyV        = inst2 (pure Nothing) (pure v) eqFalse in
          let assumeCase   = head (applyC (evalRow vs (assumeV : row)) tm) in
          let denyCase     = head (applyC (evalRow vs (denyV : row)) tm) in
          [cases (pure v) assumeCase denyCase]
        evalTaut = depthC (foldr orElseC allC convs)
          where convs = fmap matchConv [truth1, truth2]
                        ++ fmap matchConv [truth3]
        matchConv thm = Conv $ \tm ->
          let (l,r) = destEq (concl thm) in
          fmap (\insts -> instM undefined insts thm) (maybeToList (match l tm))
        matchConv' thm = Conv $ \tm ->
          let (l,r) = destEq (concl thm) in
          if tm == l then [thm] else []
