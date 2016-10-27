{-# LANGUAGE DeriveFunctor #-}
-- | Embed a sequent calculus for propositional logic

module Sequent (module Utils
               ,Sequent, assms, concl, sequent, seqThm
               ,assume, charge, discharge, weaken
               ,mp
               ,inst1, inst2, inst3, instM
               ,matchMPInst) where

import Data.List
import Data.Maybe

import qualified Bootstrap as B
import BootstrapConversions hiding (matchMPInst)
import qualified Proposition as P
import Utils hiding (mp, inst1, inst2, inst3, instM)
import qualified Utils as U

-- | A sequent has the form Γ ⊦ P
data Sequent a = Sequent Int (Theorem a) deriving (Eq, Functor)

instance Show a => Show (Sequent a) where
  show s = listWords (map show $ assms s) ++ " |- " ++ show (concl s)
    where listWords ws = concat $ intersperse ", " ws

stripRight n p | n <= 0 = [p]
stripRight n (p :=>: q) = p : stripRight (n-1) q

-- | assms Γ ⊦ P yields Γ
assms :: Sequent a -> [Term a]
assms (Sequent n thm) = take n $ stripRight n $ termOfTheorem thm

-- | concl Γ ⊦ P yields P
concl :: Sequent a -> Term a
concl (Sequent n thm) = last $ stripRight n $ termOfTheorem thm

-- | Turn a sequent into a theorem by discharging all assumptions
seqThm :: Sequent a -> Theorem a
seqThm (Sequent _ thm) = thm

-- | Turn a theorem into a sequent of no assumptions.
sequent :: Theorem a -> Sequent a
sequent thm = Sequent 0 thm

-- | assume P yields {P} ⊦ P
assume :: Term a -> Sequent a
assume p = Sequent 1 (U.inst1 p B.truthThm)

triangle :: a -> [[a]]
triangle = inits . repeat

-- A conversion to move the mth hypothesis up n places
pushAssum :: (Show a, Eq a) => Int -> Int -> Conv a
pushAssum m n = foldl (.) id (replicate m conclC)
                $ everyC [ foldr ($) swapC cc
                         | cc <- take n $ triangle conclC ]

-- Add a hypothesis to a theorem
addFrontAsm :: (Eq a, Show a) => Term a -> Theorem a -> Theorem a
addFrontAsm asm thm = U.mp (U.inst2 (termOfTheorem thm) asm axiom1) thm

-- | discharge P (Γ ⊦ Q) yields P - {Γ} ⊦ P → Q
discharge :: (Eq a, Show a) => Term a -> Sequent a -> Sequent a
discharge asm s@(Sequent n thm) = f (elemIndex asm $ assms s)
  where f (Just m) = case convMP (pushAssum lassms rassms) thm of
          [thm'] -> Sequent (n-1) thm'
          _      -> error "Discharge"
          where lassms = m
                rassms = n - m - 1
        f Nothing = discharge asm
                    (Sequent (n + 1) (addFrontAsm asm thm))

-- | charge Γ ⊦ P → Q yields Γ ∪ {P} ⊦ Q
charge :: Sequent a -> Sequent a
charge (Sequent n concl) =
  case termOfTheorem concl of
  p :=>: q -> Sequent (n+1) concl

-- | weaken P (Γ ⊦ Q) yields {P} ∪ Γ ⊦ Q
weaken :: (Ord a, Show a) => Term a -> Sequent a -> Sequent a
weaken asm s | asm `elem` assms s = s
weaken asm s@(Sequent n thm)      =
  Sequent (n+1) (fromMaybe (head $ convMP (pushAssum 0 n) (addFrontAsm asm thm))
                 (do i <- findIndex (asm <) (assms s)
                     listToMaybe $ convMP (pushAssum 0 i) (addFrontAsm asm thm)))


-- Uncurry the first n hypotheses of a conditional
uncurryN :: (Eq a, Show a) => Int -> Conv a
uncurryN n | n <= 1 = allC
uncurryN n = everyC (replicate (n-1) uncurry2)

-- Inverse of uncurryN
curryN :: (Eq a, Show a) => Int -> Conv a
curryN n | n<= 1 = allC
curryN n = everyC (replicate (n-1) curry2)

-- | mp (Δ ⊦ P → Q) (Γ ⊦ P) yields Γ ∪ Δ ⊦ Q
mp :: (Ord a, Show a) => Sequent a -> Sequent a -> Sequent a
mp (Sequent 0 imp) (Sequent 0 ant) =
  case P.mp imp ant of
  Nothing -> error ("Sequent MP: " ++ show [imp,ant])
  Just c  -> Sequent 0 c
mp imps@(Sequent _ imp) ants@(Sequent _ ant) = head $ do
  impT' <- convMP (uncurryN n) impT
  antT' <- convMP (uncurryN n) antT
  case termOfTheorem impT' of
    (p :=>: q :=>: r) ->
      let thm = U.mp (U.inst3 p q r axiom2) impT'
          c   = U.mp thm antT'
      in Sequent n <$> (convMP (curryN n) c)
    _ -> error ("Sequent MP: " ++ show [concl imps,concl ants])
  where Sequent n impT = foldl (flip weaken) imps (assms ants)
        Sequent _ antT = foldl (flip weaken) ants (assms imps)

-- | Given Γ ⊦ P → Q and Δ ⊦ R, attempt to match P and R, and then apply MP using an
-- instantiation for the other variables to obtain Γ ∪ Δ ⊦ R'.
matchMPInst :: (Eq a, Ord b, Show b) =>
                (a -> Term b) -> Sequent a -> Sequent b -> Maybe (Sequent b)
matchMPInst inst imp ant =
  case concl imp of
  p :=>: q -> do
    bindings <- match p (concl ant)
    pure (mp (instM inst bindings imp) ant)

-- | Instantiate variables in a sequent based additionally on an association list.
instM :: Eq a => (a -> Term b) -> [(a, Term b)] -> Sequent a -> Sequent b
instM instantiation bindings (Sequent n thm) =
  Sequent n (U.instM instantiation bindings thm)

-- | Instantiate the variable in a theorem drawn from a singleton alphabet.
inst1 :: Term a -> Sequent () -> Sequent a
inst1 p = instM (const p) []

-- | Instantiate the two variables in a theorem drawn from the alphabet of two
-- symbols.
inst2 :: Term a -> Term a -> Sequent Two -> Sequent a
inst2 x y = instM (splitTwo x y) []

-- | Instantiate the three variables in a theorem drawn from the alphabet of three
-- symbols.
inst3 :: Term a -> Term a -> Term a -> Sequent Three -> Sequent a
inst3 p q r = instM (splitThree p q r) []
