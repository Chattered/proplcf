-- Sequent calculus embedding

module Sequent where

import Data.List
import Propositional
import Utils
import Conversions
import Data.Maybe
import qualified Bootstrap as B

data Sequent = Sequent Int (Theorem String) deriving (Eq, Ord)

printSeq s = listWords (map printTerm $ assms s) ++ " |- " ++ printTerm (concl s)
    where listWords ws = concat $ intersperse ", " ws
             
stripRight n p | n <= 0 = [p]
stripRight n (p :=>: q) = p : stripRight (n-1) q

-- assms Γ ⊦ P yields Γ
assms :: Sequent -> [Term String]
assms (Sequent n thm) = take n $ stripRight n $ theoremTerm thm

-- concl Γ ⊦ P yields P
concl :: Sequent -> Term String
concl (Sequent n thm) = last $ stripRight n $ theoremTerm thm

-- Turn a sequent into a theorem by discharging all assumptions
seqThm :: Sequent -> Theorem String
seqThm (Sequent _ thm) = thm

sequent :: Theorem String -> Sequent
sequent thm = Sequent 0 thm

axiom1S = sequent axiom1
axiom2S = sequent axiom2
axiom3S = sequent axiom3          
                          
-- assume P yields {P} ⊦ P
assume :: Term String -> Sequent 
assume p = Sequent 1 (instL [p] B.truth)

triangle :: a -> [[a]]
triangle = inits . repeat

-- A conversion to move the mth hypothesis up n places
pushAssum m n = foldl (.) id (replicate m conclC) 
                $ everyC [ foldr ($) swapC cc 
                         | cc <- take n $ triangle conclC ]
                
-- Add a hypothesis to a theorem
addFrontAsm :: Term String -> Theorem String -> Theorem String
addFrontAsm asm thm = head $ mp (instL [theoremTerm thm, asm] axiom1) thm

-- discharge P (Γ ⊦ Q) yields P - {Γ} ⊦ P → Q
discharge :: Term String -> Sequent -> Sequent
discharge asm s@(Sequent n thm) = f (elemIndex asm $ assms s)
  where f (Just m) = case convMP (pushAssum lassms rassms) thm of
          [thm'] -> Sequent (n-1) thm'
          _      -> error "Discharge"
          where lassms = m
                rassms = n - m - 1
        f Nothing = discharge asm 
                    (Sequent (n + 1) (addFrontAsm asm thm))
                    
-- addHyp P (Γ ⊦ Q) yields {P} ∪ Γ ⊦ Q
addHyp :: Term String -> Sequent -> Sequent
addHyp asm s | asm `elem` assms s = s
addHyp asm s@(Sequent n thm)      =
  Sequent (n+1) (fromMaybe (head $ convMP (pushAssum 0 n) (addFrontAsm asm thm))
                 (do i <- findIndex (asm <) (assms s)
                     listToMaybe $ convMP (pushAssum 0 i) (addFrontAsm asm thm)))
     

-- Uncurry the first n hypotheses of a conditional
uncurryN n | n <= 1 = allC
uncurryN n = everyC (replicate (n-1) uncurry2)

-- Inverse of uncurryN
curryN n | n<= 1 = allC
curryN n = everyC (replicate (n-1) curry2)

-- mp (Γ ⊦ P) (Δ ⊦ P → Q) yields (Γ ∪ Δ ⊦ Q)
mpS :: Sequent-> Sequent -> [Sequent]
mpS (Sequent 0 imp) (Sequent 0 ant) = Sequent 0 `fmap` matchMP imp ant
mpS imps@(Sequent _ imp) ants@(Sequent _ ant) = 
    do impT'   <- convMP (uncurryN n) impT
       antT'   <- convMP (uncurryN n) antT
       thm     <- matchMP axiom2 impT'
       c       <- matchMP thm antT'
       c'      <- convMP (curryN n) c
       return (Sequent n c')
  where Sequent n impT = foldl (flip addHyp) imps (assms ants)
        Sequent _ antT = foldl (flip addHyp) ants (assms imps)

instMS :: (String -> Term String) -> [(String, Term String)] -> Sequent -> Sequent
instMS dflt l (Sequent n thm) = Sequent n (Utils.instM dflt l thm)

instLS :: [Term String] -> Sequent -> Sequent
instLS l p = instMS Var (zip (vars (theoremTerm (seqThm p))) l) p 