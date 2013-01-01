-- Natural deduction

module Natural where

import Propositional
import Sequent
import qualified Bootstrap as B
import Utils
import Control.Monad
import Data.List

-- Given ⊦ P → Q and ⊦ R, attempt to match P and R and then apply mp
matchMP :: Sequent -> Sequent -> [Sequent]
matchMP imp ant = case (concl imp, concl ant) of
      (p :=>: q, p') -> do insts <- match p p'
                           mpS (instMS (Var . avoid (vars p')) insts imp) ant
      _ -> []
                     
matchMP' imp ant = case (concl imp, concl ant) of
      (p :=>: q, p') -> do insts <- match p p'
                           return $ instMS (Var . avoid (vars p')) insts imp

-- cut (Γ ⊢ P) (Δ ⊦ Q) yields (Γ ∪ Δ - {P}) ⊢ Q)
cut :: Sequent -> Sequent -> Sequent
cut s s' = head $ matchMP (discharge (concl s) s') s

-- impI (Γ ∪ {P} ⊢ Q) yields Γ ⊢ P → Q
impI :: Term String -> Sequent -> Sequent
impI = discharge

-- impE (Γ ⊢ P → Q) yields Γ ∪ {P} ⊢ Q
impE :: Sequent -> [Sequent]
impE thm = mpS thm (assume p)
    where (p :=>: q) = concl thm

-- conjI (Γ ⊢ P) (Δ ⊦ Q) yields Γ ∪ Δ ⊦ P ∧ Q                        
conjI :: Sequent -> Sequent -> Sequent
conjI p q = head (do qr <- matchMP (sequent B.conjI) p
                     matchMP qr q)

-- conj1 (Γ ⊢ P ∧ Q) yields Γ ⊦ P
conj1 :: Sequent -> [Sequent]
conj1 conj = matchMP (sequent B.conj1) conj

-- conj2 (Γ ⊢ P ∧ Q) yields Γ ⊦ Q
conj2 :: Sequent -> [Sequent]
conj2 conj = matchMP (sequent B.conj2) conj

isConj (Not (p :=>: Not q)) = True
isConj _                    = False

-- Recursively strip conjunctions                              
conjL :: Sequent -> [Sequent]
conjL conj = do p <- conj1 conj
                q <- conj2 conj
                nub $ conjL p ++ conjL q
                        ++ [p | not (isConj (concl p))]
                        ++ [q | not (isConj (concl q))]

-- disj1 q (Γ ⊢ P) yields Γ ⊦ P ∨ q
disj1 :: Term String -> Sequent -> Sequent
disj1 q l = head $ matchMP (sequent (instL [concl l, q] B.notElim)) l

-- disj2 p (Γ ⊢ P) yields Γ ⊦ p ∨ P
disj2 :: Term String -> Sequent -> Sequent
disj2 p r = head $ matchMP (sequent $ instL [concl r,Not p] axiom1) r

disjELemma :: Sequent
disjELemma = head (do
    step1  <- [assume (p \/ q)]
    step2  <- [assume (p :=>: r)]
    step3  <- [assume (q :=>: r)]
    step4  <- [assume p]
    step5  <- matchMP step2 step4
    step6  <- [assume (Not p)]
    step7  <- matchMP step1 step6
    step8  <- matchMP step3 step7
    step9  <- [discharge (concl step4) step5]
    step10 <- [discharge (concl step6) step8]
    step11 <- matchMP (sequent B.cases) step9
    step12 <- matchMP step11 step10
    [foldr discharge step12 [concl step1, concl step2, concl step3]])

-- disjE (Γ ⊢ P ∨ Q) (Δ u {P} ⊢ R) (Ε u {Q} ⊢ R) yields Γ ∪ Δ ∪ Ε ⊦ R
disjE :: Sequent -> Sequent -> Sequent -> [Sequent]
disjE disj l r = matchMP disjELemma disj 
                 >>= flip matchMP (impI p l)
                 >>= flip matchMP (impI q r)
  where Not p :=>: q = concl disj

falseElimLemma :: Sequent
falseElimLemma = head (do
    step1 <- matchMP axiom1S (sequent B.truth)
    step2 <- matchMP (sequent B.mt) (instLS [Not q] step1)
    step3 <- [assume f]
    step4 <- matchMP step2 step3
    step5 <- matchMP (sequent B.dblNegElim) step4
    [discharge (concl step3) step5])

-- falseElim P (Γ ⊢ ⊥) yields (Γ ⊢ P)
falseElim :: Term String -> Sequent -> [Sequent]
falseElim p = matchMP (instMS Var [("q", p)] falseElimLemma) 

-- notElim (Γ ⊢ ¬P) yields (Γ ⊢ P → ⊥)
notElim :: Sequent -> [Sequent]
notElim = matchMP (sequent B.lemma1)

-- exclude-middle
excludedMiddle :: Sequent
excludedMiddle = sequent B.dblNegElim