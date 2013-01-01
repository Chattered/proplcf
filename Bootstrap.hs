-- A bootstrapping forward-prover and lemmas.

module Bootstrap where

import System.IO
import Propositional
import Utils
import Control.Monad

import Data.List

-- Proof terms with assumptions. In comments, we write Γ ⊢ P to denote a proof with
-- conclusion P and assumptions Γ. Proofs are not guaranteed to be valid, and are
-- pushed through the kernel via verify.
data Proof = Assume (Term String)
           | UseTheorem (Theorem String)
           | MP Proof Proof
            deriving (Eq,Show)
                     
-- sequent (Γ ⊢ P) yields (Γ, P)
sequent :: Proof -> ([Term String], Term String)
sequent (Assume a)   = ([a], a)
sequent (UseTheorem t) = ([], theoremTerm t)
sequent (MP pr pr')    = let (asms,c) = sequent pr' in
  case sequent pr of
    (asms', p :=>: q) | p == c    -> (nub $ sort $ asms ++ asms', q)
                      | otherwise -> error "MP"
    _ -> error "MP"

concl :: Proof -> Term String
concl = snd . sequent

assms :: Proof -> [Term String]
assms = fst . sequent

-- ⊢ P → P
truth :: Theorem String
truth = let step1 = instL [p, p :=>: p] axiom1
            step2 = instL [p, p :=>: p, p] axiom2
            step3 = head $ mp step2 step1
            step4 = instL [p, p] axiom1 in
        head $ mp step3 step4
     
-- discharge P (Γ ⊢ R) yields (Γ - {P} ⊢ P → R)
discharge :: Term String -> Proof -> Proof
discharge asm = d
    where d pr@(Assume t) | t == asm  = UseTheorem (instL [t] truth)
                          | otherwise =
                              MP (UseTheorem (instL [concl pr,asm] axiom1)) pr
          d pr@(UseTheorem t) 
              = MP (UseTheorem (instL [concl pr,asm] axiom1)) pr
          d (MP imp p) 
              = let p'           = concl p 
                in case concl imp of
                  _ :=>: r' ->
                      MP (MP (UseTheorem (instL [asm,p',r'] axiom2)) (d imp)) (d p)
                  _         -> error "MP"

-- Verify a proof. If there is only one assumption remaining, we automatically 
-- discharge it.
verify :: Proof -> Theorem String
verify proof = 
  let v (UseTheorem t) = t
      v (MP pr pr')    = case mp (v pr) (v pr') of
        []     -> error "MP"
        (t':_) -> t'
  in case assms proof of
    []  -> v proof
    [a] -> v (discharge a proof)
    as  -> error errorMsg
      where errorMsg = "Undischarged assumptions:\n" ++ 
                       unlines [ "  " ++ printTerm a | a <- as ]
          
-- matchMP (P → Q) (Γ ⊢ P') attempts to match P with P', and then applies MP.
matchMP :: Theorem String -> Proof -> Proof
matchMP imp ant = 
  let antT = concl ant in
    case theoremTerm imp of
      p :=>: q -> 
        case match p antT of
          [insts] -> MP (UseTheorem $ instM Var insts imp) ant
          _       -> error "MATCH MP"
      _ -> error "MATCH MP"      
      
-- ⊢ ¬P → P → ⊥
lemma1 :: Theorem String
lemma1 = let step1 = UseTheorem (instL [Not p, Not f] axiom1)
             step2 = Assume (Not p)
             step3 = MP step1 step2
             step4 = matchMP axiom3 step3
         in verify step4

-- ⊢ (¬P → Q) -> (¬P → ¬Q) → P
-- This is Mendelson's axiom3.
mendelson :: Theorem String
mendelson = let step1  = Assume (Not p :=>: Not q)
                step2  = Assume (Not p :=>: q) 
                step3  = Assume (Not p)
                step4  = MP step1 step3
                step5  = MP step2 step3
                step6  = matchMP lemma1 step4
                step7  = MP step6 step5
                step8  = discharge (Not p) step7
                step9  = matchMP axiom3 step8
                step10 = UseTheorem (instL [q] truth)
                step11 = MP step9 step10
                step12 = discharge (concl step2) step11
            in verify step12
               
-- ⊢ ¬¬P → P
dblNegElim :: Theorem String
dblNegElim = let step1 = Assume (Not (Not p))
                 step2 = Assume (Not p :=>: Not (Not p))
                 step3 = matchMP mendelson step2
                 step4 = UseTheorem (instL [Not p] truth)
                 step5 = MP step3 step4
                 step6 = discharge (concl step2) step5
                 step7 = UseTheorem (instL [Not (Not p), Not p] axiom1)
                 step8 = MP step7 step1
                 step9 = MP step6 step8
             in verify step9
                
-- ⊢ P → ¬¬P                
dblNegIntro :: Theorem String
dblNegIntro = let step1 = UseTheorem (instL [Not p] dblNegElim)
                  step2 = matchMP axiom3 step1
              in verify step2
                 
-- ⊢ (P → Q) → ¬Q → ¬P
mt :: Theorem String
mt = let step1 = Assume (p :=>: q)
         step2 = Assume (Not (Not p))
         step3 = matchMP dblNegElim step2
         step4 = MP step1 step3
         step5 = matchMP dblNegIntro step4
         step6 = discharge (concl step2) step5
         step7 = matchMP axiom3 step6
     in verify step7
        
-- ⊢ P → ¬P → Q
notElim :: Theorem String
notElim = let step1 = Assume p
              step2 = Assume (Not p)
              step3 = UseTheorem (instL [p, Not q] axiom1)
              step4 = MP step3 step1
              step5 = matchMP mt step4
              step6 = MP step5 step2
              step7 = matchMP dblNegElim step6
              step8 = discharge (concl step2) step7
          in verify step8
             
-- ⊢ (P → Q) → (¬P → Q) → Q
cases :: Theorem String
cases = let step1  = Assume (p :=>: q)
            step2  = Assume (Not p :=>: q)
            step3  = matchMP mt step1
            step4  = matchMP mt step2
            step5  = Assume (Not q)
            step6  = MP step4 step5
            step7  = matchMP dblNegElim step6
            step8  = discharge (concl step5) step7
            step9  = matchMP mendelson step3
            step10 = MP step9 step8
            step11 = discharge (concl step2) step10
        in verify step11
                                         
-- ⊢ (P → ¬P) → ¬P
contra :: Theorem String
contra = let step1 = Assume (p :=>: Not p)
             step2 = Assume p
             step3 = MP step1 step2
             step4 = discharge (concl step2) step3
             step5 = Assume (Not p)
             step6 = discharge (concl step5) step5
             step7 = matchMP cases step4 
             step8 = MP step7 step6
         in verify step8
            
-- ⊢ (¬P → P) → P            
contra2 :: Theorem String
contra2 = let step1 = Assume (Not p :=>: p)
              step2 = Assume (Not p)
              step3 = MP step1 step2
              step4 = matchMP dblNegIntro step3
              step5 = discharge (concl step2) step4
              step6 = matchMP contra step5
              step7 = matchMP dblNegElim step6
          in verify step7

-- ⊢ P ∧ Q → P
conj1 :: Theorem String
conj1 = let step1  = Assume p
            step2  = Assume (Not p)
            step3  = UseTheorem (instL [p,Not q] notElim)
            step4  = MP step3 step1
            step5  = MP step4 step2
            step6  = discharge (concl step1) step5
            step7  = UseTheorem (instL [concl step6, p] notElim)
            step8  = MP step7 step6
            step9  = Assume (p /\ q)
            step10 = MP step8 step9
            step11 = discharge (concl step2) step10
            step12 = matchMP contra2 step11
        in verify step12

-- ⊢ P ∧ Q → Q
conj2 :: Theorem String
conj2 = let step1 = Assume p
            step2 = Assume (Not q)
            step3 = discharge (concl step1) step2
            step4 = UseTheorem (instL [concl step3, q] notElim)
            step5 = MP step4 step3
            step6 = Assume (p /\ q)
            step7 = MP step5 step6
            step8 = discharge (concl step2) step7
            step9 = matchMP contra2 step8
        in verify step9
              
-- ⊢ P → Q → P ∧ Q
conjI :: Theorem String
conjI = let step1  = Assume p
            step2  = Assume q
            step3  = Assume (p :=>: Not q)
            step4  = MP step3 step1
            step5  = UseTheorem (instL [concl step2, Not (concl step3)] notElim)
            step6  = MP step5 step2
            step7  = MP step6 step4
            step8  = discharge (concl step3) step7
            step9  = matchMP contra step8
            step10 = discharge (concl step2) step9
        in verify step10
           
-- ⊢ (P → Q → R) ↔ (Q → P → R)
swapT :: Theorem String
swapT = let step1 = UseTheorem lemma
            step2 = UseTheorem (instL [q,p] lemma)
            step3 = UseTheorem (instL [concl step1, concl step2] conjI )
            step4 = MP step3 step1
            step5 = MP step4 step2
        in verify step5
  where lemma = let step1 = Assume p
                    step2 = Assume q
                    step3 = Assume (p :=>: q :=>: r)
                    step4 = MP step3 step1
                    step5 = MP step4 step2
                    step6 = discharge (concl step1) step5
                    step7 = discharge (concl step2) step6
                in verify step7
                   
-- ⊦ (P → Q → R) ↔ (P /\ Q → R)
uncurry :: Theorem String
uncurry = let step1 = Assume (p :=>: q :=>: r)
              step2 = Assume (p /\ q)
              step3 = matchMP conj1 step2
              step4 = matchMP conj2 step2
              step5 = MP step1 step3
              step6 = MP step5 step4
              step7 = discharge (concl step2) step6
              step8 = discharge (concl step1) step7
              step9 = Assume (p /\ q :=>: r)
              step10 = Assume p
              step11 = Assume q
              step12 = matchMP conjI step10
              step13 = MP step12 step11
              step14 = MP step9 step13
              step15 = discharge (concl step11) step14
              step16 = discharge (concl step10) step15
              step17 = discharge (concl step9) step16
              step18 = UseTheorem (instL [concl step8, concl step17] conjI )
              step19 = MP step18 step8
              step20 = MP step19 step17
          in verify step20

-- Theorems for equational reasoning
x = Var "x"                   
y = Var "y"
z = Var "z"

-- ⊢ (X ↔ Y) → X → Y
eqMP :: Theorem String
eqMP = let step1 = Assume (x <=> y)
           step2 = Assume x
           step3 = matchMP conj1 step1
           step4 = MP step3 step2
           step5 = discharge (concl step2) step4
       in verify step5

-- ⊢ (X ↔ X)
reflEq :: Theorem String
reflEq = let step1 = UseTheorem (instL [theoremTerm truth, theoremTerm truth] conjI)
             step2 = UseTheorem truth
             step3 = MP step1 step2
             step4 = MP step3 step2
         in verify step4             

-- ⊢ (X ↔ Y) ↔ (Y ↔ X)
symEq :: Theorem String
symEq = let step1 = UseTheorem lemma
            step2 = UseTheorem (instL [y,x] lemma)
            step3 = UseTheorem (instL [concl (step1), concl (step2)] conjI)
            step4 = MP step3 step1
            step5 = MP step4 step2
        in verify step5
  where lemma = let step1  = Assume (x <=> y)
                    step2  = Assume y
                    step3  = matchMP conj2 step1
                    step4  = MP step3 step2
                    step5  = discharge (concl step2) step4
                    step6  = Assume x
                    step7  = matchMP conj1 step1
                    step8  = MP step7 step6
                    step9  = discharge (concl step6) step8
                    step10 = UseTheorem (instL [concl (step5), concl (step9)] conjI)
                    step11 = MP step10 step5
                    step12 = MP step11 step9
                in verify step12
                   
-- ⊢ (X ↔ Y) → (Y ↔ Z) → (X ↔ Z)
trans :: Theorem String
trans = let step1 = Assume (x <=> y)
            step2 = Assume (y <=> z)
            step3 = Assume x
            step4 = matchMP conj1 step1
            step5 = matchMP conj1 step2
            step6 = MP step4 step3
            step7 = MP step5 step6
            step8 = discharge (concl step3) step7 
            step9 = Assume z
            step10 = matchMP conj2 step2
            step11 = matchMP conj2 step1
            step12 = MP step10 step9
            step13 = MP step11 step12
            step14 = discharge (concl step9) step13
            step15 = UseTheorem (instL [concl step8, concl step14] conjI)
            step16 = MP step15 step8
            step17 = MP step16 step14
            step18 = discharge (concl step2) step17
        in verify step18
            
-- reflect (⊢ (X ↔ Y) → φ(X) → ψ(X)) yields ⊢ (X ↔ Y) → φ(X,Y) ↔ ψ(X,Y)
reflect thm = let step1  = UseTheorem thm
                  step2  = UseTheorem (instL [y,x] thm)
                  step3  = Assume (x <=> y)
                  step4  = MP step1 step3
                  step5  = matchMP conj1 (UseTheorem symEq)
                  step6  = MP step5 step3
                  step7  = MP step2 step6 
                  step8  = UseTheorem (instL [concl step4, concl step7] conjI)
                  step9  = MP step8 step4
                  step10 = MP step9 step7
            in verify step10                    
                   
-- ⊢ (X ↔ Y) → (X → P ↔ Y → P)
substLeft :: Theorem String
substLeft = reflect lemma
  where lemma = let step1 = Assume (x <=> y)
                    step2 = Assume (x :=>: p)
                    step3 = Assume y
                    step4 = matchMP conj2 step1
                    step5 = MP step4 step3
                    step6 = MP step2 step5
                    step7 = discharge (concl step3) step6
                    step8 = discharge (concl step2) step7
                in verify step8
               
-- ⊢ (X ↔ Y) → (P → X ↔ P → Y)
substRight :: Theorem String
substRight = reflect lemma
  where lemma = let step1 = Assume (x <=> y)
                    step2 = Assume (p :=>: x)
                    step3 = Assume p
                    step4 = MP step2 step3
                    step5 = matchMP conj1 step1
                    step6 = MP step5 step4
                    step7 = discharge (concl step3) step6
                    step8 = discharge (concl step2) step7
                in verify step8

-- ⊢ (X ↔ Y) → (¬X ↔ ¬Y)
substNot :: Theorem String
substNot = reflect lemma
  where lemma = let step1 = Assume (x <=> y)
                    step2 = matchMP conj2 step1
                    step3 = matchMP mt step2
                in verify step3
                   
