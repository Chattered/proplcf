-- | Just enough theorems to get us going with conversions, proven using a tree
-- notation that allows us to make assumptions.

module Bootstrap where

import Data.Foldable
import Data.List

import Utils

-- | Proof terms with assumptions. In the notes, we write Γ ⊢ P to denote a proof
-- with conclusion P and assumptions Γ. Proofs are not guaranteed to be valid, and
-- are pushed through the kernel via verify.
data Proof a = Assume (Term a)
             | UseTheorem (Theorem a)
             | MP (Proof a) (Proof a)
             deriving Eq

-- | sequent (Γ ⊢ P) yields (Γ, P)
sequent :: (Ord a, Show a) => Proof a -> ([Term a], Term a)
sequent (Assume a)   = ([a], a)
sequent (UseTheorem t) = ([], termOfTheorem t)
sequent (MP pr pr')    = let (asms,c) = sequent pr' in
  case sequent pr of
    (asms', p :=>: q) | p == c    -> (nub $ sort $ asms ++ asms', q)
                      | otherwise -> error ("MP: " ++ show [p :=>: q, c])
    (_, imp) -> error ("MP: " ++ show [imp, c])

-- | concl (Γ ⊢ P) yields P
concl :: (Ord a, Show a) => Proof a -> Term a
concl = snd . sequent

-- | concl (Γ ⊢ P) yields Γ
assms :: (Ord a, Show a) => Proof a -> [Term a]
assms = fst . sequent

u :: Term ()
x :: Term Two
y :: Term Two
u = pure ()
(x,y) = (pure X, pure Y)

-- | ⊢ P → P
truthThm :: Theorem ()
truthThm =
  let step1 = inst2 u (truth ()) axiom1
      step2 = inst3 u (truth ()) u axiom2
      step3 = mp step2 step1
      step4 = inst2 u u axiom1
  in mp step3 step4

-- | discharge P (Γ ⊢ R) yields (Γ - {P} ⊢ P → R). This is mechanics of the deduction
-- theorem.
discharge :: (Ord a, Show a) => Term a -> Proof a -> Proof a
discharge asm = d
    where d pr@(Assume t) | t == asm  = UseTheorem (inst (const t) truthThm)
                          | otherwise =
                              MP (UseTheorem (inst2 (concl pr) asm axiom1)) pr
          d pr@(UseTheorem t) =
                MP (UseTheorem (inst2 (concl pr) asm axiom1)) pr
          d (MP imp p) =
                let p' = concl p
                in case concl imp of
                  p'' :=>: r' | p' == p''->
                    MP (MP (UseTheorem (inst3 asm p' r' axiom2)) (d imp)) (d p)
                  _ -> error ("Discharge MP:" ++ show [concl imp, p'])

-- | Verify a proof. If there is only one assumption remaining, we automatically
-- discharge it.
verify :: (Ord a, Show a) => Proof a -> Theorem a
verify proof =
  let v (UseTheorem t) = t
      v (MP pr pr')    = mp (v pr) (v pr')
  in case assms proof of
    []  -> v proof
    [a] -> v (discharge a proof)
    as  -> error errorMsg
      where errorMsg = "Undischarged assumptions:\n" ++
                       unlines [ "  " ++ show a | a <- as ]

-- | matchMPInst (P → Q) (Γ ⊢ P') inst
-- attempts to match P with P', instantiates any remaining variables with inst, and
-- then applies MP.
matchMPInst :: (Eq a, Ord b, Show b) =>
               Theorem a -> Proof b -> (a -> Term b) -> Proof b
matchMPInst imp ant inst =
  let antT = concl ant in
    case termOfTheorem imp of
      p :=>: q ->
        case match p antT of
          Just insts -> MP (UseTheorem $ instM inst insts imp) ant
          _          -> error "MATCH MP: No match"
      _ -> error "MATCH MP"

-- | matchMP without any instantiation. All theorems and proofs must be drawn from
-- the same alphabet.
matchMP :: (Ord a, Show a) => Theorem a -> Proof a -> Proof a
matchMP imp ant = matchMPInst imp ant pure

-- | ⊢ ¬P → P → ⊥
lemma1 :: Theorem Two
lemma1 = let step1 = UseTheorem (inst2 (Not x) (Not (false Y)) axiom1)
             step2 = Assume (Not x)
             step3 = MP step1 step2
             step4 = matchMP axiom3 step3
         in verify step4

-- | ⊢ (¬P → ¬Q) -> (¬P → Q) → P
-- | Mendelson's axiom3.
mendelson :: Theorem Two
mendelson = let step1  = Assume (Not x :=>: Not y)
                step2  = Assume (Not x :=>: y)
                step3  = Assume (Not x)
                step4  = MP step1 step3
                step5  = MP step2 step3
                step6  = matchMP lemma1 step4
                step7  = MP step6 step5
                step8  = discharge (Not x) step7
                step9  = matchMP axiom3 step8
                step10 = UseTheorem (inst1 y truthThm)
                step11 = MP step9 step10
                step12 = discharge (concl step2) step11
            in verify step12

-- | ⊢ ¬¬P → P
dblNegElim :: Theorem ()
dblNegElim = let step1 = Assume (Not (Not u))
                 step2 = Assume (Not u :=>: Not (Not u))
                 step3 = MP (UseTheorem (inst2 u (Not u) mendelson)) step2
                 step4 = UseTheorem (inst1 (Not u) truthThm)
                 step5 = MP step3 step4
                 step6 = discharge (concl step2) step5
                 step7 = UseTheorem (inst2 (Not (Not u)) (Not u) axiom1)
                 step8 = MP step7 step1
                 step9 = MP step6 step8
             in verify step9

-- | ⊢ P → ¬¬P
dblNegIntro :: Theorem ()
dblNegIntro = let step1 = UseTheorem (inst1 (Not u) dblNegElim)
                  step2 = MP (UseTheorem (inst2 (Not (Not u)) u axiom3)) step1
              in verify step2

-- | ⊢ (P → Q) → ¬Q → ¬P
mt :: Theorem Two
mt = let step1 = Assume (x :=>: y)
         step2 = Assume (Not (Not x))
         step3 = MP (UseTheorem (inst1 x dblNegElim)) step2
         step4 = MP step1 step3
         step5 = MP (UseTheorem (inst1 y dblNegIntro)) step4
         step6 = discharge (concl step2) step5
         step7 = matchMP axiom3 step6
     in verify step7

-- | ⊢ P → ¬P → Q
notElim :: Theorem Two
notElim = let step1 = Assume x
              step2 = Assume (Not x)
              step3 = UseTheorem (inst2 x (Not y) axiom1)
              step4 = MP step3 step1
              step5 = matchMP mt step4
              step6 = MP step5 step2
              step7 = MP (UseTheorem (inst1 y dblNegElim)) step6
              step8 = discharge (concl step2) step7
          in verify step8

-- | ⊢ (P → Q) → (¬P → Q) → Q
cases :: Theorem Two
cases = let step1  = Assume (x :=>: y)
            step2  = Assume (Not x :=>: y)
            step3  = matchMP mt step1
            step4  = matchMP mt step2
            step5  = Assume (Not y)
            step6  = MP step4 step5
            step7  = MP (UseTheorem (inst1 x dblNegElim)) step6
            step8  = discharge (concl step5) step7
            step9  = matchMP mendelson step3
            step10 = MP step9 step8
            step11 = discharge (concl step2) step10
        in verify step11

-- | ⊢ (P → ¬P) → ¬P
contra :: Theorem ()
contra = let step1 = Assume (u :=>: Not u)
             step2 = Assume u
             step3 = MP step1 step2
             step4 = discharge (concl step2) step3
             step5 = Assume (Not u)
             step6 = discharge (concl step5) step5
             step7 = MP (UseTheorem (inst2 u (Not u) cases)) step4
             step8 = MP step7 step6
         in verify step8

-- | ⊢ (¬P → P) → P
contra2 :: Theorem ()
contra2 = let step1 = Assume (Not u :=>: u)
              step2 = Assume (Not u)
              step3 = MP step1 step2
              step4 = matchMP dblNegIntro step3
              step5 = discharge (concl step2) step4
              step6 = matchMP contra step5
              step7 = matchMP dblNegElim step6
          in verify step7

-- | ⊢ P ∧ Q → P
conj1 :: Theorem Two
conj1 = let step1  = Assume x
            step2  = Assume (Not x)
            step3  = UseTheorem (inst2 x (Not y) notElim)
            step4  = MP step3 step1
            step5  = MP step4 step2
            step6  = discharge (concl step1) step5
            step7  = UseTheorem (inst2 (concl step6) x notElim)
            step8  = MP step7 step6
            step9  = Assume (x /\ y)
            step10 = MP step8 step9
            step11 = discharge (concl step2) step10
            step12 = MP (UseTheorem (inst1 x contra2)) step11
        in verify step12

-- | ⊢ P ∧ Q → Q
conj2 :: Theorem Two
conj2 = let step1 = Assume x
            step2 = Assume (Not y)
            step3 = discharge (concl step1) step2
            step4 = UseTheorem (inst2 (concl step3) y notElim)
            step5 = MP step4 step3
            step6 = Assume (x /\ y)
            step7 = MP step5 step6
            step8 = discharge (concl step2) step7
            step9 = MP (UseTheorem (inst1 y contra2)) step8
        in verify step9

-- | ⊢ P → Q → P ∧ Q
conjI :: Theorem Two
conjI = let step1  = Assume x
            step2  = Assume y
            step3  = Assume (x :=>: Not y)
            step4  = MP step3 step1
            step5  = UseTheorem (inst2 (concl step2) (Not (concl step3)) notElim)
            step6  = MP step5 step2
            step7  = MP step6 step4
            step8  = discharge (concl step3) step7
            step9  = MP (UseTheorem (inst1 (x :=>: Not y) contra)) step8
            step10 = discharge (concl step2) step9
        in verify step10

p :: Term Three
q :: Term Three
r :: Term Three
(p,q,r) = (Var P, Var Q, Var R)

-- | ⊢ (P → Q → R) ↔ (Q → P → R)
swapT :: Theorem Three
swapT = let step1 = UseTheorem lemma
            step2 = UseTheorem (inst3 q p r lemma)
            step3 = UseTheorem (inst2 (concl step1) (concl step2) conjI )
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

-- | ⊦ (P → Q → R) ↔ (P /\ Q → R)
uncurry :: Theorem Three
uncurry = let step1  = Assume (p :=>: q :=>: r)
              step2  = Assume (p /\ q)
              step3  = MP (UseTheorem (inst2 p q conj1)) step2
              step4  = MP (UseTheorem (inst2 p q conj2)) step2
              step5  = MP step1 step3
              step6  = MP step5 step4
              step7  = discharge (concl step2) step6
              step8  = discharge (concl step1) step7
              step9  = Assume (p /\ q :=>: r)
              step10 = Assume p
              step11 = Assume q
              step12 = matchMP (inst2 p q conjI) step10
              step13 = MP step12 step11
              step14 = MP step9 step13
              step15 = discharge (concl step11) step14
              step16 = discharge (concl step10) step15
              step17 = discharge (concl step9) step16
              step18 = UseTheorem (inst2 (concl step8) (concl step17) conjI)
              step19 = MP step18 step8
              step20 = MP step19 step17
          in verify step20

-- | ⊢ (X ↔ Y) → X → Y
eqMP :: Theorem Two
eqMP = let step1 = Assume (x <=> y)
           step2 = Assume x
           step3 = matchMP conj1 step1
           step4 = MP step3 step2
           step5 = discharge (concl step2) step4
       in verify step5

-- | ⊢ (X ↔ X)
reflEq :: Theorem ()
reflEq = let step1 = UseTheorem (inst2 (truth ()) (truth ()) conjI)
             step2 = UseTheorem truthThm
             step3 = MP step1 step2
             step4 = MP step3 step2
         in verify step4

-- | ⊢ (X ↔ Y) ↔ (Y ↔ X)
symEq :: Theorem Two
symEq = let step1 = UseTheorem lemma
            step2 = UseTheorem (inst2 y x lemma)
            step3 = UseTheorem (inst2 (concl (step1)) (concl (step2)) conjI)
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
                    step10 = UseTheorem (inst2 (concl (step5)) (concl (step9)) conjI)
                    step11 = MP step10 step5
                    step12 = MP step11 step9
                in verify step12

-- | ⊢ (X ↔ Y) → (Y ↔ Z) → (X ↔ Z)
trans :: Theorem Three
trans = let step1 = Assume (p <=> q)
            step2 = Assume (q <=> r)
            step3 = Assume p
            step4 = MP (UseTheorem (inst2 (p :=>: q) (q :=>: p) conj1)) step1
            step5 = MP (UseTheorem (inst2 (q :=>: r) (r :=>: q) conj1)) step2
            step6 = MP step4 step3
            step7 = MP step5 step6
            step8 = discharge (concl step3) step7
            step9 = Assume r
            step10 = MP (UseTheorem (inst2 (p :=>: q) (q :=>: p) conj2)) step1
            step11 = MP (UseTheorem (inst2 (q :=>: r) (r :=>: q) conj2)) step2
            step12 = MP step11 step9
            step13 = MP step10 step12
            step14 = discharge (concl step9) step13
            step15 = UseTheorem (inst2 (concl step8) (concl step14) conjI)
            step16 = MP step15 step8
            step17 = MP step16 step14
            step18 = discharge (concl step2) step17
        in verify step18

-- | reflect (⊢ (X ↔ Y) → φ(X) → ψ(X)) yields ⊢ (X ↔ Y) → φ(X,Y) ↔ ψ(X,Y)
reflect :: (Ord a, Show a) => Theorem a -> Theorem a
reflect thm = let (xv:yv:_) = toList thm
                  (x,y)     = (pure xv, pure yv)
                  step1     = UseTheorem thm
                  step2     = UseTheorem (instM pure [(xv,y),(yv,x)] thm)
                  step3     = Assume (x <=> y)
                  step4     = MP step1 step3
                  step5     = UseTheorem (inst2 ((x <=> y) :=>: (y <=> x))
                                                ((y <=> x) :=>: (x <=> y))
                                                conj1)
                  step6     = MP step5 (UseTheorem (inst2 x y symEq))
                  step7     = MP step6 step3
                  step8     = MP step2 step7
                  step9     = UseTheorem (inst2 (concl step4) (concl step8) conjI)
                  step10    = MP step9 step4
                  step11    = MP step10 step8
            in verify step11

-- | ⊢ (X ↔ Y) → (X → P ↔ Y → P)
substLeft :: Theorem Three
substLeft = reflect lemma
  where lemma = let step1 = Assume (p <=> q)
                    step2 = Assume (p :=>: r)
                    step3 = Assume q
                    step4 = UseTheorem (inst2 (p :=>: q) (q :=>: p) conj2)
                    step5 = MP step4 step1
                    step6 = MP step5 step3
                    step7 = MP step2 step6
                    step8 = discharge (concl step3) step7
                    step9 = discharge (concl step2) step8
                in verify step9

-- | ⊢ (X ↔ Y) → (P → X ↔ P → Y)
substRight :: Theorem Three
substRight = reflect lemma
  where lemma = let step1 = Assume (p <=> q)
                    step2 = Assume (r :=>: p)
                    step3 = Assume r
                    step4 = MP step2 step3
                    step5 = UseTheorem (inst2 (p :=>: q) (q :=>: p) conj1)
                    step6 = MP step5 step1
                    step7 = MP step6 step4
                    step8 = discharge (concl step3) step7
                    step9 = discharge (concl step2) step8
                in verify step9

-- | ⊢ (X ↔ Y) → (¬X ↔ ¬Y)
substNot :: Theorem Two
substNot = reflect lemma
  where lemma = let step1 = Assume (x <=> y)
                    step2 = matchMP conj2 step1
                    step3 = matchMP mt step2
                in verify step3
