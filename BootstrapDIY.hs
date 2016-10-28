-- | Just enough theorems to get us going with conversions, proven using a tree
-- notation that allows us to make assumptions.

module BootstrapDIY where

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
mendelson = undefined

-- | ⊢ ¬¬P → P
dblNegElim :: Theorem ()
dblNegElim = undefined

-- | ⊢ P → ¬¬P
dblNegIntro :: Theorem ()
dblNegIntro = undefined

-- | ⊢ (P → Q) → ¬Q → ¬P
mt :: Theorem Two
mt = undefined

-- | ⊢ P → ¬P → Q
notElim :: Theorem Two
notElim = undefined

-- | ⊢ (P → Q) → (¬P → Q) → Q
cases :: Theorem Two
cases = undefined

-- | ⊢ (P → ¬P) → ¬P
contra :: Theorem ()
contra = undefined

-- | ⊢ (¬P → P) → P
contra2 :: Theorem ()
contra2 = undefined

-- | ⊢ P ∧ Q → P
conj1 :: Theorem Two
conj1 = undefined

-- | ⊢ P ∧ Q → Q
conj2 :: Theorem Two
conj2 = undefined

-- | ⊢ P → Q → P ∧ Q
conjI :: Theorem Two
conjI = undefined

p :: Term Three
q :: Term Three
r :: Term Three
(p,q,r) = (Var P, Var Q, Var R)

-- | ⊢ (P → Q → R) ↔ (Q → P → R)
swapT :: Theorem Three
swapT = undefined

-- | ⊦ (P → Q → R) ↔ (P /\ Q → R)
uncurry :: Theorem Three
uncurry = undefined

-- | ⊢ (X ↔ Y) → X → Y
eqMP :: Theorem Two
eqMP = undefined

-- | ⊢ (X ↔ X)
reflEq :: Theorem ()
reflEq = undefined

-- | ⊢ (X ↔ Y) ↔ (Y ↔ X)
symEq :: Theorem Two
symEq = undefined

-- | ⊢ (X ↔ Y) → (Y ↔ Z) → (X ↔ Z)
trans :: Theorem Three
trans = undefined

-- | reflect (⊢ (X ↔ Y) → φ(X) → ψ(X)) yields ⊢ (X ↔ Y) → φ(X,Y) ↔ ψ(X,Y)
reflect :: (Ord a, Show a) => Theorem a -> Theorem a
reflect = undefined

-- | ⊢ (X ↔ Y) → (X → P ↔ Y → P)
substLeft :: Theorem Three
substLeft = undefined

-- | ⊢ (X ↔ Y) → (P → X ↔ P → Y)
substRight :: Theorem Three
substRight = undefined

-- | ⊢ (X ↔ Y) → (¬X ↔ ¬Y)
substNot :: Theorem Two
substNot = undefined
