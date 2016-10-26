-- | The kernel for propositional logic.

module Proposition (Theorem, Term(..), axiom1, axiom2, axiom3, mp,
                    Two(..), Three(..),
                    instTerm, inst, termOfTheorem) where

infixr 1 :=>:

-- | The syntax of propositional logic, with variables drawn from the alphabet `a`.
data Term a = Var a
            | Term a :=>: Term a
            | Not (Term a)
            deriving Eq

-- | The abstract type of theorems.
newtype Theorem a = Theorem (Term a)

-- | All theorems are terms. Not all terms are theorems.
termOfTheorem :: Theorem a -> Term a
termOfTheorem (Theorem t) = t

-- | The two element alphabet.
data Two = X | Y

-- | The three element alphabet.
data Three = P | Q | R

x :: Term Two
y :: Term Two
(x,y) = (Var X,Var Y)

p :: Term Three
q :: Term Three
r :: Term Three
(p,q,r) = (Var P, Var Q, Var R)

-- | Axiom 1. The K combinator.
axiom1 :: Theorem Two
axiom1 = Theorem (x :=>: y :=>: x)

-- | Axiom 2. The S combinator.
axiom2 :: Theorem Three
axiom2 = Theorem ((p :=>: q :=>: r) :=>: (p :=>: q) :=>: (p :=>: r))

-- | Axiom 3. The classical axiom.
axiom3 :: Theorem Two
axiom3 = Theorem ((Not x :=>: Not y) :=>: y :=>: x)

-- | Modus Ponens.
mp :: Eq a => Theorem a -> Theorem a -> Maybe (Theorem a)
mp (Theorem (p :=>: q)) (Theorem p') | p == p' = pure (Theorem q)
mp _ _ = Nothing

-- | Instantiate the variables of a term.
instTerm :: (a -> Term b) -> Term a -> Term b
instTerm f (Var x)    = f x
instTerm f (Not t)    = Not (instTerm f t)
instTerm f (a :=>: c) = instTerm f a :=>: instTerm f c

-- | Instantiate the variables of a theorem.
inst :: (a -> Term b) -> Theorem a -> Theorem b
inst f (Theorem x) = Theorem (instTerm f x)
