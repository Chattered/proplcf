-- An encapsulated logical kernel for a Hilbert-style Propositional Calculus

module Propositional (Theorem, Term(..), axiom1, axiom2, axiom3, mp, instTerm, inst, 
                      theoremTerm) where

infixr 8 :=>:

data Term a = Var a
            | Term a :=>: Term a
            | Not (Term a)
            deriving (Show,Eq,Ord)

newtype Theorem a = Theorem (Term a) deriving (Eq, Ord, Show)

theoremTerm :: Theorem a -> Term a
theoremTerm (Theorem t) = t

(p,q,r) = (Var "p",Var "q",Var "r")

axiom1 :: Theorem String
axiom1 = Theorem (p :=>: q :=>: p)

axiom2 :: Theorem String
axiom2 = Theorem ((p :=>: q :=>: r) :=>: (p :=>: q) :=>: (p :=>: r))

axiom3 :: Theorem String
axiom3 = Theorem ((Not p :=>: Not q) :=>: q :=>: p)

mp :: Eq a => Theorem a -> Theorem a -> [Theorem a]
mp (Theorem (p :=>: q)) (Theorem p') = [Theorem q | p == p']
                                                  
instTerm :: (a -> Term b) -> Term a -> Term b
instTerm f (Var p)    = f p
instTerm f (Not t)    = Not (instTerm f t)
instTerm f (a :=>: c) = instTerm f a :=>: instTerm f c

inst :: (a -> Term b) -> Theorem a -> Theorem b
inst f (Theorem t) = Theorem (instTerm f t)