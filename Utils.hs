module Utils where

import Propositional

import Data.List
import Data.Maybe (mapMaybe)

p = Var "p"
q = Var "q"
r = Var "r"

-- Derived syntax
p \/ q  = Not p :=>: q
p /\ q  = Not (p :=>: Not q)
p <=> q = (p :=>: q) /\ (q :=>: p)
t  = p :=>: p
f  = Not t
        
printTerm :: Term String -> String
printTerm (Var p)             = p
printTerm (Not (Var p))       = "~" ++ p
printTerm (Not (Not p))       = "~" ++ printTerm (Not p)
printTerm (Not p)             = "~(" ++ printTerm p ++ ")"
printTerm ((p :=>: q) :=>: r) = "(" ++ printTerm (p :=>: q) ++ ")" 
                               ++ " ==> " ++ printTerm r
printTerm (p :=>: q)          = printTerm p ++ " ==> " ++ printTerm q

printThm thm = "|- " ++ printTerm (theoremTerm thm)

vars :: Eq a => Term a -> [a]
vars (Var p)    = [p]
vars (Not p)    = vars p
vars (p :=>: q) = nub $ vars p ++ vars q
        
-- Instantiate variables in a term using a lookup
instTermM :: (Eq a) => (a -> Term b) -> [(a, Term b)] -> Term a -> Term b
instTermM dflt l = instTerm f
  where f p = maybe (dflt p) id (lookup p l)
        
-- Instantiate variables in a theorem using a lookup
instM :: (Eq a) => (a -> Term b) -> [(a, Term b)] -> Theorem a -> Theorem b
instM dflt l = inst f
  where f p = maybe (dflt p) id (lookup p l)
        
-- Instantiate variables in the order that they appear when in a depth-first traversal
instL :: Eq a => [Term a] -> Theorem a -> Theorem a
instL l p = instM Var (zip (vars (theoremTerm p)) l) p
        
avoid :: [String] -> String -> String
avoid ps p = p ++ replicate maxPrimes '\''
  where suffixes  = mapMaybe (stripPrefix p) ps
        maxPrimes = (maximum $ 0 : map primes suffixes)
        primes cs = 
          case span (== '\'') cs of
            (ps,"") -> length ps + 1
            _       -> 0
            
match :: (Eq a, Eq b) => Term a -> Term b -> [[(a, Term b)]]
match = m [] 
  where m is (Var p) t =
          case lookup p is of
            Nothing -> [ (p, t) : is ]
            Just t' -> [ is | t == t' ]
        m is (Not t) (Not t')        = m is t t'
        m is (a :=>: c) (a' :=>: c') = concat [ m is' c c' | is' <- m is a a' ]
        m _ _ _                      = []

listToError :: a -> [b] -> Either a b
listToError x []    = Left x
listToError _ (y:_) = Right y

runError :: Either String t -> t
runError (Left x)   = error x
runError (Right x)  = x
                     