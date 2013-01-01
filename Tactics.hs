-- Basic tactics and tacticals

module Tactics where

import Propositional    
import Sequent
import Natural
import Utils

-- A goal is a list of hypotheses Γ together with a goal term P, written Γ ? P.
data Goal = Goal [Term String] (Term String) deriving Show

-- A tactic converts a goal Γ ? P into subgoals Γ1 ? Q1, Γ2 ? Q2,...,ΓN ? QN, and
-- a justification function which should send Γ1 ⊢ Q1, Γ2 ⊢ Q2,...,ΓN ⊢ QN to
-- Γ ⊢ P. Tactics are non-deterministic.
newtype Tactic = Tactic (Goal -> [([Goal], [Sequent] -> Sequent)])

-- Tactic application
applyT :: Tactic -> Goal -> [([Goal], [Sequent] -> Sequent)]
applyT (Tactic t) g = t g
    
-- Try all the left tactics, and if they fail, try all the right.
orT :: Tactic -> Tactic -> Tactic
orT (Tactic t) (Tactic t') = Tactic f
    where f g = t g ++ t' g

-- Try the tactics which succeed
tryAllT :: [Tactic] -> Tactic
tryAllT = foldr orT failT

-- Place elements of xs into sublists, mimicking the structure of yss
structureAs :: [a] -> [[b]] -> [[a]]
structureAs xs yss  =
    snd $ mapAccumL (\xs n -> swap (splitAt n xs))
         xs (map length yss)
    where swap (x,y) = (y,x)

-- Apply a tactic, and then apply the elements of a tactic-list pairwise to the
-- resulting subgoals.
thenL :: Tactic -> [Tactic] -> Tactic
thenL (Tactic t) ts = Tactic (f . t)
    where f gsj = do (gs, just) <- gsj
                     if length gs == length ts then
                         (map (applyAll just . unzip)
                                  (sequence $ zipWith applyT ts gs))
                         else []
          applyAll j (gss,js) =
              (concat gss, \thms -> j (zipWith ($) js (thms `structureAs` gss)))

-- Apply a tactic, and then apply a second tactic across all subgoals.   
thenT :: Tactic -> Tactic -> Tactic
thenT t@(Tactic tf) t' = Tactic f
    where f g = do (gs,_) <- tf g 
                   applyT (t `thenL` replicate (length gs) t') g
                          
-- The identity for orT and zero for thenT. Always fails.       
failT :: Tactic
failT = Tactic (const [])
         
-- The identity for thenL and zero for orT. Always succeeds.
allT :: Tactic
allT = Tactic (\g -> [([g], head)])

subset :: Eq a => [a] -> [a] -> Bool
subset xs ys = all (`elem` ys) xs

-- Solve a goal immediately using a sequent with matching
acceptT :: Sequent -> Tactic
acceptT thm = Tactic (\(Goal hyps g) ->
                          [([], const (instMS Var insts thm))
                          | insts <- match (concl thm) g
                          , subset 
                            (assms (instMS Var insts thm))
                            (map (instTermM Var insts) hyps)
                          ])

-- Send Γ ? P → Q to [Γ ∪ {P} ? Q]
mpT :: Tactic
mpT = Tactic t
  where t (Goal hyps g) =
          case g of 
            p :=>: q -> [ ([Goal (insert p hyps) q], \[thm] -> discharge p thm) ]
            _        -> error "Failure: mpT"

-- Solve Γ ∪ {P} ? P
assumeT :: Tactic
assumeT = Tactic (\(Goal hyps g) ->
                      [ ([], \[] -> assume hyp)
                          | hyp <- take 1 $ filter (== g) hyps ])

-- Send Γ ? P ∧ Q to [Γ ? P, Γ ? Q]
conjT :: Tactic
conjT = Tactic (\(Goal hyps g) ->
                    [ ([Goal hyps p, Goal hyps q], \[l,r] -> conjI l r)
                        | Not (p :=>: Not q) <- [g] ])
        
-- Send Γ ? P ∨ Q to [Γ ? P]         
disj1T :: Tactic
disj1T = Tactic (\(Goal hyps g) ->
                  [ ([Goal hyps p], \[thm] -> disj1 q thm)
                      | Not p :=>: q <- [g] ])
         
-- Send Γ ? P ∨ Q to [Γ ? Q]                  
disj2T :: Tactic
disj2T = Tactic (\(Goal hyps g) ->
                  [ ([Goal hyps q], \[thm] -> disj2 p thm)
                      | Not p :=>: q <- [g] ])
         
removes :: (a -> Bool) -> [a] -> [(a, [a])]
removes p xs = f [] xs
  where f _ []                   = []
        f xs (x:xs') | p x       = (x, xs ++ xs') : ys
                     | otherwise = ys
          where ys = f (xs ++ [x]) xs'
         
-- disjET sends Γ ? R to { [ {P} ∪ Γ ? R, {Q} ∪ Γ ? R ] | P ∨ Q ∈ Γ }
disjET :: Tactic
disjET = Tactic (\(Goal hyps g) ->
                  [ ([Goal (p : hyps') g, Goal (q : hyps') g], just)
                    | (Not p :=>: q, hyps') <- removes isDisj hyps ])
  where isDisj (Not _ :=>: _) = True
        isDisj _              = False
        just [case1, case2]   = head $ disjE (assume (Not p :=>: q)) case1 case2

solve :: Term String -> Tactic -> Theorem String
solve t tac = errHead "Unsolved Goals"
  (do (_,thm) <- applyT tac (Goal [] t)
      insts   <- match (concl (thm [])) t
      return $ instM Var insts (seqThm (thm [])))
  where thms            = applyT tac (Goal [] t) 
        errHead err []  = error ("Failure: " ++ err)
        errHead _ (x:_) = x
        rematch         = instMS Var 

-- Examples
commuteDisj :: Theorem String
commuteDisj = 
  solve (p \/ q :=>: q \/ p)
  (mpT 
   `thenT` disjET
   `thenL` [ disj2T `thenT` assumeT
           , disj1T `thenT` assumeT ])   
  