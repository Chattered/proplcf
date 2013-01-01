-- Basic conversions and conversionals

module Conversions where

import Bootstrap hiding (matchMP)
import Propositional
import Utils
import Control.Monad.Error

-- Conversions wrap functions which take terms and derive equations. Each 
-- equation has an lhs which is the original term.
newtype Conv a = Conv (Term a -> [Theorem a])

applyC :: Conv a -> Term a -> [Theorem a]
applyC (Conv c) term = c term

-- Use a conversion to rewrite a theorem
convMP :: Conv String -> Theorem String -> [Theorem String]
convMP c thm = do eq  <- applyC c (theoremTerm thm)
                  imp <- matchMP eqMP eq
                  mp imp thm

-- Apply a conversion to the antecedent of a conditional
antC :: Conv String -> Conv String
antC (Conv c) = Conv f
  where f (p :=>: q) = c p >>= matchMP substLeft'
          where substLeft' = instM (Var . avoid (vars q)) [("p",q)] substLeft
        f _          = []
  
-- Apply a conversion to the consequent of a conditional        
conclC :: Conv String -> Conv String
conclC (Conv c) = Conv f
  where f (p :=>: q) = c q >>= matchMP substRight'
          where substRight' = instM (Var . avoid (vars p)) [("p",p)] substRight
        f _          = []

-- Apply a conversion to the body of a negation
notC :: Conv String -> Conv String
notC (Conv c) = Conv f 
  where f (Not p) = c p >>= matchMP substNot
        f _       = []
        
-- Attempt the left conversion, and if it fails, attempt the right
orC :: Conv a -> Conv a -> Conv a
orC (Conv c) (Conv c') = Conv f
  where f t = c t `mplus` c' t
        
-- Try all conversions which succeed
tryC :: [Conv a] -> Conv a
tryC = foldr orC failC

-- Apply a conversion conditionally
ifC :: (Term a -> Bool) -> Conv a -> Conv a
ifC p c = Conv (\t -> if p t then applyC c t else [])

-- Apply one conversion after another
thenC :: Conv String -> Conv String -> Conv String
thenC c c' = Conv f
  where f t = do thm   <- applyC c t
                 r     <- rhs (theoremTerm thm)
                 thm'  <- applyC c' r
                 thm'' <- matchMP trans thm
                 matchMP thm'' thm'
        rhs (Not ((p :=>: q) :=>: Not (r :=>: s))) | p == s && q == r = return q
        rhs _  = []
        
-- The zero for orConv and identity for thenConv: always succeeds
allC :: Conv String
allC = Conv (\t -> return $ instL [t] reflEq)

-- The identity for orConv and zero for thenConv: always fails
failC :: Conv a
failC = Conv (const [])

-- Sequence conversions
everyC :: [Conv String] -> Conv String
everyC = foldl thenC allC
        
isImp :: Term a -> Bool 
isImp (p :=>: q) = True
isImp _          = False

isNeg :: Term a -> Bool
isNeg (Not p) = True
isNeg _       = False

-- Apply a conversion to the first applicable term on a depth first search
depthConv1 :: Conv String -> Conv String
depthConv1 c = tryC [ c
                    , ifC isNeg (notC c')
                    , ifC isImp (antC c' `orC` conclC c') ]
  where c' = depthConv1 c
               
-- Given ⊦ P → Q and ⊦ R, attempt to match P and R and then apply mp
matchMP :: Theorem String -> Theorem String -> [Theorem String]
matchMP imp ant = 
  case (theoremTerm imp, theoremTerm ant) of
      (p :=>: q, p') -> do insts <- match p p'
                           mp (instM Var insts imp) ant
      _ -> []
      
-- Convert a double-negated term by eliminating the double-negation.
dblNegC :: Conv String
dblNegC = Conv c
  where c (Not (Not p)) = return $ instL [p] dblNegEq
        c _             = []
        dblNegEq = head $ matchMP (head $ matchMP conjI dblNegElim) dblNegIntro

-- Swap the first two hypotheses of a conditional 
swapC :: Conv String
swapC = Conv c
  where c (p :=>: q :=>: r) = return $ instL [p,q,r] swapT
        c _                 = []
        
-- Convert x <=> y to y <=> x
symConv :: Conv String
symConv = Conv c
  where c (Not ((p :=>: q) :=>: Not (r :=>: s))) | p == s && q == r =
          return $ instL [p,q] symEq
        c _                                      = []

-- Uncurry the first two hypotheses of a conditional
uncurry2 :: Conv String
uncurry2 = Conv c
  where c (p :=>: q :=>: r) = return $ instL [p,q,r] Bootstrap.uncurry
        c _                 = []
        
-- Curry the first hypothesis
curry2 :: Conv String
curry2 = Conv c
  where c (Not (p :=>: Not q) :=>: r) = 
          return $ instL [p,q,r] (head $ convMP symConv Bootstrap.uncurry)
        c _                           = []