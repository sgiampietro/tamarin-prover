-- Module to deal with solving linear equations and finding out how to combine
-- terms to form target indicators
--

module Theory.Constraint.Solver.Combination
  --( Polynom(..)
  --, AnnotatedGoal
  --)
where

import Theory.Constraint.System.Constraints

--import Math.Algebra.Polynomial.Multivariate -- TODO: install this package. 

import qualified Data.Set                          as S
import Term.DHMultiplication
import Term.LTerm (LNTerm)




allExponentsOf :: S.Set LNTerm -> LNTerm -> S.Set LNTerm
allExponentsOf tis target = 
  S.union (S.unions $ S.map (S.fromList . eTermsOf) tis) (S.fromList $ eTermsOf target)

allNBExponents :: S.Set LNTerm -> S.Set LNTerm -> (S.Set LNTerm, S.Set LNTerm)
allNBExponents nbasis alle = (S.intersection nbasis alle, S.difference alle nbasis)

getPolynomials:: S.Set LNTerm -> LNTerm -> (S.Set LNTerm, S.Set LNTerm) -> [Polynomials]