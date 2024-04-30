-- Module to deal with solving linear equations and finding out how to combine
-- terms to form target indicators
--

module Theory.Constraint.Solver.Combination
  --( Polynom(..)
  --, AnnotatedGoal
  --)
where

import Theory.Constraint.System.Constraints

import Data.Poly.Multi.Laurent --(e.g. from https://github.com/Bodigrim/poly )
-- we will use laurent polynomials over a1,..,an to represent the field R(a1,...,an)

import Matrix -- (e.g. from https://github.com/Carnagion/Haskell-Matrices)
-- to solve linear equations, we will use matrixes with coefficients over the Laurent "field"
-- I think this only requires to prove they are an instance of the "Num" class
-- and its subclass "Fractional"

import qualified Data.Set                          as S
import Term.DHMultiplication
import Term.LTerm (LNTerm)


data Polynomial 


gTerm2Exp ::  LNTerm -> LNTerm
gTerm2Exp t@(LIT l) nb = t
gTerm2Exp t@(FAPP (DHMult o) ts) nb = case ts of
    -- [ t1, t2 ] | o == dhMultSym   -> this shouldn't happen. only root terms. 
    [ t1, t2 ] | o == dhTimesSym   -> t
    [ t1, t2 ] | o == dhTimes2Sym   -> t
    [ t1, t2 ] | o == dhExpSym   -> t2 
    [ t1, t2 ] | o == dhPlusSym   -> t
    [ t1 ]     | o == dhGinvSym    -> (FAPP (DHMult dhMinusSym) [gTerm2Exp t1])
    [ t1 ]     | o == dhInvSym    -> t 
    [ t1 ]     | o == dhMinusSym    -> t
    [ t1 ]     | o == dhMuSym    -> t
    [ t1 ]     | o == dhBoxSym    -> gTerm2Exp t
    [ t1 ]     | o == dhBoxESym    -> t1
    []         | o == dhZeroSym    -> t
    []         | o == dhEgSym    -> (FAPP (DHMult dhZeroSym []))  
    []         | o == dhOneSym    -> t
    _                               -> error $ "unexpected term form: `"++show t++"'"


parseToPoly ::  [LNTerm] -> LNTerm  -> Polynomial
parseToPoly nb t@(LIT l) = if (member t nb) then (CONSTANT) else (VARIABLE) 
parseToPoly nb (FAPP (DHMult o) ts) = case ts of
    -- [ t1, t2 ] | o == dhMultSym   -> this shouldn't happen. only root terms. 
    [ t1, t2 ] | o == dhTimesSym   -> polymult (parseToPoly t1) (parseToPoly t2)
    [ t1, t2 ] | o == dhTimes2Sym   -> polymult (parseToPoly t1) (parseToPoly t2)
    -- [ t1, t2 ] | o == dhExpSym   -> this shouldn't happen. only root terms. 
    [ t1, t2 ] | o == dhPlusSym   -> polyadd (parseToPoly t1) (parseToPoly t2)
    -- [ t1 ]     | o == dhGinvSym    -> this shouldn't happen. only root terms.
    [ t1 ]     | o == dhInvSym    -> -- TODO. not sure how to deal with this case. 
    [ t1 ]     | o == dhMinusSym    -> polyminus (parseToPoly t1) (parseToPoly t2)
    [ t1 ]     | o == dhMuSym    -> FdhMu  t1
    [ t1 ]     | o == dhBoxSym    -> FdhBox  t1
    [ t1 ]     | o == dhBoxESym    -> FdhBoxE  t1
    []         | o == dhZeroSym    -> polyzero
    []         | o == dhEgSym    -> polyzero  
    []         | o == dhOneSym    -> polyone (CONSTANT one)
    _                               -> error $ "unexpected term form: `"++show t++"'"

allExponentsOf :: S.Set LNTerm -> LNTerm -> [LNTerm]
allExponentsOf tis target = 
  toList $ S.union (S.unions $ S.map (S.fromList . eTermsOf) tis) (S.fromList $ eTermsOf target)

allNBExponents :: [LNTerm] -> [LNTerm] -> ([LNTerm], [LNTerm])
allNBExponents nbasis allexp = (intersect nbasis allexp, allexp \\ nbasis)

getPolynomial::  [LNTerm] -> LNTerm -> Polynomial
getPolynomial nb = parseToPoly nb


createTargetEqs :: S.Set LNTerm -> LNTerm -> [PolynomialsOverPolyField]
createTargetEqs terms target = (map (getPolynomial nb) terms)