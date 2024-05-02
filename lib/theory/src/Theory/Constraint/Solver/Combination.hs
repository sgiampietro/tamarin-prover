{-# LANGUAGE FlexibleInstances #-}

-- Module to deal with solving linear equations and finding out how to combine
-- terms to form target indicators
--

module Theory.Constraint.Solver.Combination
  --( Polynom(..)
  --, AnnotatedGoal
  --)
  (
    allExponentsOf
  )
where

import GHC.Real
import qualified Data.Set                          as S
import Data.List ( (\\), intersect )

import qualified Data.Vector                       as V
import qualified Data.Matrix                       as Mx

import Term.DHMultiplication
import Term.LTerm -- (LNTerm)

import Theory.Constraint.System.Constraints

-- import Data.Poly.Multi.Laurent --(e.g. from https://github.com/Bodigrim/poly )
-- we will use laurent polynomials over a1,..,an to represent the field R(a1,...,an)

-- import Matrix -- (e.g. from https://github.com/Carnagion/Haskell-Matrices)
-- to solve linear equations, we will use matrixes with coefficients over the Laurent "field"
-- I think this only requires to prove they are an instance of the "Num" class
-- and its subclass "Fractional"



-- data Polynomial 


--fromIntegerLNTerm :: Integer -> LNTerm
--fromIntegerLNTerm (IS i)   = int2LNTerm i

int2LNTerm :: Integer -> LNTerm
int2LNTerm 0 = fAppdhZero
int2LNTerm 1 = fAppdhOne
int2LNTerm n = fAppdhPlus (fAppdhOne, int2LNTerm $ n-1)

rationalLNTerm :: Integer -> Integer -> LNTerm
rationalLNTerm n 0 = error "division by zero"
rationalLNTerm n d = fAppdhMult (fromInteger n, fAppdhInv $ fromInteger d)

instance Num (Term (Lit Name LVar)) where
  t1 + t2 = fAppdhPlus (t1,t2)
  t1 - t2 = fAppdhPlus (t1, fAppdhMinus t2)
  t1 * t2 = fAppdhTimesE (t1,t2)
  negate = fAppdhMinus
  abs t = t
  signum t = fAppdhOne
  fromInteger = int2LNTerm

instance Fractional (Term (Lit Name LVar)) where
  t1 / t2 = fAppdhTimesE (t1, fAppdhInv t2)
  recip t = fAppdhInv t
  fromRational (n:%d) = rationalLNTerm n d

gTerm2Exp ::  LNTerm -> LNTerm
gTerm2Exp t@(LIT l) = t
gTerm2Exp t@(FAPP (DHMult o) ts) = case ts of
    -- [ t1, t2 ] | o == dhMultSym   -> this shouldn't happen. only root terms. 
    [ t1, t2 ] | o == dhTimesSym   -> t
    [ t1, t2 ] | o == dhTimesESym   -> t
    [ t1, t2 ] | o == dhExpSym   -> t2
    [ t1, t2 ] | o == dhPlusSym   -> t
    [ t1 ]     | o == dhGinvSym    -> (FAPP (DHMult dhMinusSym) [gTerm2Exp t1])
    [ t1 ]     | o == dhInvSym    -> t
    [ t1 ]     | o == dhMinusSym    -> t
    [ t1 ]     | o == dhMuSym    -> t
    [ t1 ]     | o == dhBoxSym    -> gTerm2Exp t
    [ t1 ]     | o == dhBoxESym    -> t1
    []         | o == dhZeroSym    -> t
    []         | o == dhEgSym    -> (FAPP (DHMult dhZeroSym) [])
    []         | o == dhOneSym    -> t
    _                               -> error $ "unexpected term form: `"++show t++"'"



allExponentsOf :: S.Set LNTerm -> LNTerm -> [LNTerm]
allExponentsOf tis target =
  S.toList $ S.union (S.unions $ S.map (S.fromList . eTermsOf) tis) (S.fromList $ eTermsOf target)

allNBExponents :: [LNTerm] -> [LNTerm] -> ([LNTerm], [LNTerm])
allNBExponents nbasis allexp = (nbasis `intersect` allexp, allexp \\ nbasis)


createMatrix :: [LNTerm] -> LNTerm -> Matrix LNTerm
createMatrix terms target = Mx.indentity $ length terms

-- polynomials, how should we represent them? maps? vectors?


{-
parseToPoly ::  [LNTerm] -> LNTerm  -> Polynomial
parseToPoly nb t@(LIT l) = if (member t nb) then (CONSTANT) else (VARIABLE) 
parseToPoly nb (FAPP (DHMult o) ts) = case ts of
    -- [ t1, t2 ] | o == dhMultSym   -> this shouldn't happen. only root terms. 
    [ t1, t2 ] | o == dhTimesSym   -> polymult (parseToPoly t1) (parseToPoly t2)
    [ t1, t2 ] | o == dhTimesESym   -> polymult (parseToPoly t1) (parseToPoly t2)
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

getPolynomial::  [LNTerm] -> LNTerm -> Polynomial
getPolynomial nb = parseToPoly nb


createTargetEqs :: S.Set LNTerm -> LNTerm -> [PolynomialsOverPolyField]
createTargetEqs terms target = (map (getPolynomial nb) terms)

-}


