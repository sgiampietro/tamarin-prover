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
import qualified Data.Map                          as Map
-- we use maps to construct the linear system of equation we will need to solve. 

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

combineMaps :: LNTerm -> LNTerm -> LNTerm -> LNTerm
combineMaps key oldvalue newvalue = fAppdhPlus (oldvalue,newvalue)

Map.insertWithKey

-- THIS FUNCTION ASSUMES THAT THE INPUT TERMS ARE IN NORMAL FORM, i.e. 
-- EACH MONOMIAL (which we assume of type E) is of the form 
-- "(m1+m2+...+mk)" where mi = (e1*e2*...*el), and ei are either literals or inv(lit).

-- make sure the vars do not contain any inverse, but only pure LIT terms. 
getkeyfromProd :: [LNTerm] -> LNTerm -> LNTerm 
getkeyfromProd vars t@(LIT l) = if (member t vars) then t else fAppdhOne
getkeyfromProd vars t@(FAPP (DHMult o) ts) = case ts of
    [ t1, t2 ] | o == dhTimesSym   -> (case t1 of
        (LIT l) -> if (member t1 vars) then fAppdhTimes (t1, getkeyfromProd vars t2) else getkeyfromProd vars t2
        _       -> fAppdhTimes (getkeyfromProd vars t1, getkeyfromProd vars t2))
    [ t1, t2 ] | o == dhTimesESym   -> (case t1 of
        (LIT l) -> if (member t1 vars) then fAppdhTimes (t1, getkeyfromProd vars t2) else getkeyfromProd vars t2
        _       -> fAppdhTimes (getkeyfromProd vars t1, getkeyfromProd vars t2))
    [ t1 ]     | o == dhInvSym    -> if (member t1 vars) then t else fAppdhOne
    [ t1 ]     | o == dhMinusSym    -> getkeyfromProd vars t1
    [ t1 ]     | o == dhMuSym    -> if (member t1 vars) then fAppdhMu t1 else fAppdhOne --TODO: not sure what to do here? t1 is actually a G term??
    []         | o == dhZeroSym    -> fAppdhOne
    []         | o == dhOneSym    -> fAppdhOne
    _                               -> error $ "this shouldn't have happened: `"++show t++"'"


getcoefromProd :: [LNTerm] -> LNTerm -> LNTerm 
getcoefromProd vars t@(LIT l) = if (member t vars) then fAppdhOne else t
getcoefromProd vars t@(FAPP (DHMult o) ts) = case ts of
    [ t1, t2 ] | o == dhTimesSym   -> (case t1 of
        (LIT l) -> if (member t1 vars) then getcoefromProd vars t2 else fAppdhTimes (t1, getcoefromProd vars t2) 
        _       -> fAppdhTimes (getcoefromProd vars t1, getcoefromProd vars t2))
    [ t1, t2 ] | o == dhTimesESym   -> (case t1 of
        (LIT l) -> if (member t1 vars) then getcoefromProd vars t2 else fAppdhTimes (t1, getcoefromProd vars t2) 
        _       -> fAppdhTimes (getcoefromProd vars t1, getcoefromProd vars t2))
    [ t1 ]     | o == dhInvSym    -> if (member t1 vars) then fAppdhOne else t -- check how to deal with inverse!
    [ t1 ]     | o == dhMinusSym    -> fAppdhMinus (getcoefromProd vars t1)
    [ t1 ]     | o == dhMuSym    -> if (member t1 vars) then fAppdhOne else fAppdhMu t1  --TODO: not sure what to do here? t1 is actually a G term??
    []         | o == dhZeroSym    -> t
    []         | o == dhOneSym    -> t
    _                               -> error $ "this shouldn't have happened: `"++show t++"'"



addToMap ::  Map.Map LNTerm LNTerm -> [LNTerm] -> LNTerm  -> Map.Map LNTerm LNTerm 
addToMap currmap vars t@(LIT l) = if (member t vars) then (Map.insertWithKey combineMaps t fAppdhOne currmap) else (Map.insertWithKey combineMaps fAppdhOne t currmap) 
addToMap currmap vars t@(FAPP (DHMult o) ts) = case ts of
    -- [ t1, t2 ] | o == dhMultSym   -> this shouldn't happen. only root terms. 
    [ t1, t2 ] | o == dhTimesSym   -> Map.insertWithKey combineMaps (getkeyfromProd vars t) (getcoefromProd vars t) currmap
    [ t1, t2 ] | o == dhTimesESym   -> Map.insertWithKey combineMaps (getkeyfromProd vars t) (getcoefromProd vars t) currmap
    -- [ t1, t2 ] | o == dhExpSym   -> this shouldn't happen. only root terms. 
    [ t1, t2 ] | o == dhPlusSym   -> addToMap (addToMap currmap vars t1) vars t2
    -- [ t1 ]     | o == dhGinvSym    -> this shouldn't happen. only root terms.
    [ t1 ]     | o == dhInvSym    -> Map.insertWithKey combineMaps (getkeyfromProd vars t) (getcoefromProd vars t) currmap
    [ t1 ]     | o == dhMinusSym    -> Map.insertWithKey combineMaps (getkeyfromProd vars t1) (fAppdhMinus $ getcoefromProd vars t1) currmap
    [ t1 ]     | o == dhMuSym    -> Map.insertWithKey combineMaps (getkeyfromProd vars t) (getcoefromProd vars t) currmap
    --[ t1 ]     | o == dhBoxSym    -> FdhBox t1 (this function should be called on UN-boxed term)
    --[ t1 ]     | o == dhBoxESym    -> FdhBoxE t1 (this function should be called on UN-boxed term)
    []         | o == dhZeroSym    -> Map.empty
    []         | o == dhOneSym    -> (Map.insertWithKey combineMaps fAppdhOne fAppdhOne currmap)
    _                               -> error $ "unexpected term form: `"++show t++"'"


parseToMap ::  [LNTerm] -> LNTerm  -> Map.Map LNTerm LNTerm 
parseToMap = addToMap Map.empty

{-
getPolynomial::  [LNTerm] -> LNTerm -> Polynomial
getPolynomial nb = parseToPoly nb


createTargetEqs :: S.Set LNTerm -> LNTerm -> [PolynomialsOverPolyField]
createTargetEqs terms target = (map (getPolynomial nb) terms)

-}


