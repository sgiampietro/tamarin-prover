

-- Module to deal with solving linear equations and finding out how to combine
-- terms to form target indicators
--

module Theory.Constraint.Solver.Combination
  --( Polynom(..)
  --, AnnotatedGoal
  --)
  (
    allExponentsOf,
    getcoefromProd,
    getkeyfromProd,
    allNBExponents,
    createMatrix,
    solveMatrix,
    parseToMap
  )
where


import qualified Data.Set                          as S
import Data.List ( (\\), intersect )
import qualified Data.Map                          as Map
-- we use maps to construct the linear system of equation we will need to solve. 

--import qualified Data.Vector                       as V
import qualified Theory.Tools.Matrix                       as Mx
import Theory.Tools.Gauss                 

import           Control.Monad.Trans.Reader   

import Term.DHMultiplication
import Term.LTerm -- (LNTerm)

import Theory.Constraint.System.Constraints

import Term.Maude.Process

import Term.Rewriting.Norm

-- import Data.Poly.Multi.Laurent --(e.g. from https://github.com/Bodigrim/poly )
-- we will use laurent polynomials over a1,..,an to represent the field R(a1,...,an)

-- import Matrix -- (e.g. from https://github.com/Carnagion/Haskell-Matrices)
-- to solve linear equations, we will use matrixes with coefficients over the Laurent "field"
-- I think this only requires to prove they are an instance of the "Num" class
-- and its subclass "Fractional"



-- data Polynomial 


--fromIntegerLNTerm :: Integer -> LNTerm
--fromIntegerLNTerm (IS i)   = int2LNTerm i

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

-- polynomials, how should we represent them? maps? vectors?

combineMaps :: MaudeHandle -> LNTerm -> LNTerm -> LNTerm -> LNTerm
combineMaps hnd key oldvalue newvalue = simplify hnd $ fAppdhPlus (oldvalue,newvalue)


-- THIS FUNCTION ASSUMES THAT THE INPUT TERMS ARE IN NORMAL FORM, i.e. 
-- EACH MONOMIAL (which we assume of type E) is of the form 
-- "(m1+m2+...+mk)" where mi = (e1*e2*...*el), and ei are either literals or inv(lit).

-- make sure the vars do not contain any inverse, but only pure LIT terms. 
getkeyfromProd :: MaudeHandle -> [LNTerm] -> LNTerm -> LNTerm 
getkeyfromProd hnd vars t@(LIT l) = if (elem t vars) then t else fAppdhOne
getkeyfromProd hnd vars t@(FAPP (DHMult o) ts) = case ts of
    [ t1, t2 ] | o == dhTimesSym   -> (case t1 of
        (LIT l) -> if (elem t1 vars) then simplify hnd $ fAppdhTimesE (t1, getkeyfromProd hnd vars t2) else getkeyfromProd hnd vars t2
        _       -> simplify hnd $ fAppdhTimesE (getkeyfromProd hnd vars t1, getkeyfromProd hnd vars t2))
    [ t1, t2 ] | o == dhTimesESym   -> (case t1 of
        (LIT l) -> if (elem t1 vars) then simplify hnd $ fAppdhTimesE (t1, getkeyfromProd hnd vars t2) else getkeyfromProd hnd vars t2
        _       -> simplify hnd $ fAppdhTimesE (getkeyfromProd hnd vars t1, getkeyfromProd hnd vars t2))
    [ t1 ]     | o == dhInvSym    -> if (elem t1 vars) then t else fAppdhOne
    [ t1 ]     | o == dhMinusSym    -> getkeyfromProd hnd vars t1
    [ t1 ]     | o == dhMuSym    -> if (elem t1 vars) then fAppdhMu t1 else fAppdhOne --TODO: not sure what to do here? t1 is actually a G term??
    []         | o == dhZeroSym    -> fAppdhOne
    []         | o == dhOneSym    -> fAppdhOne
    _                               -> error $ "this shouldn't have happened: `"++show t++"'"

getcoefromProd :: MaudeHandle -> [LNTerm] -> LNTerm -> LNTerm 
getcoefromProd hnd vars t@(LIT l) = if (elem t vars) then fAppdhOne else t
getcoefromProd hnd vars t@(FAPP (DHMult o) ts) = case ts of
    [ t1, t2 ] | o == dhTimesSym   -> (case t1 of
        (LIT l) -> if (elem t1 vars) then getcoefromProd hnd vars t2 else simplify hnd $ fAppdhTimesE (t1, getcoefromProd hnd vars t2) 
        _       -> simplify hnd $ fAppdhTimesE (getcoefromProd hnd vars t1, getcoefromProd hnd vars t2))
    [ t1, t2 ] | o == dhTimesESym   -> (case t1 of
        (LIT l) -> if (elem t1 vars) then getcoefromProd hnd vars t2 else simplify hnd $ fAppdhTimesE (t1, getcoefromProd hnd vars t2) 
        _       -> simplify hnd $ fAppdhTimesE (getcoefromProd hnd vars t1, getcoefromProd hnd vars t2))
    [ t1 ]     | o == dhInvSym    -> if (elem t1 vars) then fAppdhOne else t -- check how to deal with inverse!
    [ t1 ]     | o == dhMinusSym    -> simplify hnd $ fAppdhMinus (getcoefromProd hnd vars t1)
    [ t1 ]     | o == dhMuSym    -> if (elem t1 vars) then fAppdhOne else fAppdhMu t1  --TODO: not sure what to do here? t1 is actually a G term??
    []         | o == dhZeroSym    -> t
    []         | o == dhOneSym    -> t
    _                               -> error $ "this shouldn't have happened, unexpected term form: `"++show t++"'"


addToMap ::  MaudeHandle -> Map.Map LNTerm LNTerm -> [LNTerm] -> LNTerm  -> Map.Map LNTerm LNTerm 
addToMap hnd currmap vars t@(LIT l) = if (elem t vars) then (Map.insertWithKey (combineMaps hnd) t fAppdhOne currmap) else (Map.insertWithKey (combineMaps hnd) fAppdhOne t currmap) 
addToMap hnd currmap vars t@(FAPP (DHMult o) ts) = case ts of
    -- [ t1, t2 ] | o == dhMultSym   -> this shouldn't happen. only root terms. 
    [ t1, t2 ] | o == dhTimesSym   -> Map.insertWithKey (combineMaps hnd) (getkeyfromProd hnd vars t) (getcoefromProd hnd vars t) currmap
    [ t1, t2 ] | o == dhTimesESym   -> Map.insertWithKey (combineMaps hnd) (getkeyfromProd hnd vars t) (getcoefromProd hnd vars t) currmap
    -- [ t1, t2 ] | o == dhExpSym   -> this shouldn't happen. only root terms. 
    [ t1, t2 ] | o == dhPlusSym   -> addToMap hnd (addToMap hnd currmap vars t1) vars t2
    -- [ t1 ]     | o == dhGinvSym    -> this shouldn't happen. only root terms.
    [ t1 ]     | o == dhInvSym    -> Map.insertWithKey (combineMaps hnd) (getkeyfromProd hnd vars t) (getcoefromProd hnd vars t) currmap
    [ t1 ]     | o == dhMinusSym    -> Map.insertWithKey (combineMaps hnd) (getkeyfromProd hnd vars t1) (simplify hnd $ fAppdhMinus $ getcoefromProd hnd vars t1) currmap
    [ t1 ]     | o == dhMuSym    -> Map.insertWithKey (combineMaps hnd) (getkeyfromProd hnd vars t) (getcoefromProd hnd vars t) currmap
    --[ t1 ]     | o == dhBoxSym    -> FdhBox t1 (this function should be called on UN-boxed term)
    --[ t1 ]     | o == dhBoxESym    -> FdhBoxE t1 (this function should be called on UN-boxed term)
    []         | o == dhZeroSym    -> Map.empty
    []         | o == dhOneSym    -> (Map.insertWithKey (combineMaps hnd) fAppdhOne fAppdhOne currmap)
    _                               -> error $ "this shouldn't have happened, unexpected term form: `"++show t++"'"


parseToMap ::  MaudeHandle -> [LNTerm] -> LNTerm  -> Map.Map LNTerm LNTerm 
parseToMap hnd = addToMap hnd Map.empty

{-
createMatrix ::  [LNTerm] -> S.Set LNTerm -> LNTerm -> (Mx.Matrix LNTerm, Mx.Matrix LNTerm)
createMatrix nb terms target = 
    let (nbexp, vars) = allNBExponents nb (allExponentsOf terms target)
        polynomials = map (parseToMap vars) (S.toList terms)
        targetpoly = parseToMap vars target
        allkeys = S.toList (S.fromList (concat ((Map.keys targetpoly):(map Map.keys polynomials))) )
        nrow = length allkeys
        ncol = length polynomials
    in 
  (Mx.matrix nrow ncol (\(i,j) -> (polynomials !! (j-1)) Map.! (allkeys !! (i-1))  ), 
    Mx.matrix nrow 1 (\(i,j) -> targetpoly Map.! (allkeys !! (i-1))  ))
-}

getvalue :: Map.Map LNTerm LNTerm -> LNTerm -> LNTerm 
getvalue somemap key = case Map.lookup key somemap of
  Just t -> t
  Nothing -> fAppdhZero 

createMatrix :: MaudeHandle -> [LNTerm] -> S.Set LNTerm -> LNTerm -> Matrix LNTerm
createMatrix hnd nb terms target = 
    let (nbexp, vars) = allNBExponents nb (allExponentsOf terms target)
        polynomials = map (parseToMap hnd vars) (S.toList terms)
        targetpoly = parseToMap hnd vars target
        allkeys = S.toList (S.fromList (concat ((Map.keys targetpoly):(map Map.keys polynomials))) )
        -- row = map ( \i -> getvalue targetpoly i) allkeys 
    in 
  (map (\key -> (map (\p -> getvalue p key) polynomials )++ [getvalue targetpoly key]) allkeys) -- todo: double check if row/column is ok or needs to be switched

simplifymatrix :: MaudeHandle -> Matrix LNTerm -> Matrix LNTerm
simplifymatrix hnd m = m -- map (\row -> map (\el -> simplify hnd el) row ) m

solveMatrix :: MaudeHandle -> Matrix LNTerm -> Maybe (Matrix LNTerm)
solveMatrix hnd m = case (gaussSolveMatrix hnd fAppdhZero m) of 
  Simple mat -> Just (simplifymatrix hnd mat)
  Infinite mat -> Just (simplifymatrix hnd mat)
  Inconsistent -> Nothing

-- to solve the system of equations: G.gaussSolveMatrix
