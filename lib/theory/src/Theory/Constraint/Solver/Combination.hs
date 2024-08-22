

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
    solveIndicatorGauss,
    solveIndicatorGaussProto,
    parseToMap,
    gTerm2Exp,
    getvalue
  )
where


import qualified Data.Set                          as S
import Data.List ( (\\), intersect )
import qualified Data.Map                          as Map
-- we use maps to construct the linear system of equation we will need to solve. 

--import qualified Data.Vector                       as V
-- import qualified Theory.Tools.Matrix                       as Mx
import Theory.Tools.Gauss                 

-- import           Control.Monad.Trans.Reader   

import Term.DHMultiplication
import Term.LTerm -- (LNTerm)

-- import Theory.Constraint.System.Constraints
import Debug.Trace
import Data.ByteString.Builder (word16BE)


gTerm2Exp ::  LNTerm -> LNTerm
gTerm2Exp t@(LIT l) = if (isGVar t || isPubGVar t) then (fAppdhOne) else t
gTerm2Exp t@(FAPP (DHMult o) ts) = case ts of
    [ t1, t2 ] | o == dhMultSym   -> simplifyraw $ (FAPP (DHMult dhPlusSym) [gTerm2Exp t1, gTerm2Exp t2])
    [ t1, t2 ] | o == dhTimesSym   -> t
    [ t1, t2 ] | o == dhTimesESym   -> t
    [ t1, t2 ] | o == dhExpSym   ->  simplifyraw $ (FAPP (DHMult dhTimesESym) [gTerm2Exp t1, gTerm2Exp t2])
    [ t1, t2 ] | o == dhPlusSym   -> t
    [ t1 ]     | o == dhGinvSym    ->  simplifyraw $ (FAPP (DHMult dhMinusSym) [gTerm2Exp t1])
    [ t1 ]     | o == dhInvSym    -> t
    [ t1 ]     | o == dhMinusSym    -> t
    [ t1 ]     | o == dhMuSym    -> t
    --[ t1 ]     | o == dhBoxSym    -> gTerm2Exp t1
    --[ t1 ]     | o == dhBoxESym    -> gTerm2Exp t1
    []         | o == dhZeroSym    -> t
    []         | o == dhEgSym    ->  simplifyraw $ (FAPP (DHMult dhZeroSym) [])
    []         | o == dhOneSym    -> t
    _                               -> error $ "unexpected term form: `"++show t++"'"


allExponentsOf :: [LNTerm] -> LNTerm -> [LNTerm]
allExponentsOf tis target =
  S.toList $ S.union (S.unions $ map (S.fromList . eTermsOf) tis) (S.fromList $ eTermsOf target)
-- to get monomials that are also product of exponents, probably just need to modify the 
-- "eTermsOf" function to also take products of E-terms. 

allNBExponents :: [LNTerm] -> [LNTerm] -> ([LNTerm], [LNTerm])
allNBExponents nbasis allexp = (nbasis `intersect` allexp, allexp \\ nbasis)

-- polynomials, how should we represent them? maps? vectors?

combineMaps :: LNTerm -> LNTerm -> LNTerm -> LNTerm
combineMaps key oldvalue newvalue = simplifyraw $ fAppdhPlus (oldvalue,newvalue)


-- THIS FUNCTION ASSUMES THAT THE INPUT TERMS ARE IN NORMAL FORM, i.e. 
-- EACH MONOMIAL (which we assume of type E) is of the form 
-- "(m1+m2+...+mk)" where mi = (e1*e2*...*el), and ei are either literals or inv(lit).

-- make sure the vars do not contain any inverse, but only pure LIT terms. 
getkeyfromProd :: [LNTerm] -> LNTerm -> LNTerm 
getkeyfromProd vars t@(LIT l) = if (elem t vars) then t else fAppdhOne
getkeyfromProd vars t@(FAPP (DHMult o) ts) = case ts of
    [ t1, t2 ] | o == dhTimesSym   -> (case t1 of
        (LIT l) -> if (elem t1 vars) then simplifyraw $ fAppdhTimesE (t1, getkeyfromProd vars t2) else getkeyfromProd vars t2
        _       -> simplifyraw $ fAppdhTimesE (getkeyfromProd vars t1, getkeyfromProd vars t2))
    [ t1, t2 ] | o == dhTimesESym   -> (case t1 of
        (LIT l) -> if (elem t1 vars) then simplifyraw $ fAppdhTimesE (t1, getkeyfromProd vars t2) else getkeyfromProd vars t2
        _       -> simplifyraw $ fAppdhTimesE (getkeyfromProd vars t1, getkeyfromProd vars t2))
    [ t1 ]     | o == dhInvSym    -> if (elem t1 vars) then t else fAppdhOne
    [ t1 ]     | o == dhMinusSym    -> getkeyfromProd vars t1
    [ t1 ]     | o == dhMuSym    -> if (elem t1 vars) then fAppdhMu t1 else fAppdhOne --TODO: not sure what to do here? t1 is actually a G term??
    []         | o == dhZeroSym    -> fAppdhOne
    []         | o == dhOneSym    -> fAppdhOne
    _                               -> error $ "this shouldn't have happened: `"++show t++"'"

getcoefromProd :: [LNTerm] -> LNTerm -> LNTerm 
getcoefromProd vars t@(LIT l) = if (elem t vars) then fAppdhOne else t
getcoefromProd vars t@(FAPP (DHMult o) ts) = case ts of
    [ t1, t2 ] | o == dhTimesSym   -> (case t1 of
        (LIT l) -> if (elem t1 vars) then getcoefromProd vars t2 else simplifyraw $ fAppdhTimesE (t1, getcoefromProd vars t2) 
        _       -> simplifyraw $ fAppdhTimesE (getcoefromProd vars t1, getcoefromProd vars t2))
    [ t1, t2 ] | o == dhTimesESym   -> (case t1 of
        (LIT l) -> if (elem t1 vars) then getcoefromProd vars t2 else simplifyraw $ fAppdhTimesE (t1, getcoefromProd vars t2) 
        _       -> simplifyraw $ fAppdhTimesE (getcoefromProd vars t1, getcoefromProd vars t2))
    [ t1 ]     | o == dhInvSym    -> if (elem t1 vars) then fAppdhOne else t -- check how to deal with inverse!
    [ t1 ]     | o == dhMinusSym    -> simplifyraw $ fAppdhMinus (getcoefromProd vars t1)
    [ t1 ]     | o == dhMuSym    -> if (elem t1 vars) then fAppdhOne else fAppdhMu t1  --TODO: not sure what to do here? t1 is actually a G term??
    []         | o == dhZeroSym    -> t
    []         | o == dhOneSym    -> t
    _                               -> error $ "this shouldn't have happened, unexpected term form: `"++show t++"'"


addToMap :: Map.Map LNTerm LNTerm -> [LNTerm] -> LNTerm  -> Map.Map LNTerm LNTerm 
addToMap currmap vars t@(LIT l) = if (elem t vars) then (Map.insertWithKey combineMaps t fAppdhOne currmap) else (Map.insertWithKey combineMaps fAppdhOne t currmap) 
addToMap currmap vars t@(FAPP (DHMult o) ts) = case ts of
    -- [ t1, t2 ] | o == dhMultSym   -> this shouldn't happen. only root terms. 
    [ t1, t2 ] | o == dhTimesSym   -> Map.insertWithKey combineMaps (getkeyfromProd vars t) (getcoefromProd vars t) currmap
    [ t1, t2 ] | o == dhTimesESym   -> Map.insertWithKey combineMaps (getkeyfromProd vars t) (getcoefromProd vars t) currmap
    -- [ t1, t2 ] | o == dhExpSym   -> this shouldn't happen. only root terms. 
    [ t1, t2 ] | o == dhPlusSym   -> addToMap (addToMap currmap vars t1) vars t2
    -- [ t1 ]     | o == dhGinvSym    -> this shouldn't happen. only root terms.
    [ t1 ]     | o == dhInvSym    -> Map.insertWithKey combineMaps (getkeyfromProd vars t) (getcoefromProd vars t) currmap
    [ t1 ]     | o == dhMinusSym    -> Map.insertWithKey combineMaps (getkeyfromProd vars t1) (simplifyraw $ fAppdhMinus $ getcoefromProd vars t1) currmap
    [ t1 ]     | o == dhMuSym    -> Map.insertWithKey combineMaps (getkeyfromProd vars t) (getcoefromProd vars t) currmap
    --[ t1 ]     | o == dhBoxSym    -> FdhBox t1 (this function should be called on UN-boxed term)
    --[ t1 ]     | o == dhBoxESym    -> FdhBoxE t1 (this function should be called on UN-boxed term)
    []         | o == dhZeroSym    -> Map.empty
    []         | o == dhOneSym    -> (Map.insertWithKey combineMaps fAppdhOne fAppdhOne currmap)
    _                               -> error $ "this shouldn't have happened, unexpected term form: `"++show t++"'"


parseToMap ::  [LNTerm] -> LNTerm  -> Map.Map LNTerm LNTerm 
parseToMap = addToMap Map.empty


getvalue :: Map.Map LNTerm LNTerm -> LNTerm -> LNTerm 
getvalue somemap key = case Map.lookup key somemap of
  Just t -> t
  Nothing -> fAppdhZero 

createMatrix :: [LNTerm] -> [LNTerm] -> LNTerm -> Matrix LNTerm
createMatrix nb terms target = 
    let (nbexp, vars) = allNBExponents nb (allExponentsOf terms target)
        polynomials = map (parseToMap vars) terms
        targetpoly = parseToMap vars target
        allkeys =  S.toList $ S.fromList $ concat ((Map.keys targetpoly):(map Map.keys polynomials))
        -- row = map( \i -> getvalue targetpoly i) allkeys 
    in 
  trace (show ("THIS IS THE MATRIX I GET, vars, targetpoly, polynoimals, allkey ",nb,vars, targetpoly, polynomials, allkeys)) (map (\key -> ((map (\p -> getvalue p key) polynomials )++ [getvalue targetpoly key])) allkeys) -- todo: double check if row/column is ok or needs to be switched




solveIndicatorGauss :: [LNTerm] -> [LNTerm] -> LNTerm -> Maybe [LNTerm]
solveIndicatorGauss nb terms target = solveMatrix fAppdhZero $ createMatrix (nb) (map gTerm2Exp terms) (gTerm2Exp target)
-- TODO: these terms are possible G, terms. We assume here that our terms are always of the form
-- 'g'^x for some fixed g, so we need to transform them to their exponent values. 



-- PART FOR PROTOCOL ACTION INDICATORS

getVariablesOf :: [LNTerm] -> [LNTerm]
getVariablesOf tis =
  S.toList (S.unions $ map (S.fromList . varTermsOf) tis) 

stripVarsProd :: LNTerm -> (LNTerm, LNTerm)
stripVarsProd t@(LIT l) = error "this shouldn't happen" 
stripVarsProd t@(FAPP (DHMult o) ts) = case ts of
    [ t1, t2 ] | o == dhTimesSym   -> if isvarEVar t1 then (t1,t2) else (t2,t1)
    [ t1, t2 ] | o == dhTimesESym   -> if isvarEVar t1 then (t1,t2) else (t2,t1)
    _                               -> error $ "this shouldn't have happened, unexpected term form: `"++show t++"'"

stripVars :: LNTerm -> (LNTerm, (LNTerm, LNTerm)) -- summed var, (multiplied var, term)
stripVars t@(LIT l) = error "this shouldn't happen" 
stripVars t@(FAPP (DHMult o) ts) = case ts of
    [ t1, t2 ] | o == dhPlusSym   -> if isvarEVar t1 then (t1, stripVarsProd t2) else (t2, stripVarsProd t1)
    _                               -> error $ "this shouldn't have happened, unexpected term form: `"++show t++"'"


oneIfOne :: LNTerm -> LNTerm
oneIfOne fAppdhOne = fAppdhOne
oneIfOne _ = fAppdhZero

createMatrixProto :: [LNTerm] -> LNTerm -> LNTerm -> (LNTerm, LNTerm, Matrix LNTerm)
createMatrixProto nb term target = 
    let (nbexp, vars) = allNBExponents nb (allExponentsOf [term] target)
        (z1,(w1,term2)) = trace (show ("stripvars on", term, nb, nbexp, vars)) $ stripVars term
        polynomial = parseToMap vars term2 -- this term now contains the introduced W and V variables. 
        targetpoly = parseToMap vars target
        allkeys =  S.toList $ S.fromList $ concat ((Map.keys targetpoly):[Map.keys polynomial])
        -- row = map( \i -> getvalue targetpoly i) allkeys 
    in 
  (w1, z1, map (\key -> ( getvalue polynomial key):(oneIfOne key):[getvalue targetpoly key]) allkeys) -- todo: double check if row/column is ok or needs to be switched

-- w1 is multiplied term, z1 is the summed term. 


solveIndicatorGaussProto :: [LNTerm] -> LNTerm -> LNTerm -> Maybe [(LVar, LNTerm)]
solveIndicatorGaussProto nb term target = 
    let (w1, z2, matriz) = createMatrixProto (nb) (gTerm2Exp term) (gTerm2Exp target)
        solution = solveMatrix fAppdhZero matriz
    in
  case solution of 
    Nothing -> Nothing
    Just ([t1,t2]) -> case (getVar w1, getVar z2) of
                        (Just varw1, Just varz2) -> Just [(varw1, t1), (varz2, t2)]
                        _ -> Nothing


-- TODO: these terms are possible G, terms. We assume here that our terms are always of the form
-- 'g'^x for some fixed g, so we need to transform them to their exponent values. 
