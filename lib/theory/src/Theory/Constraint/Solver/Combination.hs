

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
    gTerm2Exp',
    getvalue
  )
where


import qualified Data.Set                          as S
import Data.List ( (\\), intersect, nub, permutations )
import qualified Data.Map                          as Map
import Data.Maybe ( fromJust, isJust )
import Data.Tuple (swap)
-- we use maps to construct the linear system of equation we will need to solve. 

--import qualified Data.Vector                       as V
-- import qualified Theory.Tools.Matrix                       as Mx
import Theory.Tools.Gauss

-- import           Control.Monad.Trans.Reader   

import Term.DHMultiplication
import Term.LTerm -- (LNTerm)
import Term.Unification
import Term.Rewriting.Norm
import Term.Substitution

-- import Theory.Constraint.System.Constraints
import Debug.Trace.Ignore
import Control.Monad.Disj (disjunctionOfList)
import           Control.Monad.Reader
import Data.Primitive (mutableByteArrayContents)



gTerm2Exp ::  LNTerm -> LNTerm
gTerm2Exp t@(LIT l) = if (isGVar t || isPubGVar t || isGConst t) then (fAppdhOne) else t
gTerm2Exp t@(FAPP (DHMult o) ts) = case ts of
    [ t1, t2 ] | o == dhMultSym   -> simplifyraw $ (FAPP (DHMult dhPlusSym) [gTerm2Exp t1, gTerm2Exp t2])
    [ t1, t2 ] | o == dhTimesSym   -> t
    [ t1, t2 ] | o == dhTimesESym   -> t
    [ t1, t2 ] | o == dhExpSym   ->  simplifyraw $ (FAPP (DHMult dhTimesESym) [gTerm2Exp t1, gTerm2Exp t2])
    [ t1, t2 ] | o == dhPlusSym   -> t
    [ t1 ]     | o == dhGinvSym    ->  simplifyraw $ (FAPP (DHMult dhMinusSym) [gTerm2Exp t1])
    [ t1 ]     | o == dhInvSym    -> t
    [ t1 ]     | o == dhMinusSym    -> t
    [ t1 ]     | o == dhMuSym    -> FAPP (DHMult dhMuSym) [simplifyraw t1]
    --[ t1 ]     | o == dhBoxSym    -> gTerm2Exp t1
    --[ t1 ]     | o == dhBoxESym    -> gTerm2Exp t1
    []         | o == dhZeroSym    -> t
    []         | o == dhEgSym    ->  simplifyraw $ (FAPP (DHMult dhZeroSym) [])
    []         | o == dhOneSym    -> t
    _                               -> error $ "unexpected term form: `"++show t++"'"
gTerm2Exp t =  error $ "unexpected term form2: `"++show t++"'"

getMuTerms :: LNTerm -> [LNTerm]
getMuTerms t@(LIT l) = []
getMuTerms t@(FAPP (DHMult o) ts) = case ts of
    [ t1, t2 ] | o == dhMultSym   -> nub $ (getMuTerms t1)++(getMuTerms t2)
    [ t1, t2 ] | o == dhTimesSym   -> nub $ (getMuTerms t1)++(getMuTerms t2)
    [ t1, t2 ] | o == dhTimesESym   -> nub $ (getMuTerms t1)++(getMuTerms t2)
    [ t1, t2 ] | o == dhExpSym   ->  nub $ (getMuTerms t1)++(getMuTerms t2)
    [ t1, t2 ] | o == dhPlusSym   -> nub $ (getMuTerms t1)++(getMuTerms t2)
    [ t1 ]     | o == dhGinvSym    -> (getMuTerms t1)
    [ t1 ]     | o == dhInvSym    -> (getMuTerms t1)
    [ t1 ]     | o == dhMinusSym    -> (getMuTerms t1)
    [ t1 ]     | o == dhMuSym    -> [t]
    --[ t1 ]     | o == dhBoxSym    -> gTerm2Exp t1
    --[ t1 ]     | o == dhBoxESym    -> gTerm2Exp t1
    []         | o == dhZeroSym    -> []
    []         | o == dhEgSym    -> []
    []         | o == dhOneSym    -> []
    _                               -> error $ "unexpected term form: `"++show t++"'"

replaceMuTerms :: LNTerm -> Map.Map LNTerm LVar -> LNTerm
replaceMuTerms t@(LIT l) mapp = t
replaceMuTerms t@(FAPP (DHMult o) ts) mapp = case ts of
    [ t1, t2 ] | o == dhMultSym   -> FAPP (DHMult dhMultSym) [replaceMuTerms t1 mapp, replaceMuTerms t2 mapp]
    [ t1, t2 ] | o == dhTimesSym   -> FAPP (DHMult dhTimesSym) [replaceMuTerms t1 mapp, replaceMuTerms t2 mapp]
    [ t1, t2 ] | o == dhTimesESym   -> FAPP (DHMult dhTimesESym) [replaceMuTerms t1 mapp, replaceMuTerms t2 mapp]
    [ t1, t2 ] | o == dhExpSym   ->  FAPP (DHMult dhExpSym) [replaceMuTerms t1 mapp, replaceMuTerms t2 mapp]
    [ t1, t2 ] | o == dhPlusSym   -> FAPP (DHMult dhPlusSym) [replaceMuTerms t1 mapp, replaceMuTerms t2 mapp]
    [ t1 ]     | o == dhGinvSym    -> FAPP (DHMult dhGinvSym) [replaceMuTerms t1 mapp]
    [ t1 ]     | o == dhInvSym    -> FAPP (DHMult dhGinvSym) [replaceMuTerms t1 mapp]
    [ t1 ]     | o == dhMinusSym    -> FAPP (DHMult dhGinvSym) [replaceMuTerms t1 mapp]
    [ t1 ]     | o == dhMuSym    ->  varTerm $ fromJust $ Map.lookup t mapp
    []         | o == dhZeroSym    -> t
    []         | o == dhEgSym    -> t
    []         | o == dhOneSym    -> t
    _                               -> error $ "unexpected term form: `"++show t++"'"


var :: String -> Int -> LVar
var s i =  LVar s LSortE $ fromIntegral i

gTerm2Exp' ::  LNTerm -> String -> (LNTerm, [(LVar,LNTerm)])
gTerm2Exp' t p = (gTerm2Exp newterm, map swap mapping)
                  where muterms = getMuTerms t
                        mapping = (zip muterms $ map (var p ) [1 .. length muterms])
                        newterm = replaceMuTerms t (Map.fromList mapping)

allExponentsOf :: [LNTerm] -> LNTerm -> [LNTerm]
allExponentsOf tis target =
  S.toList $ S.union (S.unions $ map (S.fromList . eTermsOf) tis) (S.fromList $ eTermsOf target)
-- to get monomials that are also product of exponents, probably just need to modify the 
-- "eTermsOf" function to also take products of E-terms. 

allNBExponents :: [LNTerm] -> [LNTerm] -> ([LNTerm], [LNTerm])
allNBExponents nbasis allexp = (nbasis `intersect` allexp, allexp \\ nbasis)

-- polynomials, how should we represent them? maps? vectors?


coeffTermsOf :: ( LNTerm) -> (LNTerm) -> LNTerm
coeffTermsOf t@(LIT l) vart
  | t == vart = fAppdhOne
  | otherwise = t
coeffTermsOf t@(FAPP (DHMult o) ts) vart =     case ts of
    [ t1, t2 ] | o == dhPlusSym   -> error $ "term not in normal form?: `"++show t++"'"
    [ t1, t2 ] | o == dhTimesESym   -> simplifyraw $ fAppdhTimesE ( coeffTermsOf t1 vart, coeffTermsOf t2 vart)
    [ t1, t2 ] | o == dhTimesSym   -> simplifyraw $ fAppdhTimesE ( coeffTermsOf t1 vart, coeffTermsOf t2 vart)
    [t1]       | o == dhMuSym  -> t
    _                               -> error $ "term not in normal form?: `"++show t++"'"


setSimplify :: S.Set LNTerm -> S.Set LNTerm
setSimplify s =
  if S.size s == 1 then s
  else ( S.filter (\x -> x /= fAppdhOne ) s)


monomialsOf :: [LNTerm] -> LNTerm -> [S.Set LNTerm]
--eTermsOf t@(viewTerm3 -> Box dht) = eTermsOf dht
--eTermsOf t@(viewTerm3 -> BoxE dht) = eTermsOf dht
monomialsOf vars t@(LIT l)
  | isEVar t && elem t vars= [S.singleton t]
  | isNZEVar t && elem t vars= [S.singleton t]
  | isFrNZEVar t && elem t vars = [S.singleton t]
  | otherwise = [S.empty]
monomialsOf vars t =
  case viewTerm2 t of
    FdhTimesE t1 t2 -> [S.union (head $ monomialsOf vars t1) (head $ monomialsOf vars t2)]
    FdhTimesE t1 t2 -> [S.union (head $ monomialsOf vars t1) (head $ monomialsOf vars t2)]
    FdhPlus t1 t2 -> monomialsOf vars t1 ++ monomialsOf vars t2
    FdhMinus t1 -> monomialsOf vars t1
    FdhInv t1 | elem t vars -> [S.singleton t1]
    FdhInv t1 -> [S.empty]

-- THIS FUNCTION ASSUMES THAT THE INPUT TERMS ARE IN NORMAL FORM, i.e. 
-- EACH MONOMIAL (which we assume of type E) is of the form 
-- "(m1+m2+...+mk)" where mi = (e1*e2*...*el), and ei are either literals or inv(lit).

-- make sure the vars do not contain any inverse, but only pure LIT terms. 
getkeyfromProd :: [LNTerm] -> LNTerm -> S.Set LNTerm
getkeyfromProd vars t@(LIT l) = if (elem t vars) then (S.singleton t) else (S.singleton fAppdhOne)
getkeyfromProd vars t@(FAPP (DHMult o) ts) = case ts of
    [ t1, t2 ] | o == dhTimesSym   -> (case t1 of
        (LIT l) -> if (elem t1 vars) then setSimplify $ S.union (S.singleton t1) (getkeyfromProd vars t2) else getkeyfromProd vars t2
        _       -> setSimplify $ S.union (getkeyfromProd vars t1) (getkeyfromProd vars t2))
    [ t1, t2 ] | o == dhTimesESym   -> (case t1 of
        (LIT l) -> if (elem t1 vars) then setSimplify $ S.union (S.singleton t1) (getkeyfromProd vars t2) else getkeyfromProd vars t2
        _       -> setSimplify $ S.union (getkeyfromProd vars t1) (getkeyfromProd vars t2))
    [ t1 ]     | o == dhInvSym    -> if (elem t1 vars) then S.singleton t else S.singleton fAppdhOne
    [ t1 ]     | o == dhMinusSym    -> getkeyfromProd vars t1
    [ t1 ]     | o == dhMuSym    -> S.singleton fAppdhOne  -- if (elem t1 vars) then S.singleton $ fAppdhMu t1 else--TODO: not sure what to do here? t1 is actually a G term??
    []         | o == dhZeroSym    -> S.singleton fAppdhOne
    []         | o == dhOneSym    -> S.singleton fAppdhOne
    _                               -> error $ "this shouldn't have happened: `"++show t++"'"

getcoefromProd :: [LNTerm] -> LNTerm -> LNTerm
getcoefromProd vars t@(LIT l) = if (elem t vars) then fAppdhOne else t
getcoefromProd vars t@(FAPP (DHMult o) ts) = case ts of
    [ t1, t2 ] | o == dhTimesSym   -> (case t1 of
        (LIT l) -> if (elem t1 vars) then getcoefromProd vars t2 else simplifyraw $ fAppdhTimesE ( t1, getcoefromProd vars t2)
        _       -> simplifyraw $ fAppdhTimesE (getcoefromProd vars t1, getcoefromProd vars t2))
    [ t1, t2 ] | o == dhTimesESym   -> (case t1 of
        (LIT l) -> if (elem t1 vars) then getcoefromProd vars t2 else simplifyraw $ fAppdhTimesE (t1, getcoefromProd vars t2)
        _       -> simplifyraw $ fAppdhTimesE (getcoefromProd vars t1, getcoefromProd vars t2))
    [ t1 ]     | o == dhInvSym    -> if (elem t1 vars) then fAppdhOne else t -- check how to deal with inverse!
    [ t1 ]     | o == dhMinusSym    -> simplifyraw $ fAppdhMinus (getcoefromProd vars t1)
    [ t1 ]     | o == dhMuSym    -> fAppdhMu t1  --TODO: not sure what to do here? t1 is actually a G term??
    []         | o == dhZeroSym    -> t
    []         | o == dhOneSym    -> t
    _                               -> error $ "this shouldn't have happened, unexpected term form: `"++show t++"'"


combineMaps :: S.Set LNTerm -> LNTerm -> LNTerm -> LNTerm
combineMaps key oldvalue newvalue = simplifyraw $ fAppdhPlus (oldvalue,newvalue)

addToMap :: Map.Map (S.Set LNTerm) LNTerm -> [LNTerm] -> LNTerm  -> Map.Map (S.Set LNTerm) LNTerm
addToMap currmap vars t@(LIT l) = if (elem t vars) then (Map.insertWithKey combineMaps (S.singleton t) fAppdhOne currmap) else (Map.insertWithKey combineMaps (S.singleton fAppdhOne) t currmap)
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
    []         | o == dhOneSym    -> (Map.insertWithKey combineMaps (S.singleton fAppdhOne) fAppdhOne currmap)
    _                               -> error $ "this shouldn't have happened, unexpected term form: `"++show t++"'"


parseToMap ::  [LNTerm] -> LNTerm  -> Map.Map (S.Set LNTerm) LNTerm
parseToMap ts t = trace (show ("parsingPoly vars term,", ts, t)) (addToMap Map.empty ts t)

getvalue :: Map.Map (S.Set LNTerm) LNTerm -> (S.Set LNTerm) -> LNTerm
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
        createdmatrix = (map (\key -> ((map (\p -> getvalue p key) polynomials )++ [getvalue targetpoly key])) allkeys)
    in
  trace (show ("polynomials", polynomials, "targetpoly", targetpoly, "allkeys", allkeys, "thisistheresultingmatrix", createdmatrix, "vars", vars, "nb", nb)) createdmatrix -- todo: double check if row/column is ok or needs to be switched

solveIndicatorGauss :: [LNTerm] -> [LNTerm] -> LNTerm -> Maybe [LNTerm]
solveIndicatorGauss nb terms target = (\(a,b,c) -> a) $ solveMatrix fAppdhZero (createMatrix (nb) (map gTerm2Exp terms) (gTerm2Exp target)) []


-- PART FOR PROTOCOL ACTION INDICATORS

getVariablesOf :: [LNTerm] -> [LNTerm]
getVariablesOf tis =
  S.toList (S.unions $ map (S.fromList . varTermsOf) tis)


stripVars :: LNTerm -> LNTerm -> LNTerm -- (coeff of X, coeff of Y, constant factor)
stripVars var t@(LIT l) = if (t == var) then fAppdhOne else fAppdhZero
stripVars var t@(FAPP (DHMult o) ts) = case ts of
    [ t1, t2 ] | o == dhPlusSym   -> simplifyraw $ fAppdhPlus (stripVars var t1, stripVars var t2)
    [ t1, t2 ] | o == dhTimesESym   -> if (elem var (varTermsOf t)) then (coeffTermsOf t var) else fAppdhZero
    [ t1, t2 ] | o == dhTimesSym   -> if (elem var (varTermsOf t)) then (coeffTermsOf t var) else fAppdhZero
    [ t1 ]     | o == dhMinusSym   -> simplifyraw $ fAppdhMinus (stripVars var t1)
    [ t1 ]     | o == dhMuSym      -> if (elem var (varTermsOf t)) then error ("variables inside mu term" ++ show t) else fAppdhZero
    [  ]     | o == dhZeroSym      -> fAppdhZero
    [  ]     | o == dhOneSym      -> fAppdhZero
    _                               -> error $ "this shouldn't have happened, unexpected term form: `"++show t++"'"

constCoeff :: LNTerm -> LNTerm -- (coeff of X, coeff of Y, constant factor)
constCoeff t@(LIT l) = if (isvarGVar t || isvarEVar t) then fAppdhZero else t
constCoeff t@(FAPP (DHMult o) ts) = case ts of
    [ t1, t2 ] | o == dhPlusSym   -> simplifyraw $ fAppdhPlus (constCoeff t1, constCoeff t2)
    [ t1, t2 ] | o == dhTimesESym   -> if (null $ varTermsOf t ) then t else fAppdhZero
    [ t1, t2 ] | o == dhTimesSym   -> if (null $ varTermsOf t) then t else fAppdhZero
    [ t1 ]     | o == dhMinusSym   -> simplifyraw $ fAppdhMinus (constCoeff t1)
    [ t1 ]     | o == dhMuSym      -> if (null $ varTermsOf t) then t else fAppdhZero
    [  ]     | o == dhZeroSym      -> fAppdhZero
    [  ]     | o == dhOneSym      -> fAppdhOne
    _                               -> error $ "this shouldn't have happened, unexpected term form: `"++show t++"'"


splitVars :: [LNTerm] -> LNTerm -> LNTerm -> ([(LNTerm, LNTerm)], (LNTerm, LNTerm)) -- ([coeff of X, coeff of Y,..], constant factor)
splitVars vs term target = (map (\v -> (stripVars v term, stripVars v target)) vs, (constCoeff term, constCoeff target))
-- stripVars nbset t = stripVarsAux nbset t (fAppdhZero, [])

oneIfOne :: LNTerm -> LNTerm
oneIfOne fAppdhOne = fAppdhOne
oneIfOne _ = fAppdhZero

--this doesn't work if we 

createMatrixProto :: [LNTerm] -> LNTerm -> LNTerm -> ([LNTerm], Matrix LNTerm)
createMatrixProto nb term target =
    let (nbexp, vars) =   (allExponentsOf [term] target, []) --allNBExponents nb (allExponentsOf [term] target) --
        matrixvars = trace (show ("doestargethavevars",target)) $ getVariablesOf [term, target]
        (coeffVars, (constOfTerm, constTarget)) = splitVars matrixvars term target
        --(coeffVarsTarget, constTarget) = splitVars matrixvars target trace (show ("coeffVars",coeffVars,"**",const)) $ 
        polynomials = map (\(coeffX, coeffXTarget) -> parseToMap vars (simplifyraw $ fAppdhPlus (coeffX, simplifyraw $ fAppdhMinus coeffXTarget)) ) coeffVars -- this term now contains the introduced W and V variables. 
        targetvalue = trace (show (matrixvars, "thistermmm", polynomials, "thistermmm", constTarget, constOfTerm, (simplifyraw $ fAppdhPlus (constTarget, simplifyraw $ fAppdhMinus constOfTerm)))) $ parseToMap vars (simplifyraw $ fAppdhPlus (constTarget, simplifyraw $ fAppdhMinus constOfTerm))
        allkeys =  S.toList $ S.fromList $ concat ((Map.keys targetvalue):(map Map.keys polynomials))
        resultmatrix = map (\key -> ((map (\p -> getvalue p key) polynomials )++ [getvalue targetvalue key])) allkeys
        -- allkeys =  S.toList $ S.fromList $ concat ((Map.keys targetpoly):[Map.keys polynomial])
        -- row = map( \i -> getvalue targetpoly i) allkeys 
    in
  trace (show ("OBTAINEDMATRIX!!:", "**", matrixvars,"**", targetvalue,"**", resultmatrix,"**", allkeys, "Term,target:", term,"**",target)) (matrixvars, resultmatrix)
-- w1 is multiplied term, z1 is the summed term. 

oneSolution :: [LNTerm] -> ([LNTerm], [LNTerm], [LNTerm],[(LVar,LNTerm)]) -> [(LVar, LNTerm)]
oneSolution wzs a@(ts, newwzs, subszero, subextra) =  trace (show ("vars", wzs, "extrareplacewith", subextra, "zero", zerovars)) (if (all (isJust) wzvars && all isJust zerovars) then
                 ((zipWith zipfun wzvars ts) ++ subextra ++ map ((\i -> (i, getsubst i fAppdhZero)).fromJust) zerovars) else [])
                    where wzvars = map getVar newwzs
                          --pubg = LIT (Var ( LVar "pg" LSortPubG 1))
                          pubg = pubGTerm "g"
                          getsubst v t = case sortOfLit (Var v) of
                                        LSortVarG -> simplifyraw $ fAppdhExp (pubg, t)
                                        _ -> t
                          zipfun a b = (fromJust a, getsubst (fromJust a) b)
                          zerovars = map getVar subszero

extractMu :: LNTerm -> LNTerm
extractMu t@(FAPP (DHMult o) ts) = case ts of
   [ t1 ]     | o == dhMuSym      -> gTerm2Exp t1
   _ -> t

replace :: [LNTerm] -> (LNTerm, LNTerm, LNSubst, Bool) -> (LVar, LNTerm, LVar, LNTerm) -> (LNTerm, LNTerm, LNSubst, Bool)
{-replace basis (gt1, gt2, subst0, True) (var1, mu1, var2, mu2) 
  | (extractMu mu1) == (extractMu mu2) = (gt1, applyVTerm (substFromList [(var2, LIT (Var var1))]) gt2, subst0, True) -}
replace basis (gt1, gt2, subst0, True) (var1, mu1, var2, mu2) = case sol of
  Nothing -> (gt1,gt2,subst0, False)
  Just sols | null sols -> trace (show ("nullmatrix", gt1,gt2)) (gt1,applyVTerm (substFromList [(var2, LIT (Var var1))]) gt2,subst0, True)
            | otherwise -> (applyVTerm subst1 gt1, applyVTerm subst1 newgt2, newsubst, True)
                  where s = oneSolution wzs (head sols)
                        subst1 = substFromList s
                        newsubst = compose subst1 subst0
    where newgt2 = applyVTerm (substFromList [(var2, LIT (Var var1))]) gt2
          (wzs, matriz) = createMatrixProto [] (extractMu mu1) (extractMu mu2)
          sol = solveMatrix2 fAppdhZero basis matriz wzs
replace _ (gt1, gt2, subst0, False) _ = (gt1,gt2,subst0, False)

optionList :: [LNTerm] -> (LNTerm, [(LVar, LNTerm)]) -> (LNTerm, [ (LVar, LNTerm)]) ->  [ (LNTerm, LNTerm, LNSubst) ]
optionList basis (gt1,mut1) (gt2,mut2)
      | length mut1 == length mut2 = trace (show ("resultss", results)) $ map (\(a,b,c,d) -> (a,b,c)) results
      | otherwise = []
             where replacements = map (\pm -> zipWith (\(a,b) (c,d) -> (a,b,c,d)) mut1 pm) (permutations mut2)
                   foldmu permlist = foldl (replace basis) (gt1,gt2, substFromList (mut1++mut2) , True) permlist
                   results = filter (\(_,_,_,b) -> b) $ map foldmu replacements

solveIndicatorGaussProto :: MaudeHandle -> [LNTerm] -> LNTerm -> LNTerm -> [ Maybe [([(LVar, LNTerm)],[(LVar, LNTerm)]) ] ]
solveIndicatorGaussProto hnd basis term target =
    let (gt1, termsubst1) = gTerm2Exp' term "qwzk1"
        (gt2, termsubst2) = gTerm2Exp' target "qwzk2"
        options = optionList (fAppdhOne:basis') (gt1,termsubst1) (gt2,termsubst2)
        (wzs, matriz) = trace (show ("gter2msexp", gt1, gt2)) $ createMatrixProto (allExponentsOf [term] target) (gt1) (gt2)
      -- (wzs, matriz) = createMatrixProto (nb) (gTerm2Exp term) (gTerm2Exp target)       
      -- ([w1, z2], matriz) = createMatrixProto (nb) (gTerm2Exp term) (gTerm2Exp target)
        pubg =  pubGTerm "g"
        basis' = filter (\i-> i/= fAppdhOne) basis
        --sol = solveMatrix2 fAppdhZero (fAppdhOne:(basis'++map (\x->fAppdhMu (fAppdhExp (pubg, x))) basis')) matriz wzs
        sol = Just $ solveMatrix2 fAppdhZero (fAppdhOne:basis') matriz wzs
        getsol t1 t2 = case varTermsOf t1 of
            [] -> case varTermsOf t2 of
                  [] -> if sta1 == sta2 
                          then Nothing
                          else Just (Nothing)   
                              where 
                                normedpair = (runReader (norm' $ fAppPair (t1, t2)) hnd)
                                unpair t = case viewTerm t of
                                              (FApp (NoEq pairSym) [x, y]) ->(x,y)
                                              _ -> error $ "something went wrong" ++ show t
                                (sta1,sta2) =  unpair normedpair
                  _  -> Just $ solveMatrix2 fAppdhZero (fAppdhOne:basis') mat2 wz2
            _ -> Just $ solveMatrix2 fAppdhZero (fAppdhOne:basis') mat2 wz2
           where  
                  (wz2, mat2) = createMatrixProto [] (t1) (t2)
        retrieve s substss = case s of
          Nothing -> Just [(substss, [])]
          Just (Nothing) -> Nothing
          Just (Just sols) -> Just (map (\s-> (oneSolution wzs s, substss)) sols)
    in
    (retrieve sol (termsubst1++termsubst2)):(map ((\(s,t) -> retrieve s (substToList t)) . (\(t1,t2,sub) -> (getsol t1 t2, sub))) options )
 {-} case sol of 
    Nothing -> trace (show ("systemdoesnthavesolutions",wzs)) [Nothing]
    Just sols -> Just (map (\s-> (oneSolution wzs s, termsubst1++termsubst2)) sols)

let normedpair = (runReader (norm' $ fAppPair (apply subst ta1, apply subst ta2)) hndNormal)
            unpair t = case viewTerm t of
                        (FApp (NoEq pairSym) [x, y]) ->(x,y)
                        _ -> error $ "something went wrong" ++ show t
            (sta1,sta2) =  unpair normedpair
        case varTermsOf sta2 of
            [] -> case varTermsOf (sta1) of
                    [] -> do
                            if trace (show ("goodnorm",sta1,"And\n",sta2)) $ sta1 == sta2
                              then do
                                            void substSystem
                                            void normSystem
                              else contradictoryIf True
                    _  -> do
                            void substSystem
                            let bb = map (applyVTerm subst) $ S.toList nbset 
                                nb = filter (\i-> (isFrNZEVar i && (not $ i `elem` bb))) $ map (\v -> LIT (Var v)) $ varsRange subst                 
                            trace (show ("canwegethere", sta1,"And\n", sta2, "**", ta1,"**", ta2, "bset", bset, "nbset", nb)) $ void $ solveIndicatorProto nb sta1 sta2
                            void normSystem
            _  -> do
                    void substSystem
                    let bb = map (applyVTerm subst) $ S.toList nbset 
                        nb = filter (\i-> (isFrNZEVar i && (not $ i `elem` bb))) $ map (\v -> LIT (Var v)) $ varsRange subst                 
                    trace (show ("canwegethere2", sta1,"And\n", sta2, "**", ta1,"**", ta2, "bset", bset, "nbset", nb)) $ void $ solveIndicatorProto nb sta2 sta1
                    void normSystem
     else do



-}

{-
solveIndicatorGaussProto ::  LNTerm -> LNTerm -> Maybe ([(LVar, LNTerm)],[(LVar, LNTerm)],[(LVar, LNTerm)])
solveIndicatorGaussProto  term target = 
    let (gt1, termsubst1) = gTerm2Exp' term "qwzk1"
        (gt2, termsubst2) = gTerm2Exp' target "qwzk2"
        (wzs, matriz) = createMatrixProto (allExponentsOf [term] target) (gt1) (gt2)  
      -- (wzs, matriz) = createMatrixProto (nb) (gTerm2Exp term) (gTerm2Exp target)       
      -- ([w1, z2], matriz) = createMatrixProto (nb) (gTerm2Exp term) (gTerm2Exp target)
        (solution, newwzs, subszero) = solveMatrix fAppdhZero matriz wzs
    in
  case solution of 
    Nothing -> trace (show ("systemdoesnthavesolutions",newwzs,wzs,subszero)) Nothing
    Just (ts) -> trace (show ("vars", wzs, "extra", extravars,"new", newwzs, "zero", zerovars)) (if (all (isJust) wzvars && all isJust zerovars) then
                 Just (((zipWith zipfun wzvars ts) ++ map ((\i -> (i, getsubst i fAppdhZero)).fromJust) zerovars), termsubst1, termsubst2) else Nothing)
                    where wzvars = map getVar newwzs
                          --pubg = LIT (Var ( LVar "pg" LSortPubG 1))
                          pubg = pubGTerm "g"
                          getsubst v t = case sortOfLit (Var v) of
                                        LSortVarG -> trace (show ("exponentiating here", v, t)) $ simplifyraw $ fAppdhExp (pubg, t)
                                        _ -> t
                          zipfun a b = (fromJust a, getsubst (fromJust a) b)
                          extravars = (map getVar wzs) \\ wzvars
                          zerovars = map getVar subszero ++ extravars 
-}