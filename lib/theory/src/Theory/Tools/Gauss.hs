{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
-- | Matrix datatype and operations.
--
--   Every provided example has been tested.
--   Run @cabal test@ for further tests.
module Theory.Tools.Gauss (
    -- * Matrix type
    Matrix, 
    Solution(..),
    simplify,
    simplifyraw,
    gaussEliminationFromMatrix,
    gaussReduction,
    solveMatrix,
    solveMatrix2,
    removeZeroRows
  ) where


import qualified Data.Map     as Map  
--import qualified Data.Set     as S

import GHC.Real
import Term.LTerm -- (LNTerm)
import Debug.Trace -- .Ignore
--import Term.Builtin.Convenience (x0)

import Data.List (subsequences, (\\))
import Data.Maybe (fromJust)

int2LNTerm :: Integer -> LNTerm
int2LNTerm 0 = fAppdhZero
int2LNTerm 1 = fAppdhOne
int2LNTerm n = fAppdhPlus (fAppdhOne, int2LNTerm $ n-1)

rationalLNTerm :: Integer -> Integer -> LNTerm
rationalLNTerm n 0 = error "division by zero"
rationalLNTerm n d = fAppdhTimesE (fromInteger n, fAppdhInv $ fromInteger d)

instance Num (Term (Lit Name LVar)) where
  t1 + t2 = simplifyraw $ fAppdhPlus (t1,t2)
  t1 - t2 = simplifyraw $ fAppdhPlus (t1, simplifyraw $ fAppdhMinus t2)
  t1 * t2 = simplifyraw $ fAppdhTimesE (t1,t2)
  negate = fAppdhMinus
  abs t = t
  signum t = fAppdhOne
  fromInteger = int2LNTerm

instance Fractional (Term (Lit Name LVar)) where
  t1 / t2 = simplifyraw $ fAppdhTimesE (t1, simplifyraw $ fAppdhInv t2)
  recip t = simplifyraw $ fAppdhInv t
  fromRational (n:%d) = rationalLNTerm n d


type Vector a = [a]
type Row a = [a]
type Matrix a = [ Row a ]

data Solution a = Simple (Matrix a) | Infinite (Matrix a) | Inconsistent

-- 1. Sort rows by count of leading zeros
-- 2. Make zero in each row at its index position and add it to others making zero in that position from top to bottom
-- 3. Do the same from bottom to the top

simplify :: LNTerm  -> LNTerm
simplify mterm = simplifyraw mterm --runReader (norm' mterm) hnd

simplifyraw :: LNTerm -> LNTerm
simplifyraw t= case viewTerm2 t of 
  Lit2 l -> t
  FdhTimes t1 t2 -> (case (viewTerm2 t1, viewTerm2 t2) of
    (DHOne, DHOne)  -> fAppdhOne
    (DHOne, _ )     -> simplifyraw t2
    (_    , DHOne)  -> simplifyraw t1
    (DHZero, _ )    -> fAppdhZero
    (_    , DHZero) -> fAppdhZero
    (FdhInv t3, _) ->  if (t2 == t3) then fAppdhOne else t
    (_, FdhInv t3) ->  if (t1 == t3) then fAppdhOne else t
    (_    , _ )     -> t )
  FdhTimesE t1 t2 -> (case (viewTerm2 t1, viewTerm2 t2) of
    (DHOne, DHOne) -> fAppdhOne
    (DHOne, _ )    -> simplifyraw t2
    (_    , DHOne) -> simplifyraw t1
    (DHZero, _ )    -> fAppdhZero
    (_    , DHZero) -> fAppdhZero
    (FdhInv t3, _) ->  if (t2 == t3) then fAppdhOne else t
    (_, FdhInv t3) ->  if (t1 == t3) then fAppdhOne else t
    (_    , _ )    -> t )
  FdhPlus t1 t2 -> (case (viewTerm2 t1, viewTerm2 t2) of
    (DHZero, DHZero) -> fAppdhZero
    (DHZero, _ )    -> simplifyraw t2
    (_    , DHZero) -> simplifyraw t1
    (FdhMinus t3, _) ->  if (t2 == t3) then fAppdhZero else t
    (_, FdhMinus t3) ->  if (t1 == t3) then fAppdhZero else t
    (_    , _ )    -> t )
  FdhInv t1 -> (case (viewTerm2 t1) of
    FdhInv t2 -> simplifyraw t2
    DHOne     -> fAppdhOne
    FdhMinus t2 -> fAppdhMinus $ simplifyraw $ fAppdhInv t2
    _         -> t)
  FdhMinus t1 -> (case viewTerm2 t1 of
    FdhMinus t2 -> simplifyraw t2
    DHZero -> fAppdhZero
    FdhPlus t2 t3 -> fAppdhPlus (simplifyraw (fAppdhMinus t2), simplifyraw (fAppdhMinus t3))
    _      -> t
    )
  _ -> t
  --_ -> error $ "wrong format: `"++show t++"'"



-- Gauss Elimination: Solve matrix equation Ax = B
-- gaussEliminationFromEquation :: LNTerm -> Matrix LNTerm -> Matrix LNTerm -> Vector LNTerm
-- gaussEliminationFromEquation zero a b = gaussEliminationFromMatrix zero $ zipMatrix a b

-- Create augmented matrix from A and B
zipMatrix :: Matrix LNTerm -> Matrix LNTerm -> Matrix LNTerm
zipMatrix [] [] = []
zipMatrix (x:xs) (y:ys) = (x ++ y) : (zipMatrix xs ys)

-- Compute the row-reduced-echelon form of the matrix
gaussReduction :: LNTerm -> Matrix LNTerm -> [LNTerm] -> (Matrix LNTerm, [LNTerm])
gaussReduction zero [] vars = ([], vars)
gaussReduction zero matrix vars | null $ head (allzerosCheck zero matrix) = (matrix, vars)
gaussReduction zero matrix vars | null vars = gaussReduction zero matrix (replicate (length matrix) zero)
gaussReduction zero matrix vars =  (r: ( fst nextstep ), snd nextstep)
    where
        nextstep = gaussReduction zero rs varsP
        ((r:rows), varsP) = pivotCheck zero (allzerosCheck zero matrix) (length matrix) vars
        rs = map reduceRow $ rows
        -- Row reduction using row operations
        reduceRow row
            | (head row) == zero = drop 1 row
            | otherwise = drop 1 $ zipWith (\ a b -> simplifyraw $ b + (simplifyraw $ negate a) ) (map (\y -> simplifyraw $ y*frac) row) r
            where
                frac = simplifyraw $ (head r)/(head row)

-- Check and swap row if pivot element is zero
allzerosCheck :: LNTerm -> Matrix LNTerm -> Matrix LNTerm
allzerosCheck zero m 
  | null m = m
  | null (head m) = m
  | all (\r -> (head r) == zero) m = allzerosCheck zero (map (drop 1) m)
  | otherwise = m

-- Check and swap row if pivot element is zero
pivotCheck :: LNTerm -> Matrix LNTerm -> Int -> [LNTerm] -> (Matrix LNTerm, [LNTerm])
pivotCheck zero (r:rs) counter vars@(v:vs)
    | rs == [] = ((r:rs), vars)
    | counter == 0 = ((r:rs), vars)
    | (head r /= zero) = ((r:rs), vars)
    | otherwise = trace (show "swappedrow!!!!") (fst $ pivotCheck zero (rs ++ [r]) (counter-1) (vs ++ [v]), vs ++ [v])


removeZeroRows :: LNTerm -> Matrix LNTerm -> [LNTerm] -> (Matrix LNTerm, [LNTerm], [LNTerm])
removeZeroRows zero matrix vars = (map fst filtered, map snd filtered, subst)
      where 
        subst = map snd $ filter (\(row, v) -> (all (== zero) row) ) $ zip matrix vars 
        filtered = filter (\(row, v) -> not (all (== zero) row) ) $ zip matrix vars 


-- check if matrix is inconsistent - it will have all zeroes except last column in at least one row
inconsistentMatrix :: LNTerm -> Matrix LNTerm -> Bool
inconsistentMatrix zero = any (\row -> all (== zero) (drop 1 (reverse row)))


{- Reverse the rows and columns to make the calculation easier and undo
-- the column reversion before returning the solutions
-}


{-
-- Use back substitution to calculate the solutions
traceBack' :: LNTerm -> Int -> Matrix LNTerm -> Vector LNTerm
traceBack' zero _ [] = []
traceBack' zero prevlength (r:rows) = (pad ++ (var : (traceBack' zero currlength rs)))
    where
        var = simplifyraw $ (head r)/(last r)
        rs = map substituteVariable rows
        substituteVariable (x:(y:ys)) = ((simplifyraw $ x +(simplifyraw $ negate (simplifyraw $ var*y) ) ):ys)
        currlength = (length r)
        pad = if (currlength - prevlength > 0) then (replicate (currlength - prevlength) zero) else []
-}

traceBack :: LNTerm -> Matrix LNTerm -> Vector LNTerm
traceBack zero = reverse . (traceBack' zero 2) . reverse . map reverse


-- Use back substitution to calculate the solutions
traceBack' :: LNTerm -> Int -> Matrix LNTerm -> Vector LNTerm
traceBack' zero _ [] = []
traceBack' zero prevlength (r:rows) =  (var : (traceBack' zero currlength rs))
    where
        var = simplifyraw $ (head r)/(last r)
        rs = map substituteVariable rows
        substituteVariable (x:(y:ys)) = ((simplifyraw $ x +(simplifyraw $ negate (simplifyraw $ var*y) ) ):ys)
        currlength = (length r)
        -- pad = if (currlength - prevlength > 0) then (replicate (currlength - prevlength) zero) else []

myButLast (x : _ : []) = x  -- base case
myButLast (_ : xs)     = myButLast xs


innerProduct :: LNTerm -> Vector LNTerm -> Vector LNTerm -> LNTerm
innerProduct zero [] [] = zero
innerProduct zero [y] [x] = (simplifyraw $ y*x)
innerProduct zero (y:ys) (x:xs) = simplifyraw $ (simplifyraw $ y*x)+(innerProduct zero ys xs)
innerProduct zero t s = error ("unexpected format" ++ show t ++ "and" ++ show s)

-- Use back substitution to calculate the solutions
traceBack2' :: LNTerm -> Int -> Matrix LNTerm -> Vector LNTerm -> Vector LNTerm
traceBack2' zero n [] extravars = []
traceBack2' zero n (r:rows) extravars =  (var : (traceBack2' zero n rs extravars))
    where
        var2 = simplifyraw $ negate (innerProduct zero extravars ((take n (drop 1 r))))
        var = simplifyraw $ (simplifyraw $ (head r) + var2)/(last r)
        rs = map substituteVariable rows
        substituteVariable (x:(ys)) = ((simplifyraw $ x +(simplifyraw $ negate (simplifyraw $ var*(myButLast ys)) ) ):ys)
        -- pad = if (currlength - prevlength > 0) then (replicate (currlength - prevlength) zero) else []

traceBack2 :: LNTerm -> Matrix LNTerm -> [LVar] -> Vector LNTerm -> Vector LNTerm
traceBack2 zero matrix vv vars =  if m>0  then reverse (traceBack2' zero m matrix' extravars) else reverse (traceBack2' zero 0 matrix' [])
          where matrix' = reverse (map reverse matrix)
                extravars = reverse vars
                m = length extravars



-- Gauss Elimination: Solve a given augmented matrix
gaussEliminationFromMatrix :: LNTerm -> Matrix LNTerm -> [LNTerm] -> Vector LNTerm
gaussEliminationFromMatrix zero matrix vars = traceBack zero $ fst $ gaussReduction zero matrix vars




createListBasis :: LNTerm ->  [LNTerm] -> [LNTerm]
--createListBasis zero basis = []
createListBasis zero basis = map (foldl (\a b -> simplifyraw $ fAppdhPlus(a,b)) zero) $ subsequences basis

combineNlists :: Int -> [LNTerm] -> [[LNTerm]]
combineNlists 0 _ = []
combineNlists 1 xs = [xs]
combineNlists 2 xs = [x:[y] | x<-xs , y<- xs]
combineNlists n xs = [ x:zs  | x<- xs, zs<-(combineNlists (n-1) xs)]

{-
mergeWithOne :: [LVar] -> [LNTerm] -> [(LVar, LNTerm)]
mergeWithOne [] options = []
mergeWithOne (v:vs) (o:ops) = (v,o):(mergeWithOne vs ops)
-}
-- should return a Maybe [(Vector LNTerm, [LNTerm], [LNTerm])] (list of nulspace basis vectors)
solveMatrix2 :: LNTerm -> [LNTerm] -> Matrix LNTerm -> [LNTerm] -> (Maybe [(Vector LNTerm, [LNTerm], [LNTerm], [(LVar,LNTerm)])])
solveMatrix2 zero basis matrix variables 
  | inconsistentMatrix zero cleanmatrix = Nothing
  | null cleanmatrix = Nothing
  | otherwise = trace (show ("EXTRAVARS", ncol, nrows,ncol - nrows, extravars)) $ 
  Just (map (\evars -> (traceBack2 zero cleanmatrix (map fst evars) (map snd evars) , variablesP, subszero, evars)) options)  --Just (traceBack zero cleanmatrix) 
    where 
      (redmatrix, variables2) = gaussReduction zero matrix variables
      (cleanmatrix, variablesP, subszero) =  removeZeroRows zero redmatrix variables2
      ncol = length (head cleanmatrix) - 1
      nrows = length cleanmatrix
      n = ncol - nrows
      zerovars = map getVar subszero
      extravars = map fromJust $ ((map getVar variables) \\ (map getVar variablesP))\\zerovars
      -- extravars' = filter (\i-> lvarName i /= "yk") extravars
      m = trace (show "waiting") length extravars --'
      extravarssubst = filter (\z-> not $ all (fAppdhZero == ) z) $ combineNlists m [fAppdhOne, fAppdhZero] -- trace (show ("m", m,"combineN", basis)) (createListBasis zero basis )
      options = trace (show ("extravarsubst", extravarssubst, extravarssubst)) $ map (\ops -> zip extravars ops) extravarssubst -- (combineNlists m extravarssubst)



-- should return a Maybe [(Vector LNTerm, [LNTerm], [LNTerm])] (list of nulspace basis vectors)
solveMatrix :: LNTerm -> Matrix LNTerm -> [LNTerm] -> (Maybe (Vector LNTerm), [LNTerm], [LNTerm])
solveMatrix zero matrix variables 
  | inconsistentMatrix zero cleanmatrix = trace (show ("inconsistent", cleanmatrix)) (Nothing, variables, [])
  | otherwise = trace (show ("consistent", cleanmatrix)) (Just (traceBack zero cleanmatrix) , variablesP, subst) --Just (traceBack zero cleanmatrix) 
    where 
      (redmatrix, variables2) = gaussReduction zero matrix variables
      (cleanmatrix, variablesP, subst) = removeZeroRows zero redmatrix variables2
      
