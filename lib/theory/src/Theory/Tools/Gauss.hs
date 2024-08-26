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
    removeZeroRows
  ) where


import qualified Data.Map     as Map  
import qualified Data.Set     as S

import GHC.Real
import Term.Maude.Process
import Control.Monad.Trans.Reader   
import Term.Rewriting.Norm

import Term.LTerm -- (LNTerm)
import Term.Term.Raw

import Debug.Trace

int2LNTerm :: Integer -> LNTerm
int2LNTerm 0 = fAppdhZero
int2LNTerm 1 = fAppdhOne
int2LNTerm n = fAppdhPlus (fAppdhOne, int2LNTerm $ n-1)

rationalLNTerm :: Integer -> Integer -> LNTerm
rationalLNTerm n 0 = error "division by zero"
rationalLNTerm n d = fAppdhMult (fromInteger n, fAppdhInv $ fromInteger d)

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
    _         -> t)
  FdhMinus t1 -> (case viewTerm2 t1 of
    FdhMinus t2 -> simplifyraw t2
    DHZero -> fAppdhZero
    _      -> t
    )
  _ -> t
  --_ -> error $ "wrong format: `"++show t++"'"




-- Gauss Elimination: Solve matrix equation Ax = B
gaussEliminationFromEquation :: LNTerm -> Matrix LNTerm -> Matrix LNTerm -> Vector LNTerm
gaussEliminationFromEquation zero a b = gaussEliminationFromMatrix zero $ zipMatrix a b

-- Create augmented matrix from A and B
zipMatrix :: Matrix LNTerm -> Matrix LNTerm -> Matrix LNTerm
zipMatrix [] [] = []
zipMatrix (x:xs) (y:ys) = (x ++ y) : (zipMatrix xs ys)

-- Compute the row-reduced-echelon form of the matrix
gaussReduction :: LNTerm -> Matrix LNTerm -> Matrix LNTerm
gaussReduction zero [] = []
gaussReduction zero matrix = r: gaussReduction zero rs
    where
        (r:rows) = pivotCheck zero (allzerosCheck zero matrix) (length matrix)
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
pivotCheck :: LNTerm -> Matrix LNTerm -> Int -> Matrix LNTerm
pivotCheck zero (r:rs) counter
    | rs == [] = (r:rs)
    | counter == 0 = (r:rs)
    | (head r /= zero) = (r:rs)
    | otherwise = pivotCheck zero (rs ++ [r]) (counter-1)


removeZeroRows :: LNTerm -> Matrix LNTerm -> Matrix LNTerm
removeZeroRows zero = filter (\row -> not (all (== zero) row))

-- check if matrix is inconsistent - it will have all zeroes except last column in at least one row
inconsistentMatrix :: LNTerm -> Matrix LNTerm -> Bool
inconsistentMatrix zero = any (\row -> all (== zero) (drop 1 (reverse row)))


{- Reverse the rows and columns to make the calculation easier and undo
-- the column reversion before returning the solutions
-}
traceBack :: LNTerm -> Matrix LNTerm -> Vector LNTerm
traceBack zero = reverse . (traceBack' zero 2) . reverse . map reverse



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


-- Gauss Elimination: Solve a given augmented matrix
gaussEliminationFromMatrix :: LNTerm -> Matrix LNTerm -> Vector LNTerm
gaussEliminationFromMatrix zero matrix = traceBack zero $ gaussReduction zero matrix


solveMatrix :: LNTerm -> Matrix LNTerm -> Maybe (Vector LNTerm)
solveMatrix zero matrix  
  | inconsistentMatrix zero cleanmatrix = Nothing
  | otherwise = Just (traceBack zero cleanmatrix)
    where 
      redmatrix = trace (show ("IGetTillHere", gaussReduction zero matrix)) $ gaussReduction zero matrix
      cleanmatrix =  trace (show ("IGetTillHere2", removeZeroRows zero redmatrix)) $ removeZeroRows zero redmatrix
      

{-
quicksort :: [a] -> (a -> a -> Int) -> [a]
quicksort [] _ = []
quicksort (x : xs) cmp = (quicksort lesser cmp) ++ [x] ++ (quicksort greater cmp)
  where
    lesser = [i | i <- xs, (cmp x i) < 0]
    greater = [i | i <- xs, (cmp x i) >= 0]

leadingZeros :: (Eq a, Num a, Fractional a) => a -> Row a -> Int
leadingZeros zero = length . takeWhile (== zero)

-- check if matrix is inconsistent - it will have all zeroes except last column in at least one row
inconsistentMatrix :: (Eq a, Num a, Fractional a) => a -> [[a]] -> Bool
inconsistentMatrix zero = any $ all (== zero) . reverse . drop 1

infiniteSolutions :: (Eq a, Num a, Fractional a) => a -> [[a]] -> Bool
infiniteSolutions zero = any $ all (== zero)

gaussCompareRows :: (Eq a, Num a, Fractional a) => a -> Row a -> Row a -> Int
gaussCompareRows zero r1 r2 = leadingZeros zero r2 - leadingZeros zero r1

gaussSortMatrix :: (Eq a, Num a, Fractional a) => a -> Matrix a -> Matrix a
gaussSortMatrix zero = flip quicksort (gaussCompareRows zero)

gaussMakeZero :: MaudeHandle -> LNTerm -> Row LNTerm -> Row LNTerm -> Row LNTerm
gaussMakeZero hnd zero r1 r2 = map (\(r1_elt, r2_elt) -> simplifyraw $ (simplifyraw (r1_elt * factor)) + r2_elt) (zip r1 r2)
  where
    index = leadingZeros zero r1
    r1_head = r1 !! index
    r2_head = r2 !! index
    factor = simplify hnd $ (simplifyraw $ negate r2_head) / r1_head

-- apply the "zeroing head" operation to all the rows except the first one.
-- do this recursively for every row
gaussReduce :: MaudeHandle -> LNTerm -> Matrix LNTerm -> Matrix LNTerm
gaussReduce hnd zero [] = []
gaussReduce hnd zero (r1 : rs) = r1 : gaussReduce hnd zero (map (gaussMakeZero hnd zero r1) rs)

gaussFixCoefficients :: MaudeHandle -> LNTerm -> Matrix LNTerm -> Matrix LNTerm
gaussFixCoefficients hnd zero [] = []
gaussFixCoefficients hnd zero (r : rs) = map (\x -> simplify hnd (x / factor)) r : gaussFixCoefficients hnd zero rs
  where
    index = leadingZeros zero r
    factor = r !! index


--gaussExtractResults :: Matrix -> [String] -> String
--gaussExtractResults rows var_names = foldl (\acc row -> showVariableValues row var_names ++ "\n" ++ acc) "" rows

gaussRawSolveMatrix :: MaudeHandle -> LNTerm -> Matrix LNTerm -> Matrix LNTerm
gaussRawSolveMatrix hnd zero mat = mat3
  where
    mat1 = gaussReduce hnd zero mat
    mat2 = gaussReduce hnd zero $ reverse mat1
    mat3 = gaussFixCoefficients hnd zero $ reverse mat2

gaussSolveMatrix :: MaudeHandle -> LNTerm -> Matrix LNTerm -> Solution LNTerm
gaussSolveMatrix hnd zero mat
  | infiniteSolutions zero mat1 = Infinite res1'
  | infiniteSolutions zero mat2 = Infinite res2'
  | inconsistentMatrix zero mat3 = Inconsistent
  | otherwise = Simple mat3
  where
    mat1 = gaussReduce hnd zero mat
    mat2 = gaussReduce hnd zero $ reverse mat1
    mat3 = gaussFixCoefficients hnd zero $ reverse mat2
    mat1' = filter (not . all (== zero)) mat1
    mat2' = filter (not . all (== zero)) mat2
    res1' = gaussRawSolveMatrix hnd zero mat1'
    res2' = gaussRawSolveMatrix hnd zero mat2'


computeVariableValues :: LNTerm -> Row -> LNTerm
computeVariableValues zero r 
  | not (null other_coefficients) = var_str ++ other_vars_str
  | otherwise = var_str
  where
    index = leadingZeros r
    coefficient = r !! index
    value = last r
    raw_row = reverse . drop 1 . reverse $ r -- row coefficients, except the free member
    elements_count = length raw_row
    other_coefficients = filter (\(k, k_idx) -> k /= zero && k_idx /= index) (zip raw_row [0 .. elements_count])
    --subtract_coefficient k = if k < 0 then " + " ++ show (- k) else " - " ++ show k
    other_vars_str = concatMap (\(k, k_idx) -> subtract_coefficient k ++ " * " ++ (var_names !! k_idx)) other_coefficients
    var_str = (var_names !! index) ++ " = " simplifyraw (value / coefficient)

gaussExtractResults :: Matrix -> [String] -> String
gaussExtractResults rows var_names = foldl (\acc row -> showVariableValues row var_names ++ "\n" ++ acc) "" rows
-}