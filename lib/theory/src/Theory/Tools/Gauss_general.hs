{-# LANGUAGE DeriveGeneric #-}
-- | Matrix datatype and operations.
--
--   Every provided example has been tested.
--   Run @cabal test@ for further tests.
module Theory.Tools.Gauss (
    -- * Matrix type
    Matrix, 
    Solution(..),
    gaussSolveMatrix
  ) where


import qualified Data.Map     as Map  
import qualified Data.Set     as S

type Row a = [a]

type Matrix a = [ Row a ]

data Solution a = Simple (Matrix a) | Infinite (Matrix a) | Inconsistent

-- 1. Sort rows by count of leading zeros
-- 2. Make zero in each row at its index position and add it to others making zero in that position from top to bottom
-- 3. Do the same from bottom to the top

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

gaussMakeZero :: (Eq a, Num a, Fractional a) =>  a -> Row a -> Row a -> Row a
gaussMakeZero zero r1 r2 = map (\(r1_elt, r2_elt) -> (r1_elt * factor) + r2_elt) (zip r1 r2)
  where
    index = leadingZeros zero r1
    r1_head = r1 !! index
    r2_head = r2 !! index
    factor = (negate r2_head) / r1_head

-- apply the "zeroing head" operation to all the rows except the first one.
-- do this recursively for every row
gaussReduce :: (Eq a, Num a, Fractional a) =>  a -> Matrix a -> Matrix a
gaussReduce zero [] = []
gaussReduce zero (r1 : rs) = r1 : gaussReduce zero (map (gaussMakeZero zero r1) rs)

gaussFixCoefficients :: (Eq a, Num a, Fractional a) =>  a -> Matrix a -> Matrix a
gaussFixCoefficients zero [] = []
gaussFixCoefficients zero (r : rs) = map (/ factor) r : gaussFixCoefficients zero rs
  where
    index = leadingZeros zero r
    factor = r !! index


--gaussExtractResults :: Matrix -> [String] -> String
--gaussExtractResults rows var_names = foldl (\acc row -> showVariableValues row var_names ++ "\n" ++ acc) "" rows

gaussRawSolveMatrix :: (Eq a, Num a, Fractional a) =>  a -> Matrix a -> Matrix a
gaussRawSolveMatrix zero mat = mat3
  where
    mat1 = gaussReduce zero mat
    mat2 = gaussReduce zero $ reverse mat1
    mat3 = gaussFixCoefficients zero $ reverse mat2

gaussSolveMatrix :: (Eq a, Num a, Fractional a) =>  a -> Matrix a -> Solution a
gaussSolveMatrix zero mat
  | infiniteSolutions zero mat1 = Infinite res1'
  | infiniteSolutions zero mat2 = Infinite res2'
  | inconsistentMatrix zero mat3 = Inconsistent
  | otherwise = Simple mat3
  where
    mat1 = gaussReduce zero mat
    mat2 = gaussReduce zero $ reverse mat1
    mat3 = gaussFixCoefficients zero $ reverse mat2
    mat1' = filter (not . all (== zero)) mat1
    mat2' = filter (not . all (== zero)) mat2
    res1' = gaussRawSolveMatrix zero mat1'
    res2' = gaussRawSolveMatrix zero mat2'