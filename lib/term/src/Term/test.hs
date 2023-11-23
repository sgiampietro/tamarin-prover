module Main where

import Term.UnitTests
import Test.HUnit


main :: IO ()
main = do
    runTestTT testsClean2
    return ()