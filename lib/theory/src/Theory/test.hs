module Main where

import Theory.UnitTests
import Term.Maude.Process
import Term.Maude.Signature
import Test.HUnit


main :: IO ()
main = do
    hnd <- (startMaude "maude" dhMultMaudeSig)
    runTestTT $ testsRoot hnd
    return ()