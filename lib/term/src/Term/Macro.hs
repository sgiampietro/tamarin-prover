{-# LANGUAGE ViewPatterns #-} 
-- |
-- Copyright   : (c) 2023 - Thiebaux Valentin
-- License     : GPL v3 (see LICENSE)
--
-- Macro substitution and application

module Term.Macro (
    Macro
    , applyMacros
) where

import           Term.Substitution
import          Debug.Trace
import qualified Data.ByteString            as B

type Macro = (B.ByteString, [LVar], Term (Lit Name LVar))


dhMultBuiltins :: [B.ByteString]
dhMultBuiltins =  [
  dhMultSymString -- g1.g2
  , dhGinvSymString -- g^-1
  , dhZeroSymString
  , dhMinusSymString
  , dhInvSymString
  , dhEgSymString 
  , dhTimesSymString
  , dhTimesESymString -- e1*e2 for E (not necessarily NZE) elements
  , dhPlusSymString -- e1+e2
  , dhExpSymString
  , dhOneSymString
  , dhMuSymString
  -- , dhBoxSymString
  -- , dhBoxESymString  
  ] 


-- | Change a Macro to a FunSym
macroToFunSym :: Macro -> FunSym
macroToFunSym (op, args, _) = if op  `elem`  dhMultBuiltins then DHMult (op, (length args, Private, Destructor))  
    else trace (show ("ISTHISTHEPROBLEM?", op)) NoEq (op, (length args, Private, Destructor))      

-- | Apply and substitute the macro on a LNTerm
applyMacro :: FunSym -> [LVar] -> LNTerm -> LNTerm -> LNTerm
applyMacro mc margs mout (viewTerm -> FApp f targs)
    | mc == f = apply (substFromList $ zip margs (map (applyMacro mc margs mout) targs)) mout
    | otherwise = fApp f $ map (applyMacro mc margs mout) targs
applyMacro _ _ _ t = t

switchApplyMacro :: LNTerm -> Macro -> LNTerm
switchApplyMacro t (op, args, out) = applyMacro (macroToFunSym (op, args, out)) args out t 

-- | Apply and substitute all the macros on a LNTerm
applyMacros :: [Macro] -> LNTerm -> LNTerm
applyMacros [] t     = t
applyMacros [m] t    = switchApplyMacro t m
applyMacros (m:ms) t = switchApplyMacro (applyMacros ms t) m