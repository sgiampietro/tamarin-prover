{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
  -- for ByteString
-- |
-- Copyright   : (c) 2010-2012 Benedikt Schmidt & Simon Meier
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Benedikt Schmidt <beschmi@gmail.com>
--
-- Term Algebra and related notions.
module Term.Term (

    -- ** Pretty printing and query functions.
      prettyTerm
    , showFunSymName
    , lits

    -- ** Smart constructors
    , fAppOne
    , fAppZero
    , fAppDHNeutral
    , fAppDiff
    , fAppExp
    , fAppInv
    , fAppPMult
    , fAppEMap
    , fAppUnion
    , fAppPair
    , fAppFst
    , fAppSnd
    , fAppNatOne

    -- ** Smart constructors for DH
    , fAppdhMult -- g1.g2
    , fAppdhGinv -- g^-1
    , fAppdhZero
    , fAppdhMinus
    , fAppdhInv
    , fAppdhEg
    , fAppdhTimes
    , fAppdhTimes2 -- e1*e2 for E (not necessarily NZE) elements
    , fAppdhPlus -- e1+e2
    , fAppdhExp
    , fAppdhOne 
    , fAppdhMu
    , fAppdhBox
    , fAppdhBoxE 

    -- ** Destructors and classifiers
    , isPair
    , isDiff
    , isInverse
    , isProduct
    , isXor
    , isUnion
    , isEMap
    , isNullaryPublicFunction
    , isPrivateFunction
    , isAC
    , getLeftTerm
    , getRightTerm

    -- ** "Protected" subterms
    , allProtSubterms
    , elemNotBelowReducible

    -- * AC, C, and NonAC funcion symbols
    , FunSym(..)
    , ACSym(..)
    , CSym(..)
    , Privacy(..)
    , Constructability(..)
    , NoEqSym

    -- ** Signatures
    , FunSig
    , NoEqFunSig

    -- ** concrete symbols strings
    , diffSymString
    , munSymString 
    , expSymString
    , invSymString
    , pmultSymString
    , emapSymString
    , unionSymString
    , natPlusSymString
    , natOneSymString
    , oneSymString
    , dhNeutralSymString
    , multSymString
    , zeroSymString
    , xorSymString

    , dhMultSymString -- g1.g2
    , dhGinvSymString -- g^-1
    , dhZeroSymString
    , dhMinusSymString
    , dhInvSymString
    , dhEgSymString 
    , dhTimesSymString
    , dhTimes2SymString -- e1*e2 for E (not necessarily NZE) elements
    , dhPlusSymString -- e1+e2
    , dhExpSymString
    , dhOneSymString
    , dhMuSymString
    , dhBoxSymString
    , dhBoxESymString

    -- ** Function symbols
    , diffSym
    , expSym
    , pmultSym
    , natOneSym
    , oneSym
    , zeroSym
    , dhNeutralSym
     -- SOFIA: extra DH mult symbols that aren't already there: 
    , dhMultSym -- g1.g2
    , dhGinvSym -- g^-1
    , dhZeroSym
    , dhMinusSym
    , dhInvSym
    , dhEgSym
    , dhTimesSym
    , dhTimes2Sym -- e1*e2 for E (not necessarily NZE) elements
    , dhPlusSym -- e1+e2
    , dhExpSym
    , dhOneSym  
    , dhMuSym
    , dhBoxSym
    , dhBoxESym

    -- ** concrete signatures
    , dhFunSig
    , bpFunSig
    , msetFunSig
    , natFunSig
    , xorFunSig
    , pairFunSig
    , pairFunDestSig    
    , dhReducibleFunSig
    , bpReducibleFunSig
    , xorReducibleFunSig
    , implicitFunSig
    , dhMultFunSig

    , prodTerms

    , module Term.Term.Classes
    , module Term.Term.Raw
    ) where

-- import           Data.Monoid
-- import           Data.Foldable (foldMap)

import qualified Data.Set as S
import qualified Data.ByteString.Char8 as BC
import           Extension.Data.ByteString ()

import           Text.PrettyPrint.Class

import           Term.Term.Classes
import           Term.Term.FunctionSymbols
import           Term.Term.Raw

----------------------------------------------------------------------
-- Smart Constructors
----------------------------------------------------------------------

-- | Smart constructors for one, zero.
fAppOne :: Term a
fAppOne = fAppNoEq oneSym []

fAppDHNeutral :: Term a
fAppDHNeutral = fAppNoEq dhNeutralSym []

fAppZero :: Term a
fAppZero = fAppNoEq zeroSym []

-- | Smart constructors for one on naturals.
fAppNatOne :: Term a
fAppNatOne  = fAppNoEq natOneSym []

-- | Smart constructors for diff, pair, exp, pmult, and emap.
fAppDiff, fAppPair, fAppExp, fAppPMult :: (Term a, Term a) -> Term a
fAppDiff (x,y)  = fAppNoEq diffSym  [x, y]
fAppPair (x,y)  = fAppNoEq pairSym  [x, y]
fAppExp  (b,e)  = fAppNoEq expSym   [b, e]
fAppPMult (s,p) = fAppNoEq pmultSym [s, p]
fAppEMap,fAppUnion :: Ord a => (Term a, Term a) -> Term a
fAppEMap  (x,y) = fAppC    EMap     [x, y]
fAppUnion (x,y) = fAppAC    Union     [x, y]


-- | Smart constructors for DH multiplication symbols.
fAppdhMult, fAppdhTimes, fAppdhTimes2, fAppdhPlus, fAppdhExp :: (Term a, Term a) -> Term a
fAppdhMult (x,y)  = fAppNoEq dhMultSym  [x, y]
fAppdhTimes (x,y)  = fAppNoEq dhTimesSym  [x, y]
fAppdhTimes2  (b,e)  = fAppNoEq dhTimes2Sym   [b, e]
fAppdhPlus (s,p) = fAppNoEq dhPlusSym [s, p]
fAppdhExp (s,p) = fAppNoEq dhExpSym [s, p]

fAppdhGinv, fAppdhMinus, fAppdhInv, fAppdhMu, fAppdhBox, fAppdhBoxE :: Term a -> Term a
fAppdhGinv e = fAppNoEq dhGinvSym [e]
fAppdhMinus e = fAppNoEq dhMinusSym [e]
fAppdhInv e = fAppNoEq dhInvSym [e]
fAppdhMu e = fAppNoEq dhMuSym [e]
fAppdhBox e = fAppNoEq dhBoxSym [e]
fAppdhBoxE e = fAppNoEq dhBoxESym [e]

fAppdhZero, fAppdhEg, fAppdhOne :: Term a
fAppdhOne = fAppNoEq dhOneSym []
fAppdhEg = fAppNoEq dhEgSym []
fAppdhZero = fAppNoEq dhZeroSym []

-- | Smart constructors for inv, fst, and snd.
fAppInv, fAppFst, fAppSnd :: Term a -> Term a
fAppInv e = fAppNoEq invSym [e]
fAppFst a = fAppNoEq fstSym [a]
fAppSnd a = fAppNoEq sndSym [a]

-- | @lits t@ returns all literals that occur in term @t@. List can contain duplicates.
lits :: Term a -> [a]
lits = foldMap return

----------------------------------------------------------------------
-- Classifiers
----------------------------------------------------------------------

-- | 'True' iff the term is a well-formed pair.
isPair :: Show a => Term a -> Bool
isPair (viewTerm2 -> FPair _ _) = True
isPair _                        = False

-- | 'True' iff the term is a well-formed diff term.
isDiff :: Show a => Term a -> Bool
isDiff (viewTerm2 -> FDiff _ _) = True
isDiff _                        = False

-- | 'True' iff the term is a well-formed inverse.
isInverse :: Show a => Term a -> Bool
isInverse (viewTerm2 -> FInv _) = True
isInverse _                     = False

-- | 'True' iff the term is a well-formed product.
isProduct :: Show a => Term a -> Bool
isProduct (viewTerm2 -> FMult _) = True
isProduct _                      = False


-- | 'True' iff the term is a well-formed xor.
isXor :: Show a => Term a -> Bool
isXor (viewTerm2 -> FXor _) = True
isXor _                     = False

-- | 'True' iff the term is a well-formed emap.
isEMap :: Show a => Term a -> Bool
isEMap (viewTerm2 -> FEMap _ _) = True
isEMap _                        = False

-- | 'True' iff the term is a well-formed union.
isUnion :: Show a => Term a -> Bool
isUnion (viewTerm2 -> FUnion _) = True
isUnion _                       = False

-- | 'True' iff the term is a nullary, public function.
isNullaryPublicFunction :: Term a -> Bool
isNullaryPublicFunction (viewTerm -> FApp (NoEq (_, (0, Public,_))) _) = True
isNullaryPublicFunction _                                            = False

isPrivateFunction :: Term a -> Bool
isPrivateFunction (viewTerm -> FApp (NoEq (_, (_,Private,_))) _) = True
isPrivateFunction _                                            = False

-- | 'True' iff the term is an AC-operator.
isAC :: Show a => Term a -> Bool
isAC (viewTerm -> FApp (AC _) _) = True
isAC _                           = False


----------------------------------------------------------------------
-- DH Multiplication stuff
----------------------------------------------------------------------


-- | 'True' iff the term is a well-formed product.
prodTerms :: Show a => Term a -> Maybe (Term a,Term a)
prodTerms (viewTerm2 -> FdhMult x y) = Just (x,y)
prodTerms t                         = Just ( (FAPP (NoEq dhOneSym) []), t)


----------------------------------------------------------------------
-- Convert Diff Terms
----------------------------------------------------------------------

getSide :: DiffType -> Term a -> Term a
getSide _  (LIT l) = LIT l
getSide dt (FAPP (NoEq o) [t1,t2]) = case dt of
    DiffLeft  | o == diffSym -> getSide dt t1
    DiffRight | o == diffSym -> getSide dt t2
    DiffBoth  | o == diffSym -> FAPP (NoEq o) [(getSide dt t1),(getSide dt t2)]
    DiffNone  | o == diffSym -> error $ "getSide: illegal use of diff"
    _                        -> FAPP (NoEq o) [(getSide dt t1),(getSide dt t2)]
getSide dt (FAPP sym ts) = FAPP sym (map (getSide dt) ts)

getLeftTerm :: Term a -> Term a
getLeftTerm t = getSide DiffLeft t

getRightTerm :: Term a -> Term a
getRightTerm t = getSide DiffRight t

----------------------------------------------------------------------
-- "protected" subterms
-- NB: here anything but a pair or an AC symbol is protected!
----------------------------------------------------------------------

-- | Given a term, compute all protected subterms, i.e. all terms
-- which top symbol is a function, but not a pair, nor an AC symbol
allProtSubterms :: Show a => Term a -> [Term a]
allProtSubterms t@(viewTerm -> FApp _ as) | isPair t || isAC t
        = concatMap allProtSubterms as
allProtSubterms t@(viewTerm -> FApp _ as) | otherwise
        = t:concatMap allProtSubterms as
allProtSubterms _                                     = []

-- | Is term @inner@ in term @outer@ and not below a reducible function symbol?
-- This is used for the Subterm relation
elemNotBelowReducible :: Eq a => FunSig -> Term a -> Term a -> Bool
elemNotBelowReducible _ inner outer
                      | inner == outer = True
elemNotBelowReducible reducible inner (viewTerm -> FApp f as)
                      | f `S.notMember` reducible
                            = any (elemNotBelowReducible reducible inner) as
elemNotBelowReducible _ _ _ = False

----------------------------------------------------------------------
-- Pretty printing
----------------------------------------------------------------------

-- | Convert a function symbol to its name.
showFunSymName :: FunSym -> String
showFunSymName (NoEq (bs, _)) = BC.unpack bs
showFunSymName (AC op)        = show op
showFunSymName (C op )           = show op
showFunSymName List              = "List"

-- | Pretty print a term.
prettyTerm :: (Document d, Show l) => (l -> d) -> Term l -> d
prettyTerm ppLit = ppTerm
  where
    ppTerm t = case viewTerm t of
        Lit l                                     -> ppLit l
        FApp (AC o)            ts                 -> ppTerms (ppACOp o) 1 "(" ")" ts
        FApp (NoEq s)   [t1,t2] | s == expSym     -> ppTerm t1 <> text "^" <> ppTerm t2
        FApp (NoEq s)   [t1,t2] | s == diffSym    -> text "diff" <> text "(" <> ppTerm t1 <> text ", " <> ppTerm t2 <> text ")"
        FApp (NoEq s)   []      | s == natOneSym  -> text "%1"
        FApp (NoEq s)   _       | s == pairSym    -> ppTerms ", " 1 "<" ">" (split t)
        FApp (NoEq (f, _)) []                     -> text (BC.unpack f)
        FApp (NoEq (f, _)) ts                     -> ppFun f ts
        FApp (C EMap)      ts                     -> ppFun emapSymString ts
        FApp List          ts                     -> ppFun "LIST" ts

    ppACOp Mult    = "*"
    ppACOp Xor     = "⊕"
    ppACOp Union   = "++"
    ppACOp NatPlus = "%+"
 
    ppTerms sepa n lead finish ts =
        fcat . (text lead :) . (++[text finish]) .
            map (nest n) . punctuate (text sepa) . map ppTerm $ ts

    split (viewTerm2 -> FPair t1 t2) = t1 : split t2
    split t                          = [t]

    ppFun f ts =
        text (BC.unpack f ++"(") <> fsep (punctuate comma (map ppTerm ts)) <> text ")"


