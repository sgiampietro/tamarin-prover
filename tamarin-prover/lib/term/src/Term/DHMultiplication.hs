{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ViewPatterns     #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
  -- spurious warnings for view patterns
-- |
-- Copyright   : (c) 2010-2012 Sofia Giampietro
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Benedikt Schmidt <beschmi@gmail.com>
-- Portability : GHC only
--
module Term.DHMultiplication (
    clean
  , rootSet
  , multRootList
  , multRootMixed
  , extractMixedRoot
  , isRoot
  --, isOfDHSort
  , isDHTerm
  , isExpTerm
  , isMuTerm
  , isSameSymb
  , isOfBase
  --, isDHFact
  , isDHLit
  , isDHInvLit
  , getInvLit
  , isPubExp
  , isPublic
  , containsBP
  , removesBP
  , addsBP
  , getsBPbase
  , expBase
  , listOfExponents
  -- , isMult
  -- , isVarEGTerm
  , compatibleLits
  , compatibleLitsStrict
  , neededexponents
  , neededexponentslist
  , rootIndKnown
  , rootIndKnownMaude
  , rootIndKnown2
  , rootIndUnknown
  , eTermsOf
  , varTermsOf
  , varTermsOf'
  , varInMu
  --, unbox
  , isNoCanc
  , notUnifiableLits

  --, rootIndicator
  --, indicator
   --, clean2
  -- ** Classifiers
  --, isDExpRule
  --, isDEMapRule
  --, isDPMultRule

  ) where

--import           Control.Basics hiding (empty)
import Control.Monad.Fresh
import           Control.Monad.Reader

import qualified          Data.List as List
import qualified Data.Map                         as Map
import qualified Data.Set                          as S
import qualified Data.Maybe                       as Maybe

--import           Data.ByteString.Char8 (ByteString, append, pack, empty)

-- import           Extension.Data.Label

--import           Utils.Misc

import           Term.Term
--import           Term.Term.FunctionSymbols
import           Term.LTerm
-- import           Term.Term.Raw (foldTerm)
--import           Term.Maude.Signature
--import           Term.Narrowing.Variants.Compute
import             Term.Rewriting.Norm (norm')
-- import             Term.Rewriting.Definitions
import Term.Maude.Process
--import           Term.SubtermRule
--import           Term.Subsumption
--import           Term.Substitution
--import           Term.Positions


-- import           Theory.Model
--import Data.Bool (Bool)
--import Theory.Model (getFactTerms)

import           Debug.Trace.Ignore
import Text.PrettyPrint.Class (Document(text))
import GHC.IO.Exception (blockedIndefinitelyOnSTM)
--import Theory (Fact(factTerms))

-- Useful functions for the diffie-hellman multiplication approach
----------------------------------------------------------------------

getNewSimilarVar :: LVar -> [LVar] -> LVar
getNewSimilarVar x allVars
  | elem x allVars  =  LVar (lvarName x) (lvarSort x) $ (+) 1 $ foldr (max . lvarIdx) (lvarIdx x) allVars
  | otherwise = x

getVarGAvoid:: [LVar]  -> [LVar] -> LVar
getVarGAvoid t vs= getNewSimilarVar (LVar "t" LSortG 0) (t ++ vs)

getVarEAvoid:: [LVar]  -> [LVar] -> LVar
getVarEAvoid t vs= getNewSimilarVar (LVar "t" LSortE 0) (t ++ vs)


applyTermSubst:: Map.Map LVar LVar -> Term (Lit Name LVar) -> Term (Lit Name LVar)
applyTermSubst vs (LIT t) = case t of
  (Con tc) -> (LIT t)
  (Var tv) -> (case (Map.lookup tv vs) of
      (Just tv2) -> (LIT (Var tv2))
      Nothing -> (LIT t))
applyTermSubst vs (FAPP f ts) = FAPP f (map (applyTermSubst vs) ts )

applyVarSubst:: Map.Map LVar LVar ->  LVar -> LVar
applyVarSubst vs tv = (case (Map.lookup tv vs) of
      (Just tv2) -> tv2
      Nothing -> tv)


determineSort :: Term (Lit Name LVar) -> LSort
determineSort t@(FAPP (DHMult o) ts ) = case o of
    dhMultSym   -> LSortG
    dhTimesSym   -> LSortE
    dhTimesESym   -> LSortE
    dhExpSym   -> LSortG
    dhPlusSym   -> LSortE
    dhGinvSym    -> LSortG
    dhInvSym    -> LSortG
    dhMinusSym    -> LSortE
    dhMuSym    -> LSortNZE
    dhMu2Sym    -> LSortNZE
    --[ t1 ]     | o == dhBoxSym    -> Box (t1)
    --[ t1 ]     | o == dhBoxESym    -> BoxE (t1)
    dhZeroSym    -> LSortE
    dhEgSym    -> LSortG
    dhOneSym    -> LSortE
    dhBPSym -> LSortG
    dhHSym -> LSortNZE

clean :: MonadFresh m => Term (Lit Name LVar) -> m (Term (Lit Name LVar), [(LVar,VTerm Name LVar)])
clean t@(viewTerm3 -> MsgLit l) = return (LIT l, [])
clean t@(viewTerm3 -> MsgFApp f ts) =  do
                                            cleanedts <- mapM clean ts 
                                            return (FAPP f (map fst cleanedts),  (concatMap snd cleanedts)  )
clean t@(viewTerm3 -> DH f dht) = do 
                                      varx <- freshLVar "clt" (determineSort t)
                                      return ( LIT (Var varx) , [(varx, t)] )


expBase ::  LNTerm -> LNTerm
expBase t@(LIT l) = if (isPubGVar t || isGConst t) then t else pubGTerm "g"
expBase t@(FAPP (DHMult o) ts) = case ts of
    [ t1, t2 ] | o == dhMultSym   -> expBase t1
    [ t1, t2 ] | o == dhTimesSym   ->  pubGTerm "g" -- technically should not get here. 
    [ t1, t2 ] | o == dhTimesESym   -> pubGTerm "g"
    [ t1, t2 ] | o == dhExpSym   ->  t1
    [ t1, t2 ] | o == dhPlusSym   -> pubGTerm "g"
    [ t1, t2 ] | o == dhMu2Sym   -> pubGTerm "g"
    [ t1, t2 ] | o == dhH2Sym   -> pubGTerm "g"
    [ t1, t2 ] | o == dhBPSym -> t
    [ t1 ]     | o == dhGinvSym    ->  expBase t1
    [ t1 ]     | o == dhInvSym    -> pubGTerm "g"
    [ t1 ]     | o == dhMinusSym    -> pubGTerm "g"
    [ t1 ]     | o == dhMuSym    -> pubGTerm "g"
    [ t1 ]     | o == dhHSym     -> pubGTerm "g"
    --[ t1 ]     | o == dhBoxSym    -> gTerm2Exp t1
    --[ t1 ]     | o == dhBoxESym    -> gTerm2Exp t1
    []         | o == dhZeroSym    -> pubGTerm "g"
    []         | o == dhEgSym    ->  t
    []         | o == dhOneSym    -> pubGTerm "g"
    _                               -> error $ "unexpected term form: `"++show t++"'"
expBase t =  error $ "unexpected term form2: `"++show t++"'"


rootSet :: (Show a, Ord a ) => DHMultSym -> Term a -> S.Set (Term a)
rootSet operator t@(LIT l) = S.singleton t
rootSet operator t@(FAPP (DHMult o) ts) = case ts of
    --[t1]       | o == dhBoxSym    -> rootSet operator t1
    --[t1]       | o == dhBoxESym    -> rootSet operator t1
    [ t1, t2 ] | o == operator    -> S.union (rootSet operator t1) (rootSet operator t2)
    [ t1, t2 ] | o /= operator    -> S.singleton t
    [ t1 ]     | o == dhGinvSym   -> rootSet o t1
    [ t1 ]     | o == dhInvSym   -> rootSet o t1
    [ t1 ]     | o == dhMinusSym  -> rootSet o t1
    [ t1 ]                        -> S.singleton t
    []                            -> S.singleton t
    _         -> error $ "malformed term `"++show t++"'"
rootSet operator t = error ("rootSet applied on non DH term'"++show t++"Done")

multRootList :: LNTerm ->  [LNTerm]
multRootList a = case sortOfLNTerm a of
  LSortG -> S.toList (rootSet dhMultSym a)
  LSortPubG -> S.toList (rootSet dhMultSym a)
  LSortE -> S.toList (rootSet dhPlusSym a)
  LSortNZE -> S.toList (rootSet dhPlusSym a)
  LSortFrNZE -> S.toList (rootSet dhPlusSym a)
  -- error ("rootSet applied on non DH term'"++show a)

rootSetMu :: (Show a, Ord a ) => DHMultSym -> Term a -> S.Set (Term a)
rootSetMu operator t@(LIT l) = S.singleton t
rootSetMu operator t@(FAPP (DHMult o) ts) = case ts of
    --[t1]       | o == dhBoxSym    -> rootSet operator t1
    --[t1]       | o == dhBoxESym    -> rootSet operator t1
    [ t1, t2 ] | o == operator    -> S.union (rootSet operator t1) (rootSet operator t2)
    [ t1, t2 ] | o /= operator    -> S.singleton t
    [ t1 ]     | o == dhGinvSym   -> rootSet o t1
    [ t1 ]     | o == dhInvSym   -> rootSet o t1
    [ t1 ]     | o == dhMinusSym  -> rootSet o t1
    [ t1 ]     | o == dhMuSym  -> rootSet o t1
    [ t1 ]                        -> S.singleton t
    []                            -> S.singleton t
    _         -> error $ "malformed term `"++show t++"'"
rootSetMu operator t = error ("Mu applied on non DH term'"++show t++"Done")

multRootMixed :: LNTerm ->  [LNTerm]
multRootMixed a = case sortOfLNTerm a of
  LSortG -> S.toList (rootSetMu dhMultSym a)
  LSortPubG -> S.toList (rootSetMu dhMultSym a)
  LSortE -> S.toList (rootSetMu dhPlusSym a)
  LSortNZE -> S.toList (rootSetMu dhPlusSym a)
  LSortFrNZE -> S.toList (rootSetMu dhPlusSym a)
  _ -> [] -- error ("rootSet applied on non DH term'"++show a)

extractMixedRoot :: LNTerm -> [(LNTerm, LNTerm)]
extractMixedRoot t = case viewTerm2 t of
                        (FPair x y) -> trace (show ("extractmiced root", t)) (map (\rx -> (rx,x) ) $ multRootMixed x) ++ extractMixedRoot y-- (map (\ry -> (ry,y) ) $ multRootMixed y)  
                        _ -> if isDHTerm t then  trace (show ("extractmiced root2", t)) $ trace (show ("extractmiced root", t))  map (\rt -> (rt, t)) $ multRootList t else trace (show ("extractmiced root3", t)) []
 
isRoot :: (Show a, Ord a ) => DHMultSym -> Term a -> Bool
isRoot o (LIT l) = True
--isRoot o t@(viewTerm3 -> Box dht) = isRoot o dht
--isRoot o t@(viewTerm3 -> BoxE dht) = isRoot o dht
isRoot o t@(viewTerm3 -> DH dht ts) = S.size (rootSet o t) == 1
isRoot o _ = error "rootSet applied on non DH term'"


isSameSymb :: DHMultSym -> LNTerm -> Bool 
isSameSymb symb t1 = case t1 of 
  (FAPP (DHMult o) ts) | o == symb -> True
  _ -> False

isOfBase :: LNTerm -> LNTerm -> Bool 
isOfBase base t1 = expBase t1 == base

containsBP :: LNTerm -> Bool
containsBP = foldTerm (const False) ffapp
  where ffapp funsym bls = case funsym of 
            (DHMult (bs, _)) | bs == dhBPSymString -> True
                             | otherwise -> or bls
            _ -> or bls

-- following function replaces every occurence of bp(g1,g2) with 1
removesBP :: LNTerm -> LNTerm
removesBP = foldTerm (\a -> LIT a) ffapp
  where ffapp funsym fterms = case funsym of
          DHMult bs | bs == dhBPSym -> fAppdhOne
                    | otherwise -> FAPP funsym fterms         
          _ -> FAPP funsym fterms

getsBPbase :: LNTerm -> Maybe (LNTerm, LNTerm)
getsBPbase t = go t
  where go (LIT a) = Nothing 
        go (FAPP funsym fterms) = case fterms of 
          (x:y:zs) -> case funsym of
              DHMult bs | bs == dhBPSym -> Just (x,y)
                        | bs == dhExpSym -> go y
                        | bs == dhMultSym -> go x
                        | otherwise -> if Maybe.isNothing gx then (go y) else gx  
                                                where gx = go x     
              _ -> Nothing
          _ -> Nothing

-- the following function re-introduces bp(g1,g2) in the exponent of 
-- each root term, and sets the correct base gt
--  Assumes we know that the entire term is a ROOT BP term 
-- and that it is in normal form!
addsBP :: LNTerm -> LNTerm -> LNTerm -> LNTerm -> LNTerm
addsBP gT g1 g2 = foldTerm (\a -> LIT a) ffapp
  where ffapp funsym fterms = case funsym of 
            DHMult bs | bs == dhExpSym -> case fterms of 
                                                  (x:y:zs) -> FAPP funsym (gT:(fAppdhTimesE (fAppdhBP (g1,g2), y)):zs)
                                                  _ -> error "shouldn't get here"
                      | otherwise -> FAPP funsym fterms
            _ -> FAPP funsym fterms


-- assuming the input is a ROOT term, this function return the list of (multiplied)
-- exponent terms (i.e. LIT terms) that form the exponent
listOfExponents :: LNTerm -> [LNTerm] 
listOfExponents t@(LIT _) = [t]
listOfExponents t = case viewTerm2 t of
                      FdhExp t1 t2 -> listOfExponents t2
                      FdhTimes t1 t2 -> listOfExponents t1 ++ listOfExponents t2
                      FdhTimesE t1 t2 -> listOfExponents t1 ++ listOfExponents t2
                      FdhMu _ -> [t]
                      FdhMu2 _ _ -> [t]
                      FdhH _ -> [t]
                      FdhH2 _ _ -> [t]
                      FdhInv t1 -> listOfExponents t1
                      FdhMinus t1 -> listOfExponents t1
                      _ -> [] 



--------------------------------------------------------------
--------------------------------------------------------------




eTermsOf :: LNTerm -> [ LNTerm ]
--eTermsOf t@(viewTerm3 -> Box dht) = eTermsOf dht
--eTermsOf t@(viewTerm3 -> BoxE dht) = eTermsOf dht
eTermsOf t@(LIT l)
  | isEVar t = [t]
  | isNZEVar t = [t]
  | isFrNZEVar t = [t]
  | otherwise = []
eTermsOf t@(FAPP (DHMult o) ts) 
  | o == dhMuSym = [t]
  | otherwise = concatMap eTermsOf ts
eTermsOf t@(FAPP f ts) = concatMap eTermsOf ts

varInMu :: LNTerm -> [LVar]
varInMu t@(LIT l) = []
varInMu t@(viewTerm2 -> FdhMu t1) =  varsVTerm t1
varInMu t@(viewTerm2 -> FdhH t1) =  varsVTerm t1
varInMu t@(viewTerm2 -> FdhH2 t1 t2) =  varsVTerm t1 ++ varsVTerm t2
varInMu t@(viewTerm2 -> FdhMu2 t1 t2) =  varsVTerm t1 ++ varsVTerm t2
varInMu t@(FAPP (DHMult o) []) = []
varInMu t@(FAPP (DHMult o) ts) = concatMap varInMu ts
varInMu t = error ("shouldn't get to this term"++(show t))

varTermsOf :: LNTerm -> [ LNTerm ]
--varTermsOf t@(viewTerm3 -> Box dht) = varTermsOf dht
--varTermsOf t@(viewTerm3 -> BoxE dht) = varTermsOf dht
varTermsOf t@(LIT l)
  | isvarGVar t = [t]
  | isvarEVar t = [t]
  | otherwise = []
varTermsOf t@(FAPP f ts) = concatMap varTermsOf ts

varTermsOf' :: LNTerm -> [ LVar ]
varTermsOf' t@(LIT (Var l))
  | isvarGVar t = [l]
  | isvarEVar t = [l]
  | otherwise = []
varTermsOf' t@(LIT _) = []
varTermsOf' t@(FAPP f ts) = concatMap varTermsOf' ts


isDHLit :: LNTerm -> Bool
isDHLit t@(viewTerm -> Lit (Var _)) = isOfDHSort t
isDHLit _ = False

isDHInvLit :: LNTerm -> Bool
isDHInvLit t@(viewTerm2 -> FdhInv t1) = isDHLit t1
isDHInvLit _ = False

getInvLit:: LNTerm -> LNTerm
getInvLit t@(viewTerm2 -> FdhInv t1) = t1
getInvLit _ = error "not inverse term for getInvLit function"

isPubExp :: LNTerm -> Maybe (LNTerm, LNTerm)
isPubExp t@(viewTerm2 -> FdhExp t1 t2) = if (isPubGVar t1 || isGConst t1) then (Just (t1,t2)) else Nothing
isPubExp _ = Nothing

compatibleVars :: LVar -> LVar -> Bool
compatibleVars ta1 ta2 = case sortCompare (sortOfLNTerm (varTerm ta1)) (sortOfLNTerm (varTerm ta2)) of
                          Just GT -> True
                          Just EQ -> True
                          Just LT -> False
                          Nothing -> False

compatibleLitsStrict :: LNTerm -> LNTerm -> Bool
compatibleLitsStrict ta1 ta2 = case sortCompare (sortOfLNTerm ta1) (sortOfLNTerm ta2) of
                          Just GT -> True
                          Just EQ -> True
                          Just LT -> False
                          Nothing -> False


compatibleLits :: LNTerm -> LNTerm -> Bool
compatibleLits t t2 = True -- ta1@(viewTerm -> Lit (Var v1)) ta2 = all (compatibleVars v1) $ varsVTerm ta2
                      

notUnifiableLits :: LNTerm -> LNTerm -> Bool
notUnifiableLits ta1 ta2 
  | (isDHLit ta1 && (compatibleLits ta1 ta2) ) = False
  | (isDHLit ta2 && (compatibleLits ta2 ta1) ) = False
  | (isDHLit ta1 && (not $ compatibleLits ta1 ta2) ) = True
  | (isDHLit ta2 && (not $ compatibleLits ta2 ta1) ) = True
  | otherwise = False

 
neededexponents:: S.Set LNTerm -> S.Set (LNTerm, NodeId) -> LNTerm -> ([LNTerm], [NodeId])
neededexponents b nb t
  | null es = ([], map snd (filter (\(y,_) -> y `elem` et) (S.toList nb)))
  | otherwise = (S.toList es, map snd (filter (\(y,_) -> y `elem` et) (S.toList nb)))
      where et = eTermsOf t
            es = trace (show ("thishose", b, nb, eTermsOf t)) $ S.fromList et `S.difference` (b `S.union` (S.map fst nb))

neededexponentslist:: S.Set LNTerm -> S.Set (LNTerm,NodeId) -> [LNTerm] -> ([LNTerm], [NodeId])
neededexponentslist b nb terms = myNub es
      where es1 = map (neededexponents b nb) terms
            es = foldr (\(a,b) (c,d) -> (a++c,b++d)) ([],[]) es1
            myNub (a,b) = (List.nub a, List.nub b) 

isPublic :: LNTerm -> Bool
isPublic indt = case viewTerm2 (indt) of
                (DHOne) -> True
                (DHEg) -> True
                (Lit2 t) | (isPubGVar (LIT t))  -> True
                (Lit2 t) | (isGConst (LIT t)) -> True
                _ -> False

isMult :: LNTerm -> Bool
isMult t@(viewTerm2 -> FdhMult t1 t2) = True
isMult _ = False


indIsOne :: S.Set LNTerm -> S.Set LNTerm -> LNTerm -> Bool
indIsOne b nb t@(viewTerm2 -> FdhExp t1 t2) = if S.member t2 nb then True else False
indIsOne b nb t = False

rootIndKnown :: S.Set LNTerm -> S.Set LNTerm -> LNTerm -> LNTerm
rootIndKnown b nb t@(viewTerm2 -> FdhExp t1 t2) = (FAPP (DHMult dhExpSym) [ rootIndKnown b nb t1, rootIndKnown b nb t2])
rootIndKnown b nb t@(viewTerm2 -> FdhGinv dht) = rootIndKnown b nb dht--(FAPP (DHMult dhGinvSym) [rootIndKnown b nb dht])
rootIndKnown b nb t@(viewTerm2 -> FdhTimes t1 t2) = (FAPP (DHMult dhTimesSym) [rootIndKnown b nb t1, rootIndKnown b nb t2] )
rootIndKnown b nb t@(viewTerm2 -> FdhTimesE t1 t2) =  (FAPP (DHMult dhTimesESym) [rootIndKnown b nb t1, rootIndKnown b nb t2])
rootIndKnown b nb t@(viewTerm2 -> FdhMu t1) = if indIsOne b nb t1 then (FAPP (DHMult dhOneSym) []) else t --  rootIndKnown b nb t1 -- TODO FIX: you should also consider the possibility of finding rootIndKnown of t1. -- (FAPP (DHMult dhZeroSym) [])
rootIndKnown b nb t@(viewTerm2 -> FdhMu2 t1 t2) = if indIsOne b nb t1 then (if indIsOne b nb t2 then (FAPP (DHMult dhOneSym) []) else (FAPP (DHMult dhMuSym) [t2])) else (if indIsOne b nb t2 then (FAPP (DHMult dhMuSym) [t1]) else t) --  rootIndKnown b nb t1 -- TODO FIX: you should also consider the possibility of finding rootIndKnown of t1. -- (FAPP (DHMult dhZeroSym) [])
rootIndKnown b nb t@(viewTerm2 -> FdhMinus t1) = rootIndKnown b nb t1
rootIndKnown b nb t@(viewTerm2 -> FdhInv t1) = FAPP (DHMult dhInvSym) [rootIndKnown b nb t1]
rootIndKnown b nb t@(viewTerm2 -> FdhBP t1 t2) = (FAPP (DHMult dhOneSym) []) -- TODO: how to handle this??
--rootIndKnown b nb t@(viewTerm2 -> FdhBox (LIT a)) = (t)
--rootIndKnown b nb t@(viewTerm2 -> FdhBoxE (LIT (Var t1)))
--  | S.member (LIT (Var t1)) nb = (FAPP (DHMult dhOneSym) [])
--  | S.member (LIT (Var t1)) b = (t)
--  | otherwise = error ("this shouldn't happen" ++ show (t, b, nb) ++ "ops")
-- rootIndKnown b nb t@(viewTerm2 -> FdhBoxE (LIT (Con t1))) = (LIT (Con t1))
rootIndKnown b nb t@(viewTerm2 -> Lit2 (Var t1))
  | S.member t nb = (FAPP (DHMult dhOneSym) [])
  -- | S.member t b = (t)
  | otherwise  = t -- (if isPubGVar t then (FAPP (DHMult dhEgSym) []) else t) -- this is a G variable
rootIndKnown b nb t@(viewTerm2 -> Lit2 (Con _)) = t -- (FAPP (DHMult dhEgSym) [])
rootIndKnown b nb t@(viewTerm2 -> DHZero) = (FAPP (DHMult dhOneSym) [])
rootIndKnown b nb t@(viewTerm2 -> DHOne) = (FAPP (DHMult dhOneSym) [])
rootIndKnown b nb t@(viewTerm2 -> DHEg) = (FAPP (DHMult dhEgSym) [])
rootIndKnown b nb t = error ("rootSetIndKnwon applied on non DH"++show t++"term")

rootIndKnownMaude::  S.Set LNTerm -> S.Set LNTerm -> LNTerm -> WithMaude LNTerm
rootIndKnownMaude b nb t = norm' (rootIndKnown b nb t)

rootIndKnown2 :: MaudeHandle -> S.Set LNTerm -> S.Set LNTerm -> LNTerm -> LNTerm
rootIndKnown2 hnd b nb t@(viewTerm2 -> FdhExp t1 t2) = runReader (norm' (FAPP (DHMult dhExpSym) [ rootIndKnown2 hnd b nb t1, rootIndKnown2 hnd b nb t2])) hnd
rootIndKnown2 hnd b nb t@(viewTerm2 -> FdhGinv dht) = rootIndKnown2 hnd b nb dht--(FAPP (DHMult dhGinvSym) [rootIndKnown b nb dht])
rootIndKnown2 hnd b nb t@(viewTerm2 -> FdhTimes t1 t2) = runReader (norm' (FAPP (DHMult dhTimesSym) [rootIndKnown2 hnd b nb t1, rootIndKnown2 hnd b nb t2] )) hnd
rootIndKnown2 hnd b nb t@(viewTerm2 -> FdhTimesE t1 t2) =  runReader (norm' (FAPP (DHMult dhTimesESym) [rootIndKnown2 hnd b nb t1, rootIndKnown2 hnd b nb t2])) hnd
rootIndKnown2 hnd b nb t@(viewTerm2 -> FdhMu t1) 
  | S.member t nb = FAPP (DHMult dhOneSym) []
  | otherwise = t
rootIndKnown2 hnd b nb t@(viewTerm2 -> FdhBP t1 t2) = (FAPP (DHMult dhOneSym) [])
rootIndKnown2 hnd b nb t@(viewTerm2 -> FdhH t1) = t
--rootIndKnown2 hnd b nb t@(viewTerm2 -> FdhMu t1) = if isMult t1 then t else (if (isPublic $ rootIndKnown2 hnd b nb t1) then trace (show ("pubind", t, t1, rootIndKnown2 hnd b nb t1)) (FAPP (DHMult dhOneSym) []) else trace (show ("privind", t, t1, rootIndKnown2 hnd b nb t1)) t) --  rootIndKnown b nb t1 -- TODO FIX: you should also consider the possibility of finding rootIndKnown of t1. -- (FAPP (DHMult dhZeroSym) [])
rootIndKnown2 hnd b nb t@(viewTerm2 -> FdhMinus t1) = rootIndKnown2 hnd b nb t1
rootIndKnown2 hnd b nb t@(viewTerm2 -> FdhInv t1) = FAPP (DHMult dhInvSym) [rootIndKnown2 hnd b nb t1]
rootIndKnown2 hnd b nb t@(viewTerm2 -> Lit2 (Var t1))
  | S.member t nb = (FAPP (DHMult dhOneSym) [])
  | otherwise  = t 
rootIndKnown2 hnd b nb t@(viewTerm2 -> Lit2 (Con _)) = t 
rootIndKnown2 hnd b nb t@(viewTerm2 -> DHZero) = (FAPP (DHMult dhOneSym) [])
rootIndKnown2 hnd b nb t@(viewTerm2 -> DHOne) = (FAPP (DHMult dhOneSym) [])
rootIndKnown2 hnd b nb t@(viewTerm2 -> DHEg) = (FAPP (DHMult dhEgSym) [])
rootIndKnown2 hnd b nb t = error ("rootdhInd2 applied on non DH"++show t++"term")


rootIndUnknown :: S.Set LNTerm -> S.Set LNTerm -> LNTerm -> (LNTerm, [(LVar, VTerm Name LVar)])
rootIndUnknown n nb t = ( LIT (Var newv), [(newv, t)])
    where newv = getNewSimilarVar (LVar "t" LSortG 0) tvars
          tvars =  varsVTerm t


isNoCanc :: LNTerm -> LNTerm -> Bool
isNoCanc x y 
      | all (\x -> sortOfLNTerm x == LSortFrNZE ) (evars1++evars2) = True 
      | all (\x -> elem x $ varInMu y) (varsVTerm x) = True
      | otherwise = False
    where evars1 = eTermsOf x
          evars2 = eTermsOf y


isDHTerm :: LNTerm -> Bool
isDHTerm t = case viewTerm3 t of
      MsgLit _ -> isOfDHSort t
      MsgFApp _ _ -> False
      DH _ _ -> True

isExpTerm :: LNTerm -> Bool 
isExpTerm t = case viewTerm2 t of
      FdhExp _ _ -> True
      _          -> False


isMuTerm :: LNTerm -> Bool 
isMuTerm t = case viewTerm2 t of
      FdhMu _  -> True
      FdhGinv t1 -> isMuTerm t1
      FdhExp _ t1 -> isMuTerm t1 
      FdhInv t1 -> isMuTerm t1
      FdhMinus t1 -> isMuTerm t1
      FdhMu2 _ _ -> True
      FdhH2 _ _ -> True
      FdhH _ -> True
      _          -> False


