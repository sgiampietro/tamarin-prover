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
  , isRoot
  --, isOfDHSort
  , isDHTerm
  --, isDHFact
  , isDHLit
  , isPubExp
  , isPublic
  -- , isVarEGTerm
  , compatibleLits
  , neededexponents
  , neededexponentslist
  , rootIndKnown
  , rootIndKnownMaude
  , rootIndKnown2
  , rootIndUnknown
  , eTermsOf
  , varTermsOf
  , varInMu
  --, unbox
  , isNoCanc


  --, rootIndicator
  --, indicator
   --, clean2
  -- ** Classifiers
  --, isDExpRule
  --, isDEMapRule
  --, isDPMultRule

  --, module Term.Term.Raw
  ) where

--import           Control.Basics hiding (empty)
import Control.Monad.Fresh
import           Control.Monad.Reader

--import           Data.List
import qualified Data.Map                         as Map
import qualified Data.Set                          as S
import qualified Data.Maybe                       as Maybe
--import           Data.ByteString.Char8 (ByteString, append, pack, empty)

-- import           Extension.Data.Label

--import           Utils.Misc

import           Term.Term
--import           Term.Term.FunctionSymbols
import           Term.LTerm
--import           Term.Term.Raw
--import           Term.Maude.Signature
--import           Term.Narrowing.Variants.Compute
import           Term.Rewriting.Norm
import Term.Maude.Process
--import           Term.SubtermRule
--import           Term.Subsumption
--import           Term.Substitution
--import           Term.Positions


-- import           Theory.Model
--import Data.Bool (Bool)
--import Theory.Model (getFactTerms)

import           Debug.Trace
import Text.PrettyPrint.Class (Document(text))

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
    dhMuSym    -> LSortE
    --[ t1 ]     | o == dhBoxSym    -> Box (t1)
    --[ t1 ]     | o == dhBoxESym    -> BoxE (t1)
    dhZeroSym    -> LSortE
    dhEgSym    -> LSortG
    dhOneSym    -> LSortE

clean :: MonadFresh m => Term (Lit Name LVar) -> m (Term (Lit Name LVar), [(LVar,VTerm Name LVar)])
clean t@(viewTerm3 -> MsgLit l) = return (LIT l, [])
clean t@(viewTerm3 -> MsgFApp f ts) =  do
                                            cleanedts <- mapM clean ts 
                                            return (FAPP f (map fst cleanedts),  (concatMap snd cleanedts)  )
clean t@(viewTerm3 -> DH f dht) = do 
                                      varx <- freshLVar "clt" (determineSort t)
                                      return ( LIT (Var varx) , [(varx, t)] )



rootSet :: (Show a, Ord a ) => DHMultSym -> Term a -> S.Set (Term a)
rootSet operator t@(LIT l) = S.singleton t
rootSet operator t@(FAPP (DHMult o) ts) = case ts of
    --[t1]       | o == dhBoxSym    -> rootSet operator t1
    --[t1]       | o == dhBoxESym    -> rootSet operator t1
    [ t1, t2 ] | o == operator    -> S.union (rootSet operator t1) (rootSet operator t2)
    [ t1, t2 ] | o /= operator    -> S.singleton t
    [ t1 ]                        -> S.singleton t
    []                            -> S.singleton t
    _         -> error $ "malformed term `"++show t++"'"
rootSet operator t = error ("rootSet applied on non DH term'"++show t++"Done")

multRootList :: LNTerm ->  [LNTerm]
multRootList a = case sortOfLNTerm a of
  LSortG -> trace (show (a, "LSORTG", S.toList (rootSet dhMultSym a))) $ S.toList (rootSet dhMultSym a)
  LSortPubG -> trace (show (a, "LSORTPubG", S.toList (rootSet dhMultSym a))) $ S.toList (rootSet dhMultSym a)
  LSortE -> trace (show (a, "LSORTE", S.toList (rootSet dhPlusSym a))) $ S.toList (rootSet dhPlusSym a)
  LSortNZE -> trace (show (a, "LSORTNZE", S.toList (rootSet dhPlusSym a))) $ S.toList (rootSet dhPlusSym a)
  LSortFrNZE -> trace (show (a, "LSORTFrNZE", S.toList (rootSet dhPlusSym a))) $ S.toList (rootSet dhPlusSym a)
  _ -> error ("rootSet applied on non DH term'"++show a)


isRoot :: (Show a, Ord a ) => DHMultSym -> Term a -> Bool
isRoot o (LIT l) = True
--isRoot o t@(viewTerm3 -> Box dht) = isRoot o dht
--isRoot o t@(viewTerm3 -> BoxE dht) = isRoot o dht
isRoot o t@(viewTerm3 -> DH dht ts) = S.size (rootSet o t) == 1
isRoot o _ = error "rootSet applied on non DH term'"

--unbox :: LNTerm -> LNTerm
--unbox t@(viewTerm3 -> Box dht) = dht
--unbox t@(viewTerm3 -> BoxE dht) = dht
--unbox t = t 

eTermsOf :: LNTerm -> [ LNTerm ]
--eTermsOf t@(viewTerm3 -> Box dht) = eTermsOf dht
--eTermsOf t@(viewTerm3 -> BoxE dht) = eTermsOf dht
eTermsOf t@(LIT l)
  | isEVar t = [t]
  | isNZEVar t = [t]
  | isFrNZEVar t = [t]
  | otherwise = []
eTermsOf t@(FAPP f ts) = concatMap eTermsOf ts

varInMu :: LNTerm -> [LVar]
varInMu t@(LIT l) = []
varInMu t@(viewTerm2 -> FdhMu t1) =  varsVTerm t1
varInMu t@(FAPP (DHMult o) []) = []
varInMu t@(FAPP (DHMult o) ts) = concatMap varInMu ts
-- varInMu t@(FAPP (DHMult dhEgSym) ts) = error ("soitisthis:"++(show ts))
-- varInMu t@(FAPP (NoEq o) []) = [] -- TODO: FIX THIS. Unclear why Maude normalized a term into sort Msg instead of G??
varInMu t = error ("shouldn't get to this term"++(show t))

varTermsOf :: LNTerm -> [ LNTerm ]
--varTermsOf t@(viewTerm3 -> Box dht) = varTermsOf dht
--varTermsOf t@(viewTerm3 -> BoxE dht) = varTermsOf dht
varTermsOf t@(LIT l)
  | isvarGVar t = [t]
  | isvarEVar t = [t]
  | otherwise = []
varTermsOf t@(FAPP f ts) = concatMap varTermsOf ts

{-}
varTermOf :: LNTerm -> LNTerm -> [(LNTerm, LNTerm)]
varTermOf t@(LIT l) var
  | isvarGVar t = (t, acc) 
  | isvarEVar t = []
  | otherwise =  []
varTermOf t@(FAPP (DHMult o) ts) acc =     case ts of 
    [ t1, t2 ] | o == dhMultSym   -> (case sortOfLNTerm t2 
                                        LsortVarG -> (t1, basisOf t2)
                                        _ -> ) 
    [ t1, t2 ] | o == dhPlusSym   -> varTermOf t1 acc ++ varTermOf t2 acc
    [ t1, t2 ] | o == dhTimesESym   -> ( Just ( (Maybe.fromMaybe [] $ fst $ varTermOf t1) ++ (Maybe.fromMaybe [] $ fst $ varTermOf t2)) , Nothing)
    [ t1, t2 ] | o == dhTimesSym   -> ( Just ( (Maybe.fromMaybe [] $ fst $ varTermOf t1) ++ (Maybe.fromMaybe [] $ fst $ varTermOf t2)) , Nothing)
    [t1]       | o == dhMuSym  -> (Nothing, Nothing)
    _                               -> error $ "term not in normal form?: `"++show t++"'"
-}

--indComputable :: S.Set LNTerm -> LNTerm -> Bool
--indComputable bs t = S.fromList ( eTermsOf t ) `S.isSubsetOf` bs


isDHLit :: LNTerm -> Bool
-- isDHLit t@(viewTerm3 -> Box dht) = isDHLit dht
-- isDHLit t@(viewTerm3 -> BoxE dht) = isDHLit dht
isDHLit t@(viewTerm -> Lit (Var _)) = isOfDHSort t
isDHLit _ = False


isPubExp :: LNTerm -> Maybe (LNTerm, LNTerm)
-- isDHLit t@(viewTerm3 -> Box dht) = isDHLit dht
-- isDHLit t@(viewTerm3 -> BoxE dht) = isDHLit dht
isPubExp t@(viewTerm2 -> FdhExp t1 t2) = if (isPubGVar t1 || isGConst t1) then (Just (t1,t2)) else Nothing
isPubExp _ = Nothing

compatibleLits :: LNTerm -> LNTerm -> Bool
compatibleLits ta1 ta2 = case sortCompare (sortOfLNTerm ta1) (sortOfLNTerm ta2) of
                          Just GT -> True
                          Just EQ -> True
                          Just LT -> False
                          Nothing -> False


{-
compatibleLits :: LNTerm -> LNTerm -> Maybe Bool
compatibleLits ta1 ta2 = (if (sortCompare (sortOfLNTerm ta1) (sortOfLNTerm ta2) == Nothing) then Nothing else 
                            (case (isDHLit ta1, isDHLit ta2) of
                                  (True, True) ->  Just True
                                  (True, _ ) -> Just (sortCompare (sortOfLNTerm ta1) (sortOfLNTerm ta2) == Just GT)
                                  (_, True) -> Just (sortCompare (sortOfLNTerm ta1) (sortOfLNTerm ta2) == Just LT)
                                  (_, _) -> Just False)) -}

-- TODO: this function should actually return which indicators are needed too in the 
-- case it's not computable. 
neededexponents:: S.Set LNTerm -> S.Set LNTerm -> LNTerm -> [LNTerm]
neededexponents b nb t
  | null es = []
  | otherwise = S.toList es
      where es =S.fromList ( eTermsOf t ) `S.difference` (b `S.union` nb)

neededexponentslist:: S.Set LNTerm -> S.Set LNTerm -> [LNTerm] -> Maybe (S.Set LNTerm)
neededexponentslist b nb terms
  | null es = Nothing
  | otherwise = Just es
      where es = S.fromList $ concatMap (neededexponents b nb) terms

isPublic :: LNTerm -> Bool
isPublic indt = case viewTerm2 (indt) of
                (DHOne) -> True
                (DHEg) -> True
                (Lit2 t) | (isPubGVar (LIT t))  -> True
                (Lit2 t) | (isGConst (LIT t)) -> True
                _ -> False

--rootIndicator :: S.Set LNTerm -> S.Set LNTerm -> LNTerm -> (LNTerm, [(LVar, VTerm Name LVar)])
--rootIndicator b nb t
--  | indComputable (b `S.union` nb) t = (rootIndKnown b nb t,[])
--  | otherwise = rootIndUnknown b nb t

indIsOne :: S.Set LNTerm -> S.Set LNTerm -> LNTerm -> Bool
indIsOne b nb t@(viewTerm2 -> FdhExp t1 t2) = if S.member t2 nb then True else False
indIsOne b nb t = False

rootIndKnown :: S.Set LNTerm -> S.Set LNTerm -> LNTerm -> LNTerm
rootIndKnown b nb t@(viewTerm2 -> FdhExp t1 t2) = (FAPP (DHMult dhExpSym) [ rootIndKnown b nb t1, rootIndKnown b nb t2])
rootIndKnown b nb t@(viewTerm2 -> FdhGinv dht) = rootIndKnown b nb dht--(FAPP (DHMult dhGinvSym) [rootIndKnown b nb dht])
rootIndKnown b nb t@(viewTerm2 -> FdhTimes t1 t2) = (FAPP (DHMult dhTimesSym) [rootIndKnown b nb t1, rootIndKnown b nb t2] )
rootIndKnown b nb t@(viewTerm2 -> FdhTimesE t1 t2) =  (FAPP (DHMult dhTimesESym) [rootIndKnown b nb t1, rootIndKnown b nb t2])
rootIndKnown b nb t@(viewTerm2 -> FdhMu t1) = if indIsOne b nb t1 then trace (show ("HERE",t) ) (FAPP (DHMult dhOneSym) []) else t --  rootIndKnown b nb t1 -- TODO FIX: you should also consider the possibility of finding rootIndKnown of t1. -- (FAPP (DHMult dhZeroSym) [])
rootIndKnown b nb t@(viewTerm2 -> FdhMinus t1) = rootIndKnown b nb t1
rootIndKnown b nb t@(viewTerm2 -> FdhInv t1) = FAPP (DHMult dhInvSym) [rootIndKnown b nb t1]
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
rootIndKnown b nb t = error ("rootSet applied on non DH"++show t++"term")

rootIndKnownMaude::  S.Set LNTerm -> S.Set LNTerm -> LNTerm -> WithMaude LNTerm
rootIndKnownMaude b nb t = norm' (rootIndKnown b nb t)

rootIndKnown2 :: MaudeHandle -> S.Set LNTerm -> S.Set LNTerm -> LNTerm -> LNTerm
rootIndKnown2 hnd b nb t@(viewTerm2 -> FdhExp t1 t2) = runReader (norm' (FAPP (DHMult dhExpSym) [ rootIndKnown2 hnd b nb t1, rootIndKnown2 hnd b nb t2])) hnd
rootIndKnown2 hnd b nb t@(viewTerm2 -> FdhGinv dht) = rootIndKnown2 hnd b nb dht--(FAPP (DHMult dhGinvSym) [rootIndKnown b nb dht])
rootIndKnown2 hnd b nb t@(viewTerm2 -> FdhTimes t1 t2) = runReader (norm' (FAPP (DHMult dhTimesSym) [rootIndKnown2 hnd b nb t1, rootIndKnown2 hnd b nb t2] )) hnd
rootIndKnown2 hnd b nb t@(viewTerm2 -> FdhTimesE t1 t2) =  runReader (norm' (FAPP (DHMult dhTimesESym) [rootIndKnown2 hnd b nb t1, rootIndKnown2 hnd b nb t2])) hnd
rootIndKnown2 hnd b nb t@(viewTerm2 -> FdhMu t1) = if (isPublic $ rootIndKnown2 hnd b nb t1) then trace (show ("pubind", t, t1, rootIndKnown2 hnd b nb t1)) (FAPP (DHMult dhOneSym) []) else trace (show ("privind", t, t1, rootIndKnown2 hnd b nb t1)) t --  rootIndKnown b nb t1 -- TODO FIX: you should also consider the possibility of finding rootIndKnown of t1. -- (FAPP (DHMult dhZeroSym) [])
rootIndKnown2 hnd b nb t@(viewTerm2 -> FdhMinus t1) = rootIndKnown2 hnd b nb t1
rootIndKnown2 hnd b nb t@(viewTerm2 -> FdhInv t1) = FAPP (DHMult dhInvSym) [rootIndKnown2 hnd b nb t1]
--rootIndKnown b nb t@(viewTerm2 -> FdhBox (LIT a)) = (t)
--rootIndKnown b nb t@(viewTerm2 -> FdhBoxE (LIT (Var t1)))
--  | S.member (LIT (Var t1)) nb = (FAPP (DHMult dhOneSym) [])
--  | S.member (LIT (Var t1)) b = (t)
--  | otherwise = error ("this shouldn't happen" ++ show (t, b, nb) ++ "ops")
-- rootIndKnown b nb t@(viewTerm2 -> FdhBoxE (LIT (Con t1))) = (LIT (Con t1))
rootIndKnown2 hnd b nb t@(viewTerm2 -> Lit2 (Var t1))
  | S.member t nb = (FAPP (DHMult dhOneSym) [])
  -- | S.member t b = (t)
  | otherwise  = t -- (if isPubGVar t then (FAPP (DHMult dhEgSym) []) else t) -- this is a G variable
rootIndKnown2 hnd b nb t@(viewTerm2 -> Lit2 (Con _)) = t -- (FAPP (DHMult dhEgSym) [])
rootIndKnown2 hnd b nb t@(viewTerm2 -> DHZero) = (FAPP (DHMult dhOneSym) [])
rootIndKnown2 hnd b nb t@(viewTerm2 -> DHOne) = (FAPP (DHMult dhOneSym) [])
rootIndKnown2 hnd b nb t@(viewTerm2 -> DHEg) = (FAPP (DHMult dhEgSym) [])
rootIndKnown2 hnd b nb t = error ("rootSet applied on non DH"++show t++"term")


rootIndUnknown :: S.Set LNTerm -> S.Set LNTerm -> LNTerm -> (LNTerm, [(LVar, VTerm Name LVar)])
rootIndUnknown n nb t = ( LIT (Var newv), [(newv, t)])
    where newv = getNewSimilarVar (LVar "t" LSortG 0) tvars
          tvars =  varsVTerm t


isNoCanc :: LNTerm -> LNTerm -> Bool
isNoCanc _ _ = True

{-
isNoCanc :: LNTerm -> LNTerm -> Bool
isNoCanc t1 t2 | isFrNZEVar t1 = True
               | isFrNZEVar t2 = True
               | otherwise = case viewTerm2 t2 of
                  DHOne -> True
                  FdhExp t3 t4 | isFrNZEVar t4 -> True
                  _     -> (case viewTerm2 t1 of --TODO: fix this case. 
                            DHOne -> True
                            FdhExp t3 t4 | isFrNZEVar t4 -> True
                            _ -> False) -}

isDHTerm :: LNTerm -> Bool
isDHTerm t = case viewTerm3 t of
      MsgLit _ -> isOfDHSort t
      MsgFApp _ _ -> False
      DH _ _ -> True



