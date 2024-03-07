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
  , neededexponents
  , rootIndKnown
  , rootIndUnknown
  , eTermsOf
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

import           Control.Basics hiding (empty)
import           Control.Monad.Reader

import           Data.List
import qualified Data.Map                         as Map
import qualified Data.Set                          as S
import           Data.ByteString.Char8 (ByteString, append, pack, empty)

-- import           Extension.Data.Label

import           Utils.Misc

import           Term.Term
import           Term.Term.FunctionSymbols
import           Term.LTerm
--import           Term.Term.Raw
import           Term.Maude.Signature
import           Term.Narrowing.Variants.Compute
import           Term.Rewriting.Norm
import           Term.SubtermRule
--import           Term.Subsumption
import           Term.Substitution
import           Term.Positions


-- import           Theory.Model
import Data.Bool (Bool)

-- import           Debug.Trace

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

-- | @clean@ returns the message term cleaned of its diffie-hellman terms,
-- replacing them by fresh variables

-- TODO: double check that the list of variables used in the returned substitutions are fresh 
-- the function @freshToFree@ (in Substitution.hs) seems to take care of this
-- by converting a SubstVFree (which can be obtained from a [(LVar, VTerm Name LVar)] list) to one with free variables
{-
composeVFresh2 :: (IsConst c) => LSubstVFresh c -> LSubstVFresh c -> LSubstVFresh c
composeVFresh2 s1_0 s2 = composeVFresh  s1_0 s2_0
  where
    s2_0 = freshToFreeAvoiding s2 s1_0 

composeVFresh3 :: (IsConst c) => LSubstVFresh c -> LSubstVFresh c -> LSubstVFresh c
composeVFresh3 s1_0 s2 = composeVFresh  s1_0 s2_0
  where
    s2_0 = domainToFreeAvoidingFast s2 s1_0 

clean :: Term (Lit Name LVar) -> (Term (Lit Name LVar), LNSubstVFresh)
clean t@(viewTerm3 -> MsgLit l) = (LIT l, emptySubstVFresh)
clean t@(viewTerm3 -> MsgFApp f ts) = (FAPP f (map (fst.clean) ts), foldl composeVFresh2 emptySubstVFresh (map (snd.clean) ts ) )
clean t@(viewTerm3 -> Box dht) = (FAPP (NoEq dhBoxSym) [LIT (Var (LVar "t" LSortG 0))], substFromListVFresh [(LVar "t" LSortG 0 , dht)] )
clean t@(viewTerm3 -> BoxE dht) = (FAPP (NoEq dhBoxESym) [LIT (Var (LVar "t" LSortE 0))], substFromListVFresh [(LVar "t" LSortE 0, dht)] )
clean t@(viewTerm3 -> DH f dht) = (FAPP f dht, emptySubstVFresh )
-}


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

myFirst :: (a,b,c) -> a
myFirst (x,y,z) = x

mySecond :: (a,b,c) -> b
mySecond (x,y,z) = y

myThird :: (a,b,c) -> c
myThird (x,y,z) = z

clean :: Term (Lit Name LVar) -> [LVar] -> (Term (Lit Name LVar), [(LVar,VTerm Name LVar)], [LVar])
clean t@(viewTerm3 -> MsgLit l) vars = (LIT l, [], vars)
clean t@(viewTerm3 -> MsgFApp f ts) vars=  case ts of 
  [t1, t2] -> (FAPP f [myFirst ts1, myFirst ts2], mySecond ts1 `union` (mySecond ts2), vars1 `union` (myThird ts2) )
                where   ts1 = clean t1 vars
                        ts2 = clean t2 vars1
                        vars1 = vars `union` (myThird ts1) 
  [t1] -> (FAPP f [myFirst ts1], mySecond ts1, vars `union` (myThird ts1) )
                where   ts1 = clean t1 vars
  [] -> (FAPP f [], [], vars)
clean t@(viewTerm3 -> Box dht) vars = (FAPP (DHMult dhBoxSym) [LIT (Var vg )], [(vg, dht)], vg:dhtvars )
  where vg = (getVarGAvoid dhtvars vars)
        dhtvars = (varsVTerm dht)
clean t@(viewTerm3 -> BoxE dht) vars = (FAPP (DHMult dhBoxESym) [LIT (Var ve)], [(ve, dht)], ve:dhtvars )
  where ve = (getVarEAvoid dhtvars vars)
        dhtvars = (varsVTerm dht)
clean t@(viewTerm3 -> DH f dht) vars = (FAPP f dht, [], vars )



rootSet :: (Show a, Ord a ) => DHMultSym -> Term a -> S.Set (Term a)
rootSet operator t@(LIT l) = S.singleton t
rootSet operator t@(FAPP (DHMult o) ts) = case ts of
    [ t1, t2 ] | o == operator    -> S.union (rootSet operator t1) (rootSet operator t2)
    [ t1, t2 ] | o /= operator    -> S.singleton t
    [ t1 ]                        -> S.singleton t
    []                            -> S.singleton t
    _         -> error $ "malformed term `"++show t++"'"
rootSet operator _ = error "rootSet applied on non DH term'"

multRootList :: (Show a, Ord a ) => Term a ->  [(Term a)]
multRootList a = S.toList (rootSet dhMultSym a)

isRoot :: (Show a, Ord a ) => DHMultSym -> Term a -> Bool
isRoot o (LIT l) = True
isRoot o t@(viewTerm3 -> Box dht) = isRoot o dht
isRoot o t@(viewTerm3 -> BoxE dht) = isRoot o dht
isRoot o t@(viewTerm3 -> DH dht ts) = S.size (rootSet o t) == 1
isRoot o _ = error "rootSet applied on non DH term'"

eTermsOf :: LNTerm -> [ LNTerm ]
eTermsOf t@(LIT l)
  -- | isEVar t = [t]
  -- | isNZEVar t = [t]
  | isFrNZEVar t = [t]
  | otherwise = []
eTermsOf t@(FAPP f ts) = concatMap eTermsOf ts


indComputable :: S.Set LNTerm -> LNTerm -> Bool
indComputable bs t = S.fromList( eTermsOf t ) `S.isSubsetOf` bs


-- TODO: this function should actually return which indicators are needed too in the 
-- case it's not computable. 
neededexponents:: S.Set LNTerm -> S.Set LNTerm -> LNTerm -> Maybe (S.Set LNTerm)
neededexponents b nb t 
  | null es = Nothing
  | otherwise = Just es
      where es =S.fromList( eTermsOf t ) `S.difference` (b `S.union` nb)

rootIndicator :: S.Set LNTerm -> S.Set LNTerm -> LNTerm -> (LNTerm, [(LVar, VTerm Name LVar)])
rootIndicator b nb t
  | indComputable (b `S.union` nb) t = (rootIndKnown b nb t,[])
  | otherwise = rootIndUnknown b nb t

rootIndKnown :: S.Set LNTerm -> S.Set LNTerm -> LNTerm -> LNTerm
rootIndKnown b nb t@(viewTerm2 -> FdhExp t1 t2) = (FAPP (DHMult dhExpSym) [ rootIndKnown b nb t1, rootIndKnown b nb t2])
rootIndKnown b nb t@(viewTerm2 -> FdhGinv dht) = (FAPP (DHMult dhGinvSym) [rootIndKnown b nb dht])
rootIndKnown b nb t@(viewTerm2 -> FdhTimes t1 t2) = (FAPP (DHMult dhTimesSym) [rootIndKnown b nb t1, rootIndKnown b nb t2] )
rootIndKnown b nb t@(viewTerm2 -> FdhTimes2 t1 t2) = (FAPP (DHMult dhTimes2Sym) [rootIndKnown b nb t1, rootIndKnown b nb t2])
rootIndKnown b nb t@(viewTerm2 -> FdhMu t1) = (FAPP (DHMult dhOneSym) [])
rootIndKnown b nb t@(viewTerm2 -> FdhBox (LIT a)) = (t)
rootIndKnown b nb t@(viewTerm2 -> FdhBoxE (LIT (Var t1)))
  | S.member t nb = (FAPP (DHMult dhOneSym) [])
  | S.member t b = (t)
  | otherwise = error "this shouldn't happen"
rootIndKnown b nb t@(viewTerm2 -> FdhBoxE (LIT (Con t1))) = (t)
rootIndKnown b nb t@(viewTerm2 -> Lit2 (Var t1))
  | S.member t nb = (FAPP (DHMult dhOneSym) [])
  | S.member t b = (t)
  | otherwise  = (t) -- this is a G variable
rootIndKnown b nb t@(viewTerm2 -> DHZero) = (FAPP (DHMult dhOneSym) [])
rootIndKnown b nb t@(viewTerm2 -> DHOne) = (FAPP (DHMult dhOneSym) [])
rootIndKnown b nb _ = error "rootSet applied on non DH term'"

rootIndUnknown :: S.Set LNTerm -> S.Set LNTerm -> LNTerm -> (LNTerm, [(LVar, VTerm Name LVar)])
rootIndUnknown n nb t = ( LIT (Var newv), [(newv, t)])
    where newv = getNewSimilarVar (LVar "t" LSortG 0) tvars
          tvars =  varsVTerm t


isNoCanc :: LNTerm -> LNTerm -> Bool
isNoCanc t1 t2 = case viewTerm2 t2 of 
        DHOne -> True
        _ -> (case viewTerm2 t1 of --TODO: fix this case. 
              DHOne -> True
              _ -> False) 


{-
-- instead of just returning the indicator, we also return a list of variables that is unempty only if
-- the function cannot yet be evaluated, in which case it contains the exponents that don't belong to N neither NB yet.  
rootIndicator :: Show a => Set (Term a) -> Set (Term a) -> Term a -> (Term a, [(LVar, VTerm Name LVar)])
rootIndicator b nb t@(viewTerm2 -> FdhExp t1 t2) = (FAPP (NoEq dhExpSym) [fst $ rootIndicator b nb t1, fst $ rootIndicator b nb t2], concat (snd $ rootIndicator b nb t1) (snd $ rootIndicator b nb t1) )
rootIndicator b nb t@(viewTerm2 -> FdhGinv dht) = (FAPP (NoEq FdhGinv) [fst $ rootIndicator b nb dht], snd $ rootIndicator b nb dht)
rootIndicator b nb t@(viewTerm2 -> FdhTimes t1 t2) = (FAPP (NoEq dhTimesSym) [fst $ rootIndicator b nb t1, fst $ rootIndicator b nb t2], concat (snd $ rootIndicator b nb t1) (snd $ rootIndicator b nb t1) )
rootIndicator b nb t@(viewTerm2 -> FdhTimes2 t1 t2) = (FAPP (NoEq dhTimes2Sym) [fst $ rootIndicator b nb t1, fst $ rootIndicator b nb t2], concat (snd $ rootIndicator b nb t1) (snd $ rootIndicator b nb t1) )
rootIndicator b nb t@(viewTerm2 -> FdhMu t1) = (FAPP (NoEq dhOne) [], [])
rootIndicator b nb t@(viewTerm2 -> FdhBoxE (LIT t1))
  | S.member t nb = (FAPP (NoEq dhOne) [], [])
  | S.member t b = (t, [])
  | otherwise = (LIT (Var ), [(LVar "t" LSortE, dht)])
rootIndicator b nb t@(viewTerm2 -> LitG (Con c)) = t
rootIndicator b nb _ = error "rootSet applied on non DH term'"

indicator :: Show a => Set (Term a) -> Set (Term a) -> Term a -> Term a
indicator b nb t@(isRoot dhMultSym -> True) = rootIndicator b nb t
indicator b nb t@(isRoot dhMultSym -> False) = error "indicator applied on non root term"
-}
-- TODO missing auxiliary functions: 
-- but first check how unification in simplified theory (should be able to leveage)
-- on current DH unification approach. 
-- simplify
