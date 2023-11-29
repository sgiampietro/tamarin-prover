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
  --  clean
  --, rootSet
  --, isRoot
  --, rootIndicator
  --, indicator
clean, 
   clean2_acc
   , applyTermSubst
   , clean2
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

-- | Types to keep track of used variables

type PreSubst c = ([(LVar, LTerm c)], [LVar])
type EqsSubst a = ([Equal a], [LVar])


getNewSimilarVar :: LVar -> [LVar] -> LVar
getNewSimilarVar x allVars = LVar (lvarName x) (lvarSort x) $ (+) 1 $ foldr (max . lvarIdx) (lvarIdx x) allVars

getVarGAvoid:: Term (Lit Name LVar)  -> LVar
getVarGAvoid t= getNewSimilarVar (LVar "t" LSortG 0) (varsVTerm t) 

getVarEAvoid:: Term (Lit Name LVar)  -> LVar
getVarEAvoid t= getNewSimilarVar (LVar "t" LSortE 0) (varsVTerm t) 

-- | @clean@ returns the message term cleaned of its diffie-hellman terms,
-- replacing them by fresh variables

-- TODO: double check that the list of variables used in the returned substitutions are fresh 
-- the function @freshToFree@ (in Substitution.hs) seems to take care of this
-- by converting a SubstVFree (which can be obtained from a [(LVar, VTerm Name LVar)] list) to one with free variables


{-
clean2 :: Show a => Term a -> (Term a, [(Term a, VTerm Name LVar)])
clean2 t = case (viewTerm3 t) of
                (MsgLit l) -> (LIT l, [])
                (MsgFApp f ts) -> (FAPP f (map (fst.clean2) ts), concatMap (snd.clean2) ts )
                (Box dht) -> (FAPP (NoEq dhBoxSym) [(LVar "t" LSortG)], [(LVar "t" LSortG, dht)] )
                (BoxE dht) -> (FAPP (NoEq dhBoxESym) [(LVar "t" LSortE)], [(LVar "t" LSortE, dht)] )
                (DH f dht) -> (FAPP f dht, [] )
-}


{-
clean2 t@(viewTerm3 -> MsgLit l) = (LIT l, [])
clean2 t@(viewTerm3 -> MsgFApp f ts) = (FAPP f (map (fst.clean) ts), concatMap (snd.clean) ts )
clean2 t@(viewTerm3 -> Box dht) = (FAPP (NoEq dhBoxSym) [(LVar "t" LSortG)], [(LVar "t" LSortG, dht)] )
clean2 t@(viewTerm3 -> BoxE dht) = (FAPP (NoEq dhBoxESym) [(LVar "t" LSortE)], [(LVar "t" LSortE, dht)] )
clean2 t@(viewTerm3 -> DH f dht) = (FAPP f dht, [] )
-}


-- alternative need to do something like do v <- freshLVar "t" LSortDH. 
-- Need to be able to compose VFresh substitutions. 
{-
domainToFreeAvoidingFast :: ( Ord c) => LSubstVFresh c -> Subst c v -> LSubst c
domainToFreeAvoidingFast s t =
    substFromList . renameMappings . substToListVFresh $ s
  where
    renameMappings l = zip (rename (map fst l) `evalFreshAvoiding` (dom t)) (map snd l)


composeVFresh2 :: (IsConst c) => LSubstVFresh c -> LSubstVFresh c -> LSubstVFresh c
composeVFresh2 s1_0 s2 = composeVFresh  s1_0 s2_0
  where
    s2_0 = freshToFreeAvoiding s1_0 s2 

composeVFresh3 :: (IsConst c) => LSubstVFresh c -> LSubstVFresh c -> LSubstVFresh c
composeVFresh3 s1_0 s2 = composeVFresh  s1_0 s2_0
  where
    s2_0 = domainToFreeAvoidingFast s2 s1_0 


domainAvoidingFast :: (HasFrees t) => [(LVar,VTerm Name LVar)] -> t -> [(LVar,VTerm Name LVar)]
domainAvoidingFast s t = renameMappings s
  where
    renameMappings l = zip (rename (map fst l) `evalFreshAvoiding` t) (map snd l)

--- todo: make sure that "t" does not appear in the term dht in the 3rd and 4th case. 




clean :: Term (Lit Name LVar) -> (Term (Lit Name LVar), LNSubstVFresh)
clean t@(viewTerm3 -> MsgLit l) = (LIT l, emptySubstVFresh)
clean t@(viewTerm3 -> MsgFApp f ts) = (FAPP f (map (fst.clean) ts), foldl composeVFresh2 emptySubstVFresh (map (snd.clean) ts ) )
clean t@(viewTerm3 -> Box dht) = (FAPP (NoEq dhBoxSym) [LIT (Var (LVar "t" LSortG 0))], substFromListVFresh [(LVar "t" LSortG 0 , dht)] )
clean t@(viewTerm3 -> BoxE dht) = (FAPP (NoEq dhBoxESym) [LIT (Var (LVar "t" LSortE 0))], substFromListVFresh [(LVar "t" LSortE 0, dht)] )
clean t@(viewTerm3 -> DH f dht) = (FAPP f dht, emptySubstVFresh )
-}

clean2_acc :: [(LVar,VTerm Name LVar)] -> [LVar] -> [(LVar, LVar)]
clean2_acc []    acc   = []
clean2_acc (x:xss)  acc = (fst x, newx): (clean2_acc xss ((newx):acc)) 
  where newx = getNewSimilarVar (fst x) ((map fst xss)++acc)

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




-- todo: define "apply subst function"
clean :: Term (Lit Name LVar) -> (Term (Lit Name LVar), [(LVar,VTerm Name LVar)])
clean t@(viewTerm3 -> MsgLit l) = (LIT l, [])
clean t@(viewTerm3 -> MsgFApp f ts) =  (FAPP f  (map fst tss), (concatMap snd tss ) )
      where  tss = map clean ts
clean t@(viewTerm3 -> Box dht) = (FAPP (NoEq dhBoxSym) [LIT (Var vg )], [(vg, dht)] )
  where vg = (getVarGAvoid dht)
clean t@(viewTerm3 -> BoxE dht) = (FAPP (NoEq dhBoxESym) [LIT (Var ve)], [(ve, dht)] )
  where ve = (getVarEAvoid dht)
clean t@(viewTerm3 -> DH f dht) = (FAPP f dht, [] )

clean2 :: Term (Lit Name LVar) -> (Term (Lit Name LVar), [(LVar,VTerm Name LVar)])
clean2 t@(viewTerm3 -> MsgLit l) = clean t
clean2 t@(viewTerm3 -> MsgFApp f ts) = ( (applyTermSubst tosubst) (fst tss), map (\(a,b) -> (applyVarSubst tosubst a, b)) (snd tss ) )
  where tosubst = Map.fromList (clean2_acc (snd tss) [])
        tss = clean t
clean2 t@(viewTerm3 -> Box dht) = clean t
clean2 t@(viewTerm3 -> BoxE dht) = clean t
clean2 t@(viewTerm3 -> DH f dht) = clean t



-- todo: define "apply subst function"
cleanold :: Term (Lit Name LVar) -> (Term (Lit Name LVar), [(LVar,VTerm Name LVar)])
cleanold t@(viewTerm3 -> MsgLit l) = (LIT l, [])
cleanold t@(viewTerm3 -> MsgFApp f ts) =  (FAPP f (map (applyTermSubst tosubst) (map fst tss)), map (\(a,b) -> (applyVarSubst tosubst a, b)) (concatMap snd tss ) )
  where tosubst = Map.fromList (clean2_acc (concatMap snd tss) [])
        tss = map clean2 ts
cleanold t@(viewTerm3 -> Box dht) = (FAPP (NoEq dhBoxSym) [LIT (Var vg )], [(vg, dht)] )
  where vg = (getVarGAvoid dht)
cleanold t@(viewTerm3 -> BoxE dht) = (FAPP (NoEq dhBoxESym) [LIT (Var ve)], [(ve, dht)] )
  where ve = (getVarEAvoid dht)
cleanold t@(viewTerm3 -> DH f dht) = (FAPP f dht, [] )




{--
rootSet :: Show a => FunSym -> Term a -> S.Set (Term a)
rootSet operator t@(FAPP (NoEq o) ts) = case ts of
    [ t1, t2 ] | o == operator    -> concat (rootSet t1) (rootSet t2)
    [ t1, t2 ] | o /= operator    -> S.singleton t
    [ t1 ]                        -> S.singleton t
    []                            -> S.singleton t
    _         -> error $ "malformed term `"++show t++"'"
rootSet operator _ = error "rootSet applied on non DH term'"

--rootSet t@(viewTerm2 -> FdhMult t1 t2) = S.fromList [t1, t2] 
--rootSet t@(viewTerm2 -> Box dht) = rootSet dht
--rootSet t@(viewTerm2 -> BoxE dht) = rootSet dht
--rootSet _ = error "rootSet applied on non DH term'"

isRoot :: Show a => FunSym -> Term a -> Bool
isRoot o t@(viewTerm3 -> Box dht) = isRoot o dht
isRoot o t@(viewTerm3 -> BoxE dht) = isRoot o dht
isRoot o t@(viewTerm3 -> DH dht) = S.size (rootSet o dht) == 1
isRoot o _ = error "rootSet applied on non DH term'"


frInd :: Show a => Term a -> Term a

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
--}

-- TODO missing auxiliary functions: 
-- but first check how unification in simplified theory (should be able to leveage)
-- on current DH unification approach. 
-- simplify
