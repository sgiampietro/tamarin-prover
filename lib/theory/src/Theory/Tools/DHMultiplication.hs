{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ViewPatterns     #-}
{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}
  -- spurious warnings for view patterns
-- |
-- Copyright   : (c) 2010-2012 Sofia Giampietro
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Benedikt Schmidt <beschmi@gmail.com>
-- Portability : GHC only
--
module Theory.Tools.DHMultiplication (
    clean
  , indicator
  , simplify


  -- ** Classifiers
  , isDExpRule
  , isDEMapRule
  , isDPMultRule
  ) where

import           Control.Basics hiding (empty)
import           Control.Monad.Reader

import           Data.List
import qualified Data.Set                          as S
import           Data.ByteString.Char8 (ByteString, append, pack, empty)

import           Extension.Data.Label

import           Utils.Misc

import           Term.Maude.Signature
import           Term.Narrowing.Variants.Compute
import           Term.Rewriting.Norm
import           Term.SubtermRule
import           Term.Subsumption
import           Term.Positions

import           Theory.Model
import Data.Bool (Bool)

-- import           Debug.Trace

-- Useful functions for the diffie-hellman multiplication approach
----------------------------------------------------------------------

-- | @clean@ returns the message term cleaned of its diffie-hellman terms,
-- replacing them by fresh variables

-- TODO: double check that the list of variables used in the returned substitutions are fresh 
-- the function @freshToFree@ (in Substitution.hs) seems to take care of this
-- by converting a SubstVFree (which can be obtained from a [(Lvar, VTerm Name LVar)] list) to one with free variables

-- How to generate new variables??

clean :: Show a => Term a -> (Term a, [(Lvar, VTerm Name LVar)])
clean t@(viewTerm3 -> MsgLit l) = (MsgLit l, [])
clean t@(viewTerm3 -> MsgFApp f ts) = (MsgFapp f (map (fst.clean) ts), concatMap (snd.clean) ts )
clean t@(viewTerm3 -> Box dht) = (Box (Lvar "t" LSortG), [(Lvar "t" LSortG, dht)] )
clean t@(viewTerm3 -> BoxE dht) = (BoxE (Lvar "t" LSortE), [(Lvar "t" LSortE, dht)] )
clean t@(viewTerm3 -> DH dht) = (dht, [] )

-- alternative need to do something like do v <- freshLVar "t" LSortDH. 

clean :: Show a => Term a -> (Term a, [(Lvar, VTerm Name LVar)])
clean t@(viewTerm3 -> MsgLit l) = (MsgLit l, [])
clean t@(viewTerm3 -> MsgFApp f ts) = (MsgFapp f (map (fst.clean) ts), concatMap (snd.clean) ts )
clean t@(viewTerm3 -> Box dht) = (Box (Lvar "t" LSortG), [(Lvar "t" LSortG, dht)] )
clean t@(viewTerm3 -> BoxE dht) = (BoxE (Lvar "t" LSortE), [(Lvar "t" LSortE, dht)] )
clean t@(viewTerm3 -> DH dht) = (dht, [] )

rootSet :: Show a => FunSym -> Term a -> Set (Term a)
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

rootIndicator :: Show a => Term a -> Term a

indicator :: Show a => Term a -> Term a
indicator t@(isRoot -> True) = rootIndicator t
indicator t@(isRoot -> False) = error "indicator applied on non root term"


-- Auxiliary functions we'd want to define: 
-- indicator
-- simplify
