{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
  -- for ByteString
-- |
-- Copyright   : (c) 2010-2012 Benedikt Schmidt & Simon Meier
-- License     : GPL v3 (see LICENSE)
-- 
-- Maintainer  : Benedikt Schmidt <beschmi@gmail.com>
--
-- Function Symbols and Signatures.
module Term.Term.FunctionSymbols (
    -- ** AC, C, and NonAC funcion symbols
      FunSym(..)
    , ACSym(..)
    , CSym(..)
    , Privacy(..)
    , Constructability(..)
    , NoEqSym
    , DHMultSym

    -- ** Signatures
    , FunSig
    , NoEqFunSig
    , DHMultFunSig

    -- ** concrete symbols strings
    , diffSymString
    , munSymString
    , expSymString
    , invSymString
    , dhNeutralSymString
    , pmultSymString
    , emapSymString
    , unionSymString
    , oneSymString
    , fstSymString
    , sndSymString
    , multSymString
    , zeroSymString
    , xorSymString
    , natPlusSymString
    , natOneSymString
    -- SOFIA: DH mult function symbols (repeating ones that also exist for normal DH theory): 
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

    -- ** concrete symbols
    , diffSym
    , expSym
    , pmultSym
    , oneSym
    , dhNeutralSym
    , invSym
    , pairSym
    , fstSym
    , sndSym
    , fstDestSym
    , sndDestSym    
    , zeroSym
    , natOneSym
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
    , xorFunSig
    , bpFunSig
    , msetFunSig
    , pairFunSig
    , pairFunDestSig    
    , dhReducibleFunSig
    , bpReducibleFunSig
    , xorReducibleFunSig
    , implicitFunSig
    , natFunSig
    , dhMultFunSig
    ) where

import           GHC.Generics (Generic)
import           Data.Typeable
import           Data.Binary
import           Data.Data


import           Control.DeepSeq

import           Data.ByteString (ByteString)
import           Extension.Data.ByteString ()
import           Data.ByteString.Char8 ()

import           Data.Set (Set)
import qualified Data.Set as S

----------------------------------------------------------------------
-- Function symbols
----------------------------------------------------------------------

-- | AC function symbols.
data ACSym = Union | Mult | Xor | NatPlus
  deriving (Eq, Ord, Typeable, Data, Show, Generic, NFData, Binary)

-- | A function symbol can be either Private (unknown to adversary) or Public.
data Privacy = Private | Public
  deriving (Eq, Ord, Typeable, Data, Show, Generic, NFData, Binary)

-- | A function symbol can be either a constructor or a destructor in which
-- case it only applies if it reduces.
data Constructability = Constructor | Destructor
  deriving (Eq, Ord, Typeable, Data, Show, Generic, NFData, Binary)

-- | NoEq function symbols (with respect to the background theory).
type NoEqSym = (ByteString, (Int, Privacy,Constructability)) -- ^ operator name, arity, private, destructor

type DHMultSym = (ByteString, (Int, Privacy,Constructability)) -- ^ operator name, arity, private, destructor


-- | C(ommutative) function symbols
data CSym = EMap
  deriving (Eq, Ord, Typeable, Data, Show, Generic, NFData, Binary)

-- | Function symbols
data FunSym = NoEq  NoEqSym   -- ^ a free function function symbol of a given arity
            | DHMult DHMultSym
            | AC    ACSym     -- ^ an AC function symbol, can be used n-ary
            | C     CSym      -- ^ a C function symbol of a given arity
            | List            -- ^ a free n-ary function symbol of TOP sort
  deriving (Eq, Ord, Typeable, Data, Show, Generic, NFData, Binary)

-- | Function signatures.
type FunSig = Set FunSym

-- | NoEq function signatures.
type NoEqFunSig = Set NoEqSym

-- | NoEq function signatures.
type DHMultFunSig = Set DHMultSym


----------------------------------------------------------------------
-- Fixed function symbols
----------------------------------------------------------------------

diffSymString, munSymString, expSymString, invSymString, dhNeutralSymString, oneSymString, xorSymString, multSymString, zeroSymString, fstSymString, sndSymString :: ByteString
diffSymString = "diff"
munSymString = "mun"
expSymString = "exp"
invSymString = "inv"
oneSymString = "one"
fstSymString = "fst"
sndSymString = "snd"
dhNeutralSymString = "DH_neutral"
multSymString = "mult"
zeroSymString = "zero"
xorSymString = "xor"

natPlusSymString, natOneSymString :: ByteString
natPlusSymString = "tplus"
natOneSymString = "tone"

unionSymString :: ByteString
unionSymString = "union"

emapSymString, pmultSymString :: ByteString
emapSymString  = "em"
pmultSymString = "pmult"

dhMultSymString, dhGinvSymString, dhZeroSymString, dhMinusSymString,dhInvSymString,dhEgSymString,dhTimes2SymString, dhTimesSymString, dhPlusSymString,dhExpSymString,dhOneSymString, dhMuSymString, dhBoxSymString, dhBoxESymString :: ByteString
dhMultSymString = "dhMult"
dhGinvSymString = "dhGinv"
dhZeroSymString = "dhZero"
dhMinusSymString = "dhMinus"
dhInvSymString = "dhInv"
dhEgSymString = "dhEg"
dhTimes2SymString = "dhTimes2"
dhTimesSymString = "dhTimes"
dhPlusSymString = "dhPlus"
dhExpSymString = "dhExp"
dhOneSymString = "dhOne"
dhMuSymString = "dhMu"
dhBoxSymString = "dhBox"
dhBoxESymString = "dhBoxE"

pairSym, diffSym, expSym, invSym, oneSym, dhNeutralSym, fstSym, sndSym, pmultSym, zeroSym, natOneSym :: NoEqSym
-- | Pairing.
pairSym  = ("pair",(2,Public,Constructor))
-- | Diff.
diffSym  = (diffSymString,(2,Private,Constructor))
-- | Exponentiation.
expSym   = (expSymString,(2,Public,Constructor))
-- | The inverse in the groups of exponents.
invSym   = (invSymString,(1,Public,Constructor))
-- | The one in the group of exponents.
oneSym   = (oneSymString,(0,Public,Constructor))
-- | The groupd identity
dhNeutralSym = (dhNeutralSymString,(0,Public, Constructor))
-- | Projection of first component of pair.
fstSym   = (fstSymString,(1,Public,Constructor))
-- | Projection of second component of pair.
sndSym   = (sndSymString,(1,Public,Constructor))
-- | Multiplication of points (in G1) on elliptic curve by scalars.
pmultSym = (pmultSymString,(2,Public,Constructor))
-- | The zero for XOR.
zeroSym  = (zeroSymString,(0,Public,Constructor))
-- | One for natural numbers.
natOneSym = (natOneSymString, (0,Public,Constructor))

dhMultSym, dhGinvSym, dhZeroSym, dhMinusSym,dhInvSym,dhEgSym,dhTimes2Sym, dhTimesSym, dhPlusSym,dhExpSym,dhOneSym, dhMuSym, dhBoxSym, dhBoxESym :: DHMultSym
dhMultSym = (dhMultSymString,(2,Public,Constructor))
dhGinvSym = (dhGinvSymString,(1,Public,Constructor))
dhZeroSym = (dhZeroSymString,(0,Public,Constructor))
dhMinusSym = (dhMinusSymString,(1,Public,Constructor))
dhInvSym = (dhInvSymString,(1,Public,Constructor))
dhEgSym = (dhEgSymString,(0,Public,Constructor))
dhTimesSym = (dhTimesSymString,(2,Public,Constructor))
dhTimes2Sym = (dhTimes2SymString,(2,Public,Constructor))
dhPlusSym = (dhPlusSymString,(2,Public,Constructor))
dhExpSym = (dhExpSymString,(2,Public,Constructor))
dhOneSym = (dhOneSymString,(0,Public,Constructor))
dhMuSym = (dhMuSymString,(1,Public,Constructor))
dhBoxSym = (dhBoxSymString,(1,Private,Constructor))
dhBoxESym = (dhBoxESymString,(1,Private,Constructor))

mkDestSym :: NoEqSym -> NoEqSym
mkDestSym (name,(k,p,_)) = (name,(k,p, Destructor))

fstDestSym, sndDestSym :: NoEqSym
-- | Projection of first component of pair.
fstDestSym   = mkDestSym fstSym
-- | Projection of second component of pair.
sndDestSym   = mkDestSym sndSym

----------------------------------------------------------------------
-- Fixed signatures
----------------------------------------------------------------------

-- | The signature for Diffie-Hellman function symbols.
dhFunSig :: FunSig
dhFunSig = S.fromList [ AC Mult, NoEq expSym, NoEq oneSym, NoEq invSym, NoEq dhNeutralSym ]

dhMultFunSigDH :: DHMultFunSig
dhMultFunSigDH = S.fromList [dhMultSym, dhGinvSym, dhZeroSym, dhMinusSym, dhInvSym, dhEgSym, dhTimes2Sym, dhExpSym, dhOneSym, dhTimesSym, dhPlusSym, dhMuSym, dhBoxSym, dhBoxESym] 

dhMultFunSig :: FunSig
dhMultFunSig = S.fromList [DHMult dhMultSym, DHMult dhGinvSym, DHMult dhZeroSym, DHMult dhMinusSym, DHMult dhInvSym, DHMult dhEgSym, DHMult dhTimes2Sym, DHMult dhExpSym, DHMult dhOneSym, DHMult dhTimesSym, DHMult dhPlusSym, DHMult dhMuSym, DHMult dhBoxSym, DHMult dhBoxESym] 


-- | The signature for Xor function symbols.
xorFunSig :: FunSig
xorFunSig = S.fromList [ AC Xor, NoEq zeroSym ]

-- | The signature for the bilinear pairing function symbols.
bpFunSig :: FunSig
bpFunSig = S.fromList [ NoEq pmultSym, C EMap ]

-- | The signature for the multiset function symbols.
msetFunSig :: FunSig
msetFunSig = S.fromList [AC Union]

-- | The signature for pairing.
pairFunSig :: NoEqFunSig
pairFunSig = S.fromList [ pairSym, fstSym, sndSym ]

-- | The signature for pairing with destructors.
pairFunDestSig :: NoEqFunSig
pairFunDestSig = S.fromList [ pairSym, fstDestSym, sndDestSym ]

-- | Reducible function symbols for DH.
dhReducibleFunSig :: FunSig
dhReducibleFunSig = S.fromList [ NoEq expSym, NoEq invSym ]

-- | Reducible function symbols for BP.
bpReducibleFunSig :: FunSig
bpReducibleFunSig = S.fromList [ NoEq pmultSym, C EMap ]

-- | Reducible function symbols for XOR.
xorReducibleFunSig :: FunSig
xorReducibleFunSig = S.fromList [ AC Xor ]

-- | Implicit function symbols.
implicitFunSig :: FunSig
implicitFunSig = S.fromList [ NoEq invSym, NoEq pairSym
                            , AC Mult, AC Union ]

-- | The signature for the natural numbers addition function symbols.
natFunSig :: FunSig
natFunSig = S.fromList [ NoEq natOneSym, AC NatPlus ]
