{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
-- |
-- Copyright   : (c) 2010, 2011 Benedikt Schmidt
-- License     : GPL v3 (see LICENSE)
-- 
-- Maintainer  : Benedikt Schmidt <beschmi@gmail.com>
--
-- Pretty printing and parsing of Maude terms and replies.
module Term.Maude.Parser (
  -- * pretty printing of terms for Maude
    ppMaude
  , ppTheory
  , ppTheoryDHsimp

  -- * parsing of Maude replies
  , parseUnifyReply
  , parseMatchReply
  , parseVariantsReply
  , parseReduceReply
  , parseUnifyDHReply
  ) where

import Term.LTerm
import Term.Maude.Types
import Term.Maude.Signature
import Term.Rewriting.Definitions

import Control.Monad.Bind

import Control.Basics

import qualified Data.Set as S

import qualified Data.ByteString as B
import           Data.ByteString (ByteString)
import qualified Data.ByteString.Char8 as BC

import Data.Attoparsec.ByteString.Char8

import Debug.Trace

-- import Extension.Data.Monoid

------------------------------------------------------------------------------
-- Pretty printing of Maude terms.
------------------------------------------------------------------------

-- | Pretty print an 'LSort'.
ppLSort :: LSort -> ByteString
ppLSort s = case s of
    LSortPub       -> "Pub"
    LSortFresh     -> "Fresh"
    LSortMsg       -> "Msg"
    LSortNat       -> "TamNat"
    LSortNode      -> "Node"
    LSortDH         -> "DH"
    LSortG         -> "G"
    LSortE         -> "E"
    LSortNZE       -> "NZE"
    LSortPubG       -> "BG"
    LSortFrNZE     -> "FrNZE"

ppLSortSym :: LSort -> ByteString
ppLSortSym lsort = case lsort of
    LSortFresh     -> "f"
    LSortPub       -> "p"
    LSortMsg       -> "c"
    LSortNode      -> "n"
    LSortNat       -> "t"
    LSortDH         -> "dh"
    LSortG         -> "g"
    LSortE         -> "e"
    LSortNZE       -> "nze"
    LSortPubG       -> "bg"
    LSortFrNZE     -> "fnze"

parseLSortSym :: ByteString -> Maybe LSort
parseLSortSym s = case s of
    "f"  -> Just LSortFresh
    "p"  -> Just LSortPub
    "c"  -> Just LSortMsg
    "n"  -> Just LSortNode
    "t"  -> Just LSortNat
    "dh"  ->  Just LSortDH        
    "g"   -> Just LSortG     
    "e"  ->  Just LSortE        
    "nze"  -> Just LSortNZE   
    "bg"   -> Just  LSortPubG    
    "fnze"  -> Just LSortFrNZE   
    _    -> Nothing

-- | Used to prevent clashes with predefined Maude function symbols
--   like @true@
funSymPrefix :: ByteString
funSymPrefix = "tam"

-- | Encode attributes in additional prefix
funSymEncodeAttr :: Privacy -> Constructability -> ByteString
funSymEncodeAttr priv constr  = f priv <> g constr
    where
        f Private = "P"
        f Public  = "X"
        g Constructor = "C"
        g Destructor = "D"

-- | Decode string @funSymPrefix || funSymEncodeAttr p c || ident@ into
--   @(ident,p,c)@
funSymDecode :: ByteString -> (ByteString, Privacy, Constructability)
funSymDecode s = (ident,priv,constr)
    where
        prefixLen      = BC.length funSymPrefix
        (eAttr,ident)  = BC.splitAt 2 (BC.drop prefixLen s) 
        (priv,constr)  = case eAttr of
                            "PD" -> (Private,Destructor)
                            "PC" -> (Private,Constructor)
                            "XD" -> (Public,Destructor)
                            _    -> (Public,Constructor)

         

-- | Replace underscores "_" with minus "-" for Maude.
replaceUnderscore :: ByteString -> ByteString
replaceUnderscore s = BC.map f s
    where
       f x | x == '_'  = '-'
       f x | otherwise = x

-- | Replace underscores "_" with minus "-" for Maude.
replaceUnderscoreFun :: NoEqSym -> NoEqSym
replaceUnderscoreFun (s, p) = (replaceUnderscore s, p)

replaceUnderscoreFunDH :: DHMultSym -> DHMultSym
replaceUnderscoreFunDH (s, p) = (replaceUnderscore s, p)


-- | Replace minus "-" with underscores "_" when parsing back from Maude.
replaceMinus :: ByteString -> ByteString
replaceMinus s = BC.map f s
    where
       f x | x == '-'  = '_'
       f x | otherwise = x

-- | Replace minus "-" with underscores "_" when parsing back from Maude.
replaceMinusFun :: NoEqSym -> NoEqSym
replaceMinusFun (s, p) = (replaceMinus s, p)

replaceMinusFunDH :: DHMultSym -> DHMultSym
replaceMinusFunDH (s, p) = (replaceMinus s, p)


-- | Pretty print an AC symbol for Maude.
ppMaudeACSym :: ACSym -> ByteString
ppMaudeACSym o =
    funSymPrefix <> case o of
                      Mult    -> multSymString 
                      Union   -> munSymString
                      Xor     -> xorSymString
                      NatPlus -> natPlusSymString

-- | Pretty print a non-AC symbol for Maude.
ppMaudeNoEqSym :: NoEqSym -> ByteString
ppMaudeNoEqSym (o,(_,prv,cnstr))  = funSymPrefix <> funSymEncodeAttr prv cnstr <> replaceUnderscore o

ppMaudeDHMultSym :: DHMultSym -> ByteString
--ppMaudeDHMultSym (o,(_,prv,cnstr))  = replaceUnderscore o
ppMaudeDHMultSym (o,(_,prv,cnstr))  = funSymPrefix <> funSymEncodeAttr prv cnstr <> replaceUnderscore o


-- | Pretty print a C symbol for Maude.
ppMaudeCSym :: CSym -> ByteString
ppMaudeCSym EMap = funSymPrefix <> emapSymString


-- | @ppMaude t@ pretty prints the term @t@ for Maude.
ppMaude :: Term MaudeLit -> ByteString
ppMaude t = case viewTerm t of
    Lit (MaudeVar i lsort)   -> "x" <> ppInt i <> ":" <> ppLSort lsort
    Lit (MaudeConst i lsort) -> ppLSortSym lsort <> "(" <> ppInt i <> ")"
    Lit (FreshVar _ _)       -> error "Term.Maude.Types.ppMaude: FreshVar not allowed"
    FApp (NoEq fsym) []      -> ppMaudeNoEqSym fsym
    FApp (NoEq fsym) as      -> ppMaudeNoEqSym fsym <> ppArgs as
    FApp (DHMult fsym) []      -> ppMaudeDHMultSym fsym
    FApp (DHMult fsym) as      -> ppMaudeDHMultSym fsym <> ppArgs as
    FApp (C fsym) as         -> ppMaudeCSym fsym    <> ppArgs as
    FApp (AC op) as          -> ppMaudeACSym op     <> ppArgs as
    FApp List as             -> "list(" <> ppList as <> ")"
  where
    ppArgs as     = "(" <> (B.intercalate "," (map ppMaude as)) <> ")"
    ppInt         = BC.pack . show
    ppList []     = "nil"
    ppList (x:xs) = "cons(" <> ppMaude x <> "," <> ppList xs <> ")"

------------------------------------------------------------------------------
-- Pretty printing a 'MaudeSig' as a Maude functional module.
------------------------------------------------------------------------------

-- | The term algebra and rewriting rules as a functional module in Maude.
ppTheory :: MaudeSig -> ByteString
ppTheory msig = BC.unlines $
    [ "fmod MSG is"
    , "  protecting NAT ."
    , "  sort Pub Fresh Msg Node TamNat  TOP ." -- DH G E NZE PubG FrNZE 
    , "  subsort Pub < Msg ."
    , "  subsort Fresh < Msg ."
    , "  subsort TamNat < Msg ."
    , "  subsort Msg < TOP ."
    , "  subsort Node < TOP ."
    -- constants
    , "  op f : Nat -> Fresh ."
    , "  op p : Nat -> Pub ."
    , "  op c : Nat -> Msg ."
    , "  op n : Nat -> Node ."
    , "  op t : Nat -> TamNat ."
    -- used for encoding FApp List [t1,..,tk]
    -- list(cons(t1,cons(t2,..,cons(tk,nil)..)))
    , "  op list : TOP -> TOP ."
    , "  op cons : TOP TOP -> TOP ."
    , "  op nil  : -> TOP ." ]
    ++
    (if enableMSet msig
       then
       [ theoryOpAC "mun : Msg Msg -> Msg [comm assoc]" ]
       else [])
    ++
    (if enableDH msig
       then
       [ theoryOpEq "one : -> Msg"
       , theoryOpEq "DH-neutral  : -> Msg"       
       , theoryOpEq "exp : Msg Msg -> Msg"
       , theoryOpAC "mult : Msg Msg -> Msg [comm assoc]"
       , theoryOpEq "inv : Msg -> Msg" ]
       else [])
    ++
    (if enableBP msig
       then
       [ theoryOpEq "pmult : Msg Msg -> Msg"
       , theoryOpC "em : Msg Msg -> Msg [comm]" ]
       else [])
    ++
    (if enableXor msig
       then
       [ theoryOpEq "zero : -> Msg"
       , theoryOpAC "xor : Msg Msg -> Msg [comm assoc]" ]
       else [])
    ++
    (if enableDHMult msig
       then
        [ "sort DH G E NZE BG FrNZE ."
        , "  subsort G < DH ."
        , "  subsort E < DH ."
        , "  subsort NZE < E ."
        , "  subsort FrNZE < NZE ."
        , "  subsort BG < G ."
        , "  subsort DH < TOP ."
        , "  op dh : Nat -> DH ."
        , "  op g : Nat -> G ."
        , "  op e : Nat -> E ."
        , "  op nze : Nat -> NZE ."
        , "  op Bg : Nat -> BG ."
        , "  op fnze : Nat -> FrNZE ."
        , theoryOpDH "dhMult : G G -> G"
        , theoryOpEq "dhGinv : G -> G"
        , theoryOpEq "dhZero : -> E"
        , theoryOpEq "dhMinus : E -> E"
        , theoryOpEq "dhInv : NZE -> NZE"
        , theoryOpEq "dhEg : -> G"
        , theoryOpDH "dhTimes2 : E E -> E"
        , theoryOpDH "dhTimes : NZE NZE -> NZE"
        , theoryOpDH "dhPlus : E E -> E"
        , theoryOpEq "dhExp : G E -> G"
        , theoryOpEq "dhOne : -> E"
        , theoryOpEq "dhMu : G -> E"
        , theoryDH "dhBox : G -> G"
        , theoryDH "dhBoxE : E -> E"
        , "vars A B : G . "
        , "vars X Y Z : E ."
        , "vars U V : NZE ."
        , "eq tamXCdhMult(A, tamXCdhEg(A)) = A ."
        , "eq tamXCdhMult(A, tamXCdhGinv (A)) = tamXCdhEg ."
        , "eq tamXCdhPlus(X , tamXCdhZero) = X ."
        , "eq tamXCdhTimes2(X , tamXCdhOne) = X ."
        , "eq tamXCdhPlus(X , tamXCdhMinus(X)) = tamXCdhZero ."
        , "eq tamXCdhTimes2(X, tamXCdhPlus(Y, Z)) = tamXCdhPlus(tamXCdhTimes2(X, Y), tamXCdhTimes2(X, Z)) ."
        , "eq tamXCdhExp(tamXCdhExp(A, X), Y) = tamXCdhExp(A, tamXCdhTimes2(X, Y)) ."
        , "eq tamXCdhExp(tamXCdhMult(A, B), X) = tamXCdhMult(tamXCdhExp(A, X), tamXCdhExp(B, X)) ."
        , "eq tamXCdhExp(A, tamXCdhOne) = A ."
        , "eq tamXCdhExp(tamXCdhEg, X) = tamXCdhEg ."
        , "eq tamXCdhExp(A, tamXCdhPlus(X, Y)) = tamXCdhMult(tamXCdhExp(A, X), tamXCdhExp(A, Y)) ."
        , "eq tamXCdhTimes(U, V) = tamXCdhTimes2(U, V) ."
        , "eq tamXCdhInv(tamXCdhTimes(U,V)) = tamXCdhTimes(tamXCdhInv(U) , tamXCdhInv(V)) ."
        , "eq tamXCdhTimes(U, tamXCdhInd(U)) = tamXCdhOne ."
        , "eq tamXCdhInv(tamXCdhOne) = tamXCdhOne ."
        , "eq tamXCdhInv(tamXCdhMinus(U)) = tamXCdhMinus(tamXCdhInv(U)) ."
        , "eq tamXCdhInv(tamXCdhInv(U)) = U ."
        , "eq tamXCdhGinv(tamXCdhMult(A, B)) = tamXCdhMult(tamXCdhGinv(A), tamXCdhGinv(B)) ."
        , "eq tamXCdhGinv(tamXCdhGinv(B)) = B . "
        , "eq tamXCdhExp(tamXCdhGinv(A), X) = tamXCdhGinv(tamXCdhExp(A, X)) ."
        , "eq tamXCdhExp(A, tamXCdhZero) = tamXCdhOne ."
        , "eq tamXCdhExp(A, tamXCdhMinus(X) ) = tamXCdhGinv(tamXCdhExp(A, X)) ."
        , "eq tamXCdhGinv (tamXCdhEg) = tamXCdhEg ."
        , "eq tamXCdhMinus(tamXCdhZero) = tamXCdhZero ."
        , "eq tamXCdhMinus (tamXCdhPlus(X,Y)) = tamXCdhPlus((tamXCdhMinus(X)), (tamXCdhMinus(Y))) ."
        , "eq tamXCdhMinus( tamXCdhMinus(X)) = X ."
        , "eq tamXCdhMult(tamXCdhZero, X) = tamXCdhZero ."
        , "eq tamXCdhMult((tamXCdhMinus(X)), Y) = tamXCdhMinus( tamXCdhMult(X, Y)) ."
        ]
       else [])
    ++    
    (if enableNat msig
       then
       [ theoryOpEq "tone : -> TamNat"
       , theoryOpAC "tplus : TamNat TamNat -> TamNat [comm assoc]" ]
       else [])
    ++
    map theoryFunSym (S.toList $ stFunSyms msig)
    ++
    map theoryRule (S.toList $ rrulesForMaudeSig msig)
    ++
    [ "endfm" ]
  where
    maybeEncode (Just (priv,cnstr)) = funSymEncodeAttr priv cnstr
    maybeEncode Nothing             = ""
    theoryOp attr fsort =
        "  op " <> funSymPrefix <> maybeEncode attr <> fsort <>" ."
    --theoryDH fsort = "  op " <> fsort <>" ."
    theoryOpDH fsort =
        "  op " <> funSymPrefix <> maybeEncode (Just (Private,Constructor)) <> fsort <>" [comm assoc] ."
    --theoryDH fsort = "  op " <> fsort <>" ."
    theoryDH = theoryOp (Just (Private,Constructor))
    theoryOpEq = theoryOp (Just (Public,Constructor))
    theoryOpAC = theoryOp Nothing
    theoryOpC  = theoryOp Nothing
    theoryFunSym (s,(ar,priv,cnstr)) =
        theoryOp  (Just(priv,cnstr)) (replaceUnderscore s <> " : " <> (B.concat $ replicate ar "Msg ") <> " -> Msg")
    theoryRule (l `RRule` r) =
        "  eq " <> ppMaude lm <> " = " <> ppMaude rm <> " [variant] ."
      where (lm,rm) = evalBindT ((,) <$>  lTermToMTerm' l <*> lTermToMTerm' r) noBindings
                        `evalFresh` nothingUsed

-- Parser for Maude output
------------------------------------------------------------------------

-- | @parseUnifyReply reply@ takes a @reply@ to a unification query
--   returned by Maude and extracts the unifiers.
parseUnifyReply :: MaudeSig -> ByteString -> Either String [MSubst]
parseUnifyReply msig reply = flip parseOnly reply $
    choice [ string "No unifier." *> endOfLine *> pure []
           , many1 (parseSubstitution msig) ]
        <* endOfInput

-- | @parseMatchReply reply@ takes a @reply@ to a match query
--   returned by Maude and extracts the unifiers.
parseMatchReply :: MaudeSig -> ByteString -> Either String [MSubst]
parseMatchReply msig reply = flip parseOnly reply $
    choice [ string "No match." *> endOfLine *> pure []
           , many1 (parseSubstitution msig) ]
        <* endOfInput

-- | @parseVariantsReply reply@ takes a @reply@ to a variants query
--   returned by Maude and extracts the unifiers.
parseVariantsReply :: MaudeSig -> ByteString -> Either String [MSubst]
parseVariantsReply msig reply = flip parseOnly reply $ do
    endOfLine *> many1 parseVariant <* (string "No more variants.")
    <* endOfLine <* string "rewrites: "
    <* takeWhile1 isDigit <* endOfLine <* endOfInput
  where
    parseVariant = string "Variant " *> optional (char '#') *> takeWhile1 isDigit *> endOfLine *>
                   string "rewrites: " *> takeWhile1 isDigit *> endOfLine *>
                   parseReprintedTerm *> manyTill parseEntry endOfLine
    parseReprintedTerm = choice [ string "TOP" *> pure LSortMsg, parseSort ]
                         *> string ": " *> parseTerm msig <* endOfLine
    parseEntry = (,) <$> (flip (,) <$> (string "x" *> decimal <* string ":") <*> parseSort)
                     <*> (string " --> " *> parseTerm msig <* endOfLine)


parseUnifyDHReply :: MaudeSig -> ByteString -> Either String [MSubst]
parseUnifyDHReply msig reply = flip parseOnly reply $
     endOfLine *> choice [ string "No unifiers." <* endOfLine <* string "rewrites: "
              <* takeWhile1 isDigit <* endOfLine *> pure []
           , many1 (parseUnifier) <* (string "No more unifiers.")
            <* endOfLine <* string "rewrites: "
            <* takeWhile1 isDigit <* endOfLine ] 
      <* endOfInput
              where
                    parseUnifier = string "Unifier " *> optional (char '#') *> takeWhile1 isDigit *> endOfLine *>
                                    string "rewrites: " *> takeWhile1 isDigit *> endOfLine *>
                                    manyTill parseEntry endOfLine
                    parseEntry = (,) <$> (flip (,) <$> (string "x" *> decimal <* string ":") <*> parseSort)
                                    <*> (string " --> " *> parseTerm msig <* endOfLine)


parseUnifyDHReplyY :: MaudeSig -> ByteString -> Either String [MSubst]
parseUnifyDHReplyY msig reply = flip parseOnly reply $ do
            endOfLine *> many1 parseUnifier <* (string "No more unifiers.")
            <* endOfLine <* string "rewrites: "
            <* takeWhile1 isDigit <* endOfLine <* endOfInput
                where
                    parseUnifier = string "Unifier " *> optional (char '#') *> takeWhile1 isDigit *> endOfLine *>
                                    string "rewrites: " *> takeWhile1 isDigit *> endOfLine *>
                                    manyTill parseEntry endOfLine
                    parseEntry = (,) <$> (flip (,) <$> (string "x" *> decimal <* string ":") <*> parseSort)
                                    <*> (string " --> " *> parseTerm msig <* endOfLine)


-- | @parseSubstitution l@ parses a single substitution returned by Maude.
parseSubstitution :: MaudeSig -> Parser MSubst
parseSubstitution msig = do
    endOfLine *> choice [string "Solution ", string "Unifier ", string "Matcher "] *> takeWhile1 isDigit *> endOfLine
    choice [ string "empty substitution" *> endOfLine *> pure []
           , many1 parseEntry]
  where 
    parseEntry = (,) <$> (flip (,) <$> (string "x" *> decimal <* string ":") <*> parseSort)
                     <*> (string " --> " *> parseTerm msig <* endOfLine)

-- | @parseReduceReply l@ parses a single solution returned by Maude.
parseReduceReply :: MaudeSig -> ByteString -> Either String MTerm
parseReduceReply msig reply = flip parseOnly reply $ do
    string "result " *> choice [ string "TOP" *> pure LSortMsg, parseSort ] -- we ignore the sort
        *> string ": " *> parseTerm msig <* endOfLine <* endOfInput

-- | Parse an 'MSort'.
parseSort :: Parser LSort
parseSort =  string "Pub"      *> return LSortPub
         <|> string "Fresh"    *> return LSortFresh
         <|> string "Node"     *> return LSortNode
         <|> string "TamNat"   *> return LSortNat
         <|> string "DH"       *> return LSortDH
         <|> string "G"       *> return LSortG
         <|> string "E"       *> return LSortE
         <|> string "NZE"       *> return LSortNZE
         <|> string "BG"       *> return LSortPubG
         <|> string "FrNZE"       *> return LSortFrNZE
         <|> string "M"        *> -- FIXME: why?
               (    string "sg"  *> return LSortMsg )


-- | @parseTerm@ is a parser for Maude terms.
parseTerm :: MaudeSig -> Parser MTerm
parseTerm msig = choice
   [ string "#" *> (lit <$> (FreshVar <$> (decimal <* string ":") <*> parseSort))
   , string "%" *> (lit <$> (FreshVar <$> (decimal <* string ":") <*> parseSort))
   , do ident <- takeWhile1 (`BC.notElem` (":(,)\n " :: B.ByteString))
        choice [ do _ <- string "("
                    case parseLSortSym ident of
                      Just s  -> parseConst s
                      Nothing -> parseFApp ident
               , string ":" *> parseMaudeVariable ident
               , parseFAppConst ident
               ]
   ]
  where
    consSym = ("cons",(2,Public,Constructor))
    nilSym  = ("nil",(0,Public,Constructor))

    parseFunSym ident args
      | op `elem` allowedfunSyms =  replaceMinusFun op
      | op `elem` allowedfunSymsDH = (replaceMinusFunDH op)
      | otherwise                =
          error $ "Maude.Parser.parseTerm: unknown function "
                  ++ "symbol `"++ show op ++"', not in "
                  ++ show allowedfunSyms
      where 
            special             = ident `elem` ["list", "cons", "nil" ]
            (ident',priv,cnstr) = funSymDecode ident
            op                  = if special then 
                                        (ident , (length args,Public,Constructor))
                                  else  (ident', (length args, priv, cnstr))
            allowedfunSyms = [consSym, nilSym, natOneSym]
                ++ (map replaceUnderscoreFun $ S.toList $ noEqFunSyms msig)
            allowedfunSymsDH = (map replaceUnderscoreFunDH $ S.toList $ dhMultFunSyms msig)

    parseConst s = lit <$> (flip MaudeConst s <$> decimal) <* string ")"

    parseFApp ident =
        appIdent <$> sepBy1 (parseTerm msig) (string ", ") <* string ")"
      where
        appIdent args  | ident == ppMaudeACSym Mult       = fAppAC Mult    args
                       | ident == ppMaudeACSym Union      = fAppAC Union   args
                       | ident == ppMaudeACSym NatPlus    = fAppAC NatPlus args
                       | ident == ppMaudeACSym Xor        = fAppAC Xor   args
                       | ident == ppMaudeCSym  EMap       = fAppC  EMap  args
        appIdent [arg] | ident == "list"                  = fAppList (flattenCons arg)
        --appIdent args  | op `elem` (map replaceUnderscoreFunDH $ S.toList $ dhMultFunSyms msig) = error "you got here "-- fAppDHMult op args
        --  where op = parseFunSym ident args
        appIdent args  | ident `elem` (map ppMaudeDHMultSym $ S.toList $ dhMultFunSyms msig) = fAppDHMult op args
        --appIdent args  | op `elem` (map replaceMinusFunDH (map replaceUnderscoreFunDH $ S.toList $ dhMultFunSyms msig)) = fAppDHMult op args
          where op = parseFunSym ident args
        appIdent args                                     = fAppNoEq op args
          where op = parseFunSym ident args

        flattenCons (viewTerm -> FApp (NoEq s) [x,xs]) | s == consSym = x:flattenCons xs
        flattenCons (viewTerm -> FApp (NoEq s)  [])    | s == nilSym  = []
        flattenCons (viewTerm -> FApp (DHMult s) [x,xs]) | s == consSym = x:flattenCons xs
        flattenCons (viewTerm -> FApp (DHMult s)  [])    | s == nilSym  = []
        flattenCons t                                                 = [t]

    parseFAppConst ident = return $ fAppNoEq (parseFunSym ident []) []

    parseMaudeVariable ident =
        case BC.uncons ident of
            Just ('x', num) -> lit <$> (MaudeVar (read (BC.unpack num)) <$> parseSort)
            _               -> fail "invalid variable"




------------------------------------------------------------------------------
-- simplified DH Maude theory
------------------------------------------------------------------------------

ppTheoryDHsimp ::  ByteString
ppTheoryDHsimp = BC.unlines $
      [ "fmod DHsimp is"
      , "sort DH G E NZE BG FrNZE ."
      , "subsort G < DH ."
      , "subsort E < DH ."
      , "subsort NZE < E ."
      , "subsort FrNZE < NZE ."
      , "subsort BG < G ."
      , "op tamXCdhGinv : G -> G ."
      , "op tamXCdhZero : -> E ."
      , "op tamXCdhInv : NZE -> NZE ."
      , "op tamXCdhEg : -> G ."
      , "op tamXCdhTimes2 : E E -> E ."
      , "op tamXCdhTimes : NZE NZE -> NZE ."
      , "op tamXCdhExp : G E -> G ."
      , "op tamXCdhOne : -> NZE ."
      , "op tamXCdhMu : G -> E ."
      , "op tamPCdhBox : G -> G ." 
      , "op tamPCdhBoxE : E -> E ."
      , "vars A B : G . "
      , "vars X Y : E ."
      , "vars U V W : NZE ."
      , "eq tamXCdhExp(tamXCdhExp(A, X), Y) = tamXCdhExp(A, tamXCdhTimes2(X, Y)) [variant] ."
      , "eq tamXCdhExp(A, tamXCdhOne ) = A [variant] ."
      , "eq tamXCdhExp(tamXCdhEg, X) = tamXCdhEg [variant] ."
      , "eq tamXCdhTimes2(X, tamXCdhOne) = X [variant] ."
      , "eq tamXCdhInv (tamXCdhInv(U) ) = U [variant] ."
      , "eq tamXCdhInv(tamXCdhOne) = tamXCdhOne [variant] ."
      , "eq tamXCdhTimes(U, tamXCdhInv(U)) = tamXCdhOne [variant] ."
      , "eq tamXCdhTimes( tamXCdhInv(U) , tamXCdhInv(V)) = tamXCdhInv( tamXCdhTimes(U, V)) [variant] ."
      , "eq tamXCdhTimes( tamXCdhInv(tamXCdhTimes(U,V)), V) = tamXCdhInv( U) [variant] ."
      , "eq tamXCdhInv( tamXCdhTimes(tamXCdhInv(U),V)) = tamXCdhTimes(U, tamXCdhInv(V)) [variant] ."
      , "eq tamXCdhTimes( U, tamXCdhTimes(tamXCdhInv(U),V)) = V [variant] ."
      , "eq tamXCdhTimes( tamXCdhInv(U), tamXCdhTimes(tamXCdhInv(V),W)) = tamXCdhTimes( tamXCdhInv(tamXCdhTimes(U,V)),W) [variant] ."
      , "eq tamXCdhTimes( tamXCdhInv(tamXCdhTimes(U,V)), tamXCdhTimes(V,W)) = tamXCdhTimes( tamXCdhInv(U),W) [variant] ."
      , "endfm"] 




ppTheoryDHfull ::  ByteString
ppTheoryDHfull = BC.unlines $
      [ "fmod DHsimp is"
      , "sort DH G E NZE BG FrNZE ."
      , "subsort G < DH ."
      , "subsort E < DH ."
      , "subsort NZE < E ."
      , "subsort FrNZE < NZE ."
      , "subsort BG < G ."
      , "op tamXC dhMult : G G -> G [assoc comm] ."
      , "op tamXCdhGinv : G -> G ."
      , "op tamXCdhZero : -> E ."
      , "op tamXCdhMinus : E -> E ."
      , "op tamXCdhInv : NZE -> NZE ."
      , "op tamXCdhEg : -> G ."
      , "op tamXCdhTimes2 : E E -> E [assoc comm] ."
      , "op tamXCdhTimes : NZE NZE -> NZE [assoc comm] ."
      , "op tamXCdhPlus : E E -> E [assoc comm] ."
      , "op tamXCdhExp : G E -> G ."
      , "op tamXCdhOne : -> NZE ."
      , "op tamXCdhMu : G -> E ."
      , "op tamPCdhBox : G -> G ." 
      , "op tamPCdhBoxE : E -> E ."
      , "vars A B : G . "
      , "vars X Y Z : E ."
      , "vars U V : NZE ."
      , "eq tamXCdhMult(A, tamXCdhEg(A)) = A ."
      , "eq tamXCdhMult(A, tamXCdhGinv (A)) = tamXCdhEg ."
      , "eq tamXCdhPlus(X , tamXCdhZero) = X ."
      , "eq tamXCdhTimes2(X , tamXCdhOne) = X ."
      , "eq tamXCdhPlus(X , tamXCdhMinus(- X)) = tamXCdhZero ."
      , "eq tamXCdhTimes2(X, tamXCdhPlus(Y, Z)) = tamXCdhPlus(tamXCdhTimes2(X, Y), tamXCdhTimes2(X, Z)) ."
      , "eq tamXCdhExp(tamXCdhExp(A, X), Y) = tamXCdhExp(A, tamXCdhTimes2(X, Y)) ."
      , "eq tamXCdhExp(tamXCdhMult(A, B), X) = tamXCdhMult(tamXCdhExp(A, X), tamXCdhExp(B, X)) ."
      , "eq tamXCdhExp(A, tamXCdhOne) = A ."
      , "eq tamXCdhExp(tamXCdhEg, X) = tamXCdhEg ."
      , "eq tamXCdhExp(A, tamXCdhPlus(X, Y)) = tamXCdhMult(tamXCdhExp(A, X), tamXCdhExp(A, Y)) ."
      , "eq tamXCdhTimes(U, V) = tamXCdhTimes2(U, V) ."
      , "eq tamXCdhInv(tamXCdhTimes(U,V)) = tamXCdhTimes(tamXCdhInv(U) , tamXCdhInv(V)) ."
      , "eq tamXCdhTimes(U, tamXCdhInd(U)) = tamXCdhOne ."
      , "eq tamXCdhInv(tamXCdhOne) = tamXCdhOne ."
      , "eq tamXCdhInv(tamXCdhMinus(U)) = tamXCdhMinus(tamXCdhInv(U)) ."
      , "eq tamXCdhInv(tamXCdhInv(U)) = U [variant] ."
      , "eq tamXCdhGinv(tamXCdhMult(A, B)) = tamXCdhMult(tamXCdhGinv(A), tamXCdhGinv(B)) ."
      , "eq tamXCdhGinv(tamXCdhGinv(B)) = B . "
      , "eq tamXCdhExp(tamXCdhGinv(A), X) = tamXCdhGinv(tamXCdhExp(A, X)) ."
      , "eq tamXCdhExp(A, tamXCdhZero) = tamXCdhOne ."
      , "eq tamXCdhExp(A, (tamXCdhMinus X)) = tamXCdhGinv(tamXCdhExp(A, X)) ."
      , "eq tamXCdhGinv (tamXCdhEg) = tamXCdhEg ."
      , "eq tamXCdhMinus(tamXCdhZero) = tamXCdhZero ."
      , "eq tamXCdhMinus (tamXCdhPlus(X,Y)) = tamXCdhPlus((tamXCdhMinus(X)), (tamXCdhMinus(Y))) ."
      , "eq tamXCdhMinus (tamXCdhMinus X) = X ."
      , "eq tamXCdhMult(tamXCdhZero, X) = tamXCdhZero ."
      , "eq tamXCdhMult((tamXCdhMinus(X)), Y) = tamXCdhMinus (tamXCdhMult(X, Y)) ."
      , "endfm"] 

      --todo: remove [variant].