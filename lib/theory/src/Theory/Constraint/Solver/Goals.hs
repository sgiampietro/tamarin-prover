{-# LANGUAGE TupleSections    #-}
{-# LANGUAGE ViewPatterns     #-}
{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use if" #-}
-- |
-- Copyright   : (c) 2010-2012 Benedikt Schmidt & Simon Meier
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Simon Meier <iridcode@gmail.com>
-- Portability : GHC only
--
-- The constraint reduction rules, which are not enforced as invariants in
-- "Theory.Constraint.Solver.Reduction".
--
-- A goal represents a possible application of a rule that may result in
-- multiple cases or even non-termination (if applied repeatedly). These goals
-- are computed as the list of 'openGoals'. See
-- "Theory.Constraint.Solver.ProofMethod" for the public interface to solving
-- goals and the implementation of heuristics.
module Theory.Constraint.Solver.Goals (

  openGoals
  , solveGoal
  , plainOpenGoals
  ) where

import           Debug.Trace

import           Prelude                                 hiding (id, (.))

import qualified Data.ByteString.Char8                   as BC
import qualified Data.DAG.Simple                         as D (reachableSet)
-- import           Data.Foldable                           (foldMap)
import qualified Data.Map                                as M
import qualified Data.Monoid                             as Mono
import qualified Data.Set                                as S

import           Control.Basics
import           Control.Category
import           Control.Monad.Disj
import           Control.Monad.State                     (gets)
import           Control.Monad.Trans.State.Lazy          hiding (get,gets)
import           Control.Monad.Trans.FastFresh           -- GHC7.10 needs: hiding (get,gets)
import           Control.Monad.Trans.Reader              -- GHC7.10 needs: hiding (get,gets)

import           Extension.Data.Label                    as L

import           Theory.Constraint.Solver.AnnotatedGoals
import           Theory.Constraint.Solver.Contradictions (substCreatesNonNormalTerms)
import           Theory.Constraint.Solver.Reduction
import           Theory.Constraint.System
import           Theory.Tools.IntruderRules (mkDUnionRule, isDExpRule, isDPMultRule, isDEMapRule)
import           Theory.Model
import           Term.Builtin.Convenience
import           Term.DHMultiplication
import           Theory.Constraint.Solver.Combination

import           Utils.Misc                              (twoPartitions)

------------------------------------------------------------------------------
-- Extracting Goals
------------------------------------------------------------------------------

-- Usefullness and AnnotatedGoal moved to AnnotatedGoals.hs to allow exportation


-- Instances
------------

-- | The list of goals that must be solved before a solution can be extracted.
-- Each goal is annotated with its age and an indicator for its usefulness.
openGoals :: System -> [AnnotatedGoal]
openGoals sys = do
    (goal, status) <- M.toList $ get sGoals sys
    let solved = get gsSolved status
    -- check whether the goal is still open
    guard $ case goal of
        ActionG i (kFactView -> Just (UpK, m)) ->
          if get sDiffSystem sys
             -- In a diff proof, all action goals need to be solved.
             then not (solved)
             else
               not $    solved
                    -- message variables are not solved, except if the node already exists in the system -> facilitates finding contradictions
                    || (isMsgVar m && Nothing == M.lookup i (get sNodes sys))
                    || sortOfLNTerm m == LSortPub
                    || sortOfLNTerm m == LSortNat
                    -- handled by 'insertAction'
                    || isPair m || isInverse m || isProduct m --- || isXor m
                    || isUnion m || isNullaryPublicFunction m
        ActionG _ _                               -> not solved
        PremiseG _ _                              -> not solved
        -- Technically the 'False' disj would be a solvable goal. However, we
        -- have a separate proof method for this, i.e., contradictions.
        DisjG (Disj [])                           -> False
        DisjG _                                   -> not solved

        ChainG c p     ->
          case kFactView (nodeConcFact c sys) of
              Just (DnK, viewTerm2 -> FUnion args) ->
              -- do not solve Union conclusions if they contain only known msg vars
                  not solved && not (allMsgVarsKnownEarlier c args)
              -- open chains for msg vars are only solved if N5'' is applicable
              Just (DnK,  m) | isMsgVar m          -> (not solved) &&
                                                      (chainToEquality m c p)
                             | otherwise           -> not solved
              fa -> error $ "openChainGoals: impossible fact: " ++ show fa

        -- FIXME: Split goals may be duplicated, we always have to check
        -- explicitly if they still exist.
        SplitG idx -> splitExists (get sEqStore sys) idx
        SubtermG st -> st `elem` L.get (posSubterms . sSubtermStore) sys
        DHIndG _ _ _ -> not solved
        NoCancG _ -> not solved
        NeededG _ _ -> not solved
        IndicatorG _ -> not solved
        IndicatorGExp _ -> not solved

    let
        useful = case goal of
          _ | get gsLoopBreaker status              -> LoopBreaker
          ActionG i (kFactView -> Just (UpK, m))
              -- if there are KU-guards then all knowledge goals are useful
            | hasKUGuards             -> Useful
            | currentlyDeducible i m  -> CurrentlyDeducible
            | probablyConstructible m -> ProbablyConstructible
          _                           -> Useful

    return (goal, (get gsNr status, useful))
  where
    existingDeps = rawLessRel sys
    hasKUGuards  =
        any ((KUFact `elem`) . guardFactTags) $ S.toList $ get sFormulas sys

    checkTermLits :: (LSort -> Bool) -> LNTerm -> Bool
    checkTermLits p =
        Mono.getAll . foldMap (Mono.All . p . sortOfLit)

    -- KU goals of messages that are likely to be constructible by the
    -- adversary. These are terms that do not contain a fresh name or a fresh
    -- name variable. For protocols without loops they are very likely to be
    -- constructible. For protocols with loops, such terms have to be given
    -- similar priority as loop-breakers.
    probablyConstructible  m = checkTermLits (LSortFresh /=) m
                               && not (containsPrivate m)

    -- KU goals of messages that are currently deducible. Either because they
    -- are composed of public names only and do not contain private function
    -- symbols or because they can be extracted from a sent message using
    -- unpairing or inversion only.
    currentlyDeducible i m = (checkTermLits (`elem` [LSortPub, LSortNat]) m
                              && not (containsPrivate m))
                          || extractible i m

    extractible i m = or $ do
        (j, ru) <- M.toList $ get sNodes sys
        -- We cannot deduce a message from a last node.
        guard (not $ isLast sys j)
        let derivedMsgs = concatMap toplevelTerms $
                [ t | Fact OutFact _ [t] <- get rConcs ru] <|>
                [ t | Just (DnK, t)    <- kFactView <$> get rConcs ru]
        -- m is deducible from j without an immediate contradiction
        -- if it is a derived message of 'ru' and the dependency does
        -- not make the graph cyclic.
        return $ m `elem` derivedMsgs &&
                 not (j `S.member` D.reachableSet [i] existingDeps)

    toplevelTerms t@(viewTerm2 -> FPair t1 t2) =
        t : toplevelTerms t1 ++ toplevelTerms t2
    toplevelTerms t@(viewTerm2 -> FInv t1) = t : toplevelTerms t1
    toplevelTerms t = [t]

    allMsgVarsKnownEarlier (i,_) args = (all isMsgVar args) &&
        (all (`elem` earlierMsgVars) args)
      where earlierMsgVars = do (j, _, t) <- allKUActions sys
                                guard $ isMsgVar t && alwaysBefore sys j i
                                return t

    -- check whether we have a chain that fits N5'' (an open chain between an
    -- equality rule and a simple msg var conclusion that exists as a K up
    -- previously) which needs to be resolved even if it is an open chain
    chainToEquality :: LNTerm -> NodeConc -> NodePrem -> Bool
    chainToEquality t_start conc p = is_msg_var && is_equality && ku_before
        where
            -- check whether it is a msg var
            is_msg_var  = isMsgVar t_start
            -- and whether we do have an equality rule instance at the end
            is_equality = isIEqualityRule $ nodeRule (fst p) sys
            -- get all KU-facts with the same msg var
            ku_start    = filter (\x -> (fst x) == t_start) $
                              map (\(i, _, m) -> (m, i)) $ allKUActions sys
            -- and check whether any of them happens before the KD-conclusion
            ku_before   = any (\(_, x) -> alwaysBefore sys x (fst conc)) ku_start


-- | The list of all open goals left together with their status.
plainOpenGoals:: System -> [(Goal, GoalStatus)]
plainOpenGoals sys = openGoalsLeft
  where
    openGoalsLeft = filter isOpen (M.toList $ L.get sGoals sys)
    isOpen(_, status) = case status of
      GoalStatus s _ _ -> not s

------------------------------------------------------------------------------
-- Solving 'Goal's
------------------------------------------------------------------------------

-- | @solveGoal rules goal@ enumerates all possible cases of how this goal
-- could be solved in the context of the given @rules@. For each case, a
-- sensible case-name is returned.
solveGoal :: Goal -> Reduction String
solveGoal goal = do
    -- mark before solving, as representation might change due to unification
    markGoalAsSolved "directly" goal
    rules <- askM pcRules
    case goal of
      ActionG i fa  -> solveAction  (nonSilentRules rules) (i, fa)
      PremiseG p fa ->
           solvePremise (get crProtocol rules ++ get crConstruct rules) p fa
      ChainG c p    -> solveChain (get crDestruct  rules) (c, p)
      SplitG i      -> solveSplit i
      DisjG disj    -> solveDisjunction disj
      SubtermG st   -> solveSubterm st
      DHIndG p fa t -> solveDHInd (get crProtocol rules) p fa t
      NoCancG (t1, t2) -> solveNoCanc t1 t2
      NeededG x i    -> solveNeeded (get crProtocol rules) x i
      IndicatorG (t1, t2) -> solveIndicator t1 t2
      IndicatorGExp (t1, t2) -> solveIndicatorE t1 t2

-- The following functions are internal to 'solveGoal'. Use them with great
-- care.


--solveProtoAction :: RuleACInst ->  Reduction RuleACInst 
--solveProtoAction ru = return ru

-- | CR-rule *S_at*: solve an action goal.
solveAction :: [RuleAC]          -- ^ All rules labelled with an action
            -> (NodeId, LNFact)  -- ^ The action we are looking for.
            -> Reduction String  -- ^ A sensible case name.
solveAction rules (i, fa@(Fact _ ann _)) =trace (show ("SEARCHING", fa, "END")) ( do
    mayRu <- M.lookup i <$> getM sNodes
    showRuleCaseName <$> case mayRu of
        Nothing -> case fa of
            (Fact KUFact _ [m@(viewTerm2 -> FXor ts)]) -> do
                   partitions <- disjunctionOfList $ twoPartitions ts
                   case partitions of
                       (_, []) -> do
                            let ru = Rule (IntrInfo CoerceRule) [kdFact m] [fa] [fa] []
                            modM sNodes (M.insert i ru)
                            insertGoal (PremiseG (i, PremIdx 0) (kdFact m)) False
                            return ru
                       (a',  b') -> do
                            let a = fAppAC Xor a'
                            let b = fAppAC Xor b'
                            let ru = Rule (IntrInfo (ConstrRule $ BC.pack "_xor")) [(kuFact a),(kuFact b)] [fa] [fa] []
                            modM sNodes (M.insert i ru)
                            mapM_ requiresKU [a, b] *> return ru
            --(Fact (ProtoFact n s i) _ [m@(viewTerm3 -> Box ts)]) -> solveProto
            --(Fact (ProtoFact n s i) _ [m@(viewTerm3 -> BoxE ts)]) -> solveProto
            --(Fact _ _ [m@(viewTerm3 -> Box ts)]) -> solveKUAction
            --(Fact _ _ [m@(viewTerm3 -> BoxE ts)]) -> solveKUAction
            _                                        -> do
                   ru  <- labelNodeId i (annotatePrems <$> rules) Nothing
                   act <- disjunctionOfList $ get rActs ru
                   (void (solveFactEqs SplitNow [Equal fa act]))
                   return ru

        Just ru ->  case fa of
            --(Fact (ProtoFact n s i) _ [m@(viewTerm3 -> Box ts)]) -> solveProtoAction ru
            --(Fact (ProtoFact n s i) _ [m@(viewTerm3 -> BoxE ts)]) -> solveProtoAction ru
            --(Fact _ _ [m@(viewTerm3 -> Box ts)]) -> solveKU ru
            --(Fact _ _ [m@(viewTerm3 -> BoxE ts)]) -> solveKU ru
            _                                     -> do unless (fa `elem` get rActs ru) $ do
                                                          act <- disjunctionOfList $ get rActs ru
                                                          (void (solveFactEqs SplitNow [Equal fa act]))
                                                        return ru)
  where
    -- If the fact in the action goal has annotations, then consider annotated
    -- versions of intruder rules (this allows high or low priority intruder knowledge
    -- goals to propagate to intruder knowledge of subterms)
    annotatePrems ru@(Rule ri ps cs as nvs) =
        if not (S.null ann) && isIntruderRule ru then
            Rule ri (annotateFact ann <$> ps) cs (annotateFact ann <$> as) nvs
            else ru
    requiresKU t = do
        j <- freshLVar "vk" LSortNode
        let faKU = kuFact t
        insertLess j i Adversary
        void (insertAction j faKU)
    {-solveKUAction = do
                   ru  <- labelNodeId i (annotatePrems <$> rules) Nothing
                   act <- disjunctionOfList $ get rActs ru
                   (void (solveActionFactDHEqs SplitNow (Equal fa act) ru)) 
                   return ru
    solveKU ruk =  do unless (fa `elem` get rActs ruk) $ do
                            act <- disjunctionOfList $ get rActs ruk
                            (void (solveActionFactDHEqs SplitNow (Equal fa act) ruk)) 
                      return ruk
    solveProto = do
                   ru  <- labelNodeId i (annotatePrems <$> rules) Nothing
                   act <- disjunctionOfList $ get rActs ru
                   solveProtoAction ru -}

-- | CR-rules *DG_{2,P}* and *DG_{2,d}*: solve a premise with a direct edge
-- from a unifying conclusion or using a destruction chain.
--
-- Note that *In*, *Fr*, and *KU* facts are solved directly when adding a
-- 'ruleNode'.
--
solvePremise :: [RuleAC]       -- ^ All rules with a non-K-fact conclusion.
             -> NodePrem       -- ^ Premise to solve.
             -> LNFact         -- ^ Fact required at this premise.
             -> Reduction String -- ^ Case name to use.
solvePremise rules p faPrem
  | isKdhFact faPrem = do
      case factTerms faPrem of
          [t1] -> trace (show ("HERE: solving", t1) ) (solveDHInd rules p faPrem t1)
          _ -> error "malformed KdhFact"
  | isKDFact faPrem = do
      iLearn    <- freshLVar "vl" LSortNode
      mLearn    <- varTerm <$> freshLVar "t" LSortMsg -- why do we not care about the term here??
      let concLearn = kdFact mLearn
          premLearn = outFact mLearn
          -- !! Make sure that you construct the correct rule!
          ruLearn = Rule (IntrInfo IRecvRule) [premLearn] [concLearn] [] []
          cLearn = (iLearn, ConcIdx 0)
          pLearn = (iLearn, PremIdx 0)
      modM sNodes  (M.insert iLearn ruLearn)
      insertChain cLearn p
      solvePremise rules pLearn premLearn
{-
  | isOutFact fa Prem = do
      case factTerms faPrem of 
        t@(viewTerm2 -> FdhBox _) ->  (ru, c, faConc) <- trace (show ("gotHERE2", sortOfLNTerm (runReader (rootIndKnownMaude bset nbset x) hnd))) (insertFreshNodeConcOut rules) 
                                      (insertDHEdge (c, faConc, faPrem, p) (runReader (rootIndKnownMaude bset nbset x) hnd)) t 
                              (return $ showRuleCaseName ru) -- (return "done") 
-}
  | otherwise = do
      (ru, c, faConc) <- insertFreshNodeConc rules
      insertEdges [(c, faConc, faPrem, p)]
      return $ showRuleCaseName ru

-- | CR-rule *DG2_chain*: solve a chain constraint.
solveChain :: [RuleAC]              -- ^ All destruction rules.
           -> (NodeConc, NodePrem)  -- ^ The chain to extend by one step.
           -> Reduction String      -- ^ Case name to use.
solveChain rules (c, p) = do
    faConc  <- gets $ nodeConcFact c
    do -- solve it by a direct edge
        cRule <- gets $ nodeRule (nodeConcNode c)
        pRule <- gets $ nodeRule (nodePremNode p)
        faPrem <- gets $ nodePremFact p
        contradictoryIf (forbiddenEdge cRule pRule)
        insertEdges [(c, faConc, faPrem, p)]
        let mPrem = case kFactView faConc of
                      Just (DnK, m') -> m'
                      _              -> error "solveChain: impossible"
            caseName (viewTerm -> FApp o _)    = showFunSymName o
            caseName (viewTerm -> Lit l)       = showLitName l
        contradictoryIf (illegalCoerce pRule mPrem)
        return (caseName mPrem)
     `disjunction`
     -- extend it with one step
     case kFactView faConc of
         Just (DnK, viewTerm2 -> FUnion args) ->
             do -- If the chain starts at a union message, we
                -- compute the applicable destruction rules directly.
                i <- freshLVar "vr" LSortNode
                let rus = map (ruleACIntrToRuleACInst . mkDUnionRule args)
                              args
                -- NOTE: We rely on the check that the chain is open here.
                ru <- disjunctionOfList rus
                modM sNodes (M.insert i ru)
                -- FIXME: Do we have to add the PremiseG here so it
                -- marked as solved?
                let v = PremIdx 0
                faPrem <- gets $ nodePremFact (i,v)
                extendAndMark i ru v faPrem faConc
         Just (DnK, m) ->
             do -- If the chain does not start at a union message,
                -- the usual *DG2_chain* extension is perfomed.
                -- But we ignore open chains, as we only resolve
                -- open chains with a direct chain
                contradictoryIf (isMsgVar m)
                cRule <- gets $ nodeRule (nodeConcNode c)
                (i, ru) <- insertFreshNode rules (Just cRule)
                contradictoryIf (forbiddenEdge cRule ru)
                -- This requires a modified chain constraint def:
                -- path via first destruction premise of rule ...
                (v, faPrem) <- disjunctionOfList $ take 1 $ enumPrems ru
                extendAndMark i ru v faPrem faConc
         _ -> error "solveChain: not a down fact"
  where
    extendAndMark :: NodeId -> RuleACInst -> PremIdx -> LNFact -> LNFact
      -> Control.Monad.Trans.State.Lazy.StateT System
      (Control.Monad.Trans.FastFresh.FreshT
      (DisjT (Control.Monad.Trans.Reader.Reader ProofContext))) String
    extendAndMark i ru v faPrem faConc = do
        insertEdges [(c, faConc, faPrem, (i, v))]
        markGoalAsSolved "directly" (PremiseG (i, v) faPrem)
        insertChain (i, ConcIdx 0) p
        return (showRuleCaseName ru)

    -- contradicts normal form condition:
    -- no edge from dexp to dexp KD premise, no edge from dpmult
    -- to dpmult KD premise, and no edge from dpmult to demap KD premise
    -- (this condition replaces the exp/noexp tags)
    -- no more than the allowed consecutive rule applications
    forbiddenEdge :: RuleACInst -> RuleACInst -> Bool
    forbiddenEdge cRule pRule = isDExpRule   cRule && isDExpRule  pRule  ||
                                isDPMultRule cRule && isDPMultRule pRule ||
                                isDPMultRule cRule && isDEMapRule  pRule ||
                                (getRuleName cRule == getRuleName pRule)
                                    && (getRemainingRuleApplications cRule == 1)

    -- Contradicts normal form condition N2:
    -- No coerce of a pair of inverse.
    illegalCoerce pRule mPrem = isCoerceRule pRule && isPair    mPrem ||
                                isCoerceRule pRule && isInverse mPrem ||
      -- Also: Coercing of products is unnecessary, since the protocol is *-restricted.
                                isCoerceRule pRule && isProduct mPrem


-- | Solve an equation split. There is no corresponding CR-rule in the rule
-- system on paper because there we eagerly split over all variants of a rule.
-- In practice, this is too expensive and we therefore use the equation store
-- to delay these splits.
solveSplit :: SplitId -> Reduction String
solveSplit x = do
    split <- gets ((`performSplit` x) . get sEqStore)
    let errMsg = error "solveSplit: inexistent split-id"
    store      <- maybe errMsg disjunctionOfList split
    -- FIXME: Simplify this interaction with the equation store
    hnd        <- getMaudeHandle
    substCheck <- gets (substCreatesNonNormalTerms hnd)
    store'     <- simp hnd substCheck store
    contradictoryIf (eqsIsFalse store')
    sEqStore =: store'
    return "split"

-- | CR-rule *S_disj*: solve a disjunction of guarded formulas using a case
-- distinction.
--
-- In contrast to the paper, we use n-ary disjunctions and also split over all
-- of them at once.
solveDisjunction :: Disj LNGuarded -> Reduction String
solveDisjunction disj = do
    (i, gfm) <- disjunctionOfList $ zip [(1::Int)..] $ getDisj disj
    insertFormula gfm
    return $ "case_" ++ show i


-- todo: define a "isNoCanc" function!! Probably in the DHMultiplication file in the term folder. 
solveNoCanc :: LNTerm -> LNTerm -> Reduction String
solveNoCanc x y = do
    nocancs <- getM sNoCanc
    if ( S.member (x,y) nocancs)
      then  (do
        --markGoalAsSolved "directly" (NoCancG (x, y))
        return "NoCancsolved")
      else (
        if (isNoCanc x y) then (do
          --markGoalAsSolved "directly" (NoCancG (x, y))
          return "NoCancsolved" )
        else error "NoCanc does not hold"  -- TODO: not sure what to do if you don't have this condition? maybe add y and inv(x) to the DH-equation store? 
      )


solveDHIndaux :: S.Set LNTerm -> S.Set LNTerm -> LNTerm -> MaudeHandle -> NodePrem -> LNFact -> LNTerm -> [RuleAC] -> StateT System (FreshT (DisjT (Reader ProofContext))) String
solveDHIndaux bset nbset x hnd p faPrem t rules =
  case neededexponents bset nbset x of
      (Just es) -> do
          trace (show ("NEEDEDEXPO", es)) insertNeededList (S.toList es) p faPrem t
          return "NeededInserted"
      -- the current goal solveDHInd should remain and we should try to solve it again once we
      -- have solved the Needed goals. or do we try it with a variable?
      Nothing -> case viewTerm2 (runReader (rootIndKnownMaude bset nbset x) hnd) of
          (DHOne) -> trace (show ("GotHERE")) return "attack"
          (DHEg) -> trace (show ("GotHERE")) return "attack"
          (Lit2 t) | (isPubGVar (LIT t))  -> trace (show ("GotHERE")) return "attack"
          _ -> do
            (ru, c, faConc) <- trace (show ("gotHERE2", sortOfLNTerm (runReader (rootIndKnownMaude bset nbset x) hnd))) (insertFreshNodeConcOut rules)
            z1 <- freshLVar "Z1" LSortE
            let indt = (runReader (rootIndKnownMaude bset nbset x) hnd)
                indtexp = fAppdhExp (indt, LIT (Var z1) )
            (insertDHEdge False (c, faConc, faPrem, p) indtexp) t -- instead of root indicator this should be Y.ind^Z.
            (return $ showRuleCaseName ru) -- (return "done") 

solveDHInd ::  [RuleAC]        -- ^ All rules that have an Out fact containing a boxed term as conclusion. 
             -> NodePrem       -- ^ Premise to solve.
             ->LNFact
             -> LNTerm       -- ^ Product term of which we have to find the indicator  
             -> Reduction String -- ^ Case name to use.
solveDHInd rules p faPrem t =  do-- TODO: does this ensure that x is actually a root term?
    case prodTerms t of
      Just (x,y) -> do
        hnd  <- getMaudeHandle
        bset <- getM sBasis
        nbset <- getM sNotBasis
        nocancs <- getM sNoCanc
        -- trace (show ("NOCANC", x, y, bset, nbset)) insertNoCanc x y
        if not (S.member (x,y) nocancs  || isNoCanc x y) then
              (do
              insertNoCanc x y
              solveDHIndaux bset nbset x hnd p faPrem t rules)
             else (solveDHIndaux bset nbset x hnd p faPrem t rules)
          {-Nothing -> case (rootIndKnown bset nbset x) of
              --(FAPP dhEgSym []) -> trace (show ("GotHERE")) return "attack" 
              --(FAPP dhOneSym []) -> trace (show ("GotHERE")) return "attack" 
              indterm -> do
                (ru, c, faConc) <- trace (show ("gotHERE2", sortOfLNTerm indterm, indterm)) (insertFreshNodeConcOut rules) 
                (insertDHEdge (c, faConc, faPrem, p) (runReader (rootIndKnownMaude bset nbset x) hnd)) t 
                (return $ showRuleCaseName ru) -- (return "done") -}
      Nothing -> error "error in prodTerm function"


solveIndicator :: LNTerm -> LNTerm -> Reduction String
solveIndicator t1 t2  = do 
  nbset <- getM sNotBasis
  case (solveIndicators (S.toList nbset) terms t2) of 
   Just vec -> do
      markGoalAsSolved ("Found indicators! possible attack by result:" ++ show (vec, terms)) (IndicatorG (t1,t2))
      return ("Found indicators! possible attack by result:" ++ show (vec, terms))
   Nothing -> do 
      markGoalAsSolved ("Safe,cannot combine") (IndicatorG (t1,t2) )
      return "Safe,cannot combine"
  where 
    terms = [t1]

solveIndicatorE :: LNTerm -> LNTerm -> Reduction String
solveIndicatorE t1 t2 = do 
  case (solveIndicators ([]) terms t2) of 
   Just vec ->  do 
        markGoalAsSolved ("Found exponent with:" ++ show (vec, terms)) (IndicatorGExp (t1, t2))
        return "Exponent found"
   Nothing -> return "Contradiction! Cannot find exponent"
  where 
    terms = [t1]
        
  

--how do I make a case distinction _within_ a solve function?? use disjunction monad!

solveNeeded ::  [RuleAC] -> LNTerm ->  NodeId ->        -- exponent that is needed.
                Reduction String -- ^ Case name to use.
solveNeeded rules x i = do
    -- markGoalAsSolved "case split: basis or not" (NeededG x i )
    basisornot <- disjunctionOfList [True, False] -- this should return a list of True and False
    case basisornot of
      True -> do
                insertBasisElem x
                --insertGoal (PremiseG (i, PremIdx 0) (kdFact x)) False !!(adversary shouldn't know x? check if we actually _need_ to prove it CANNOT)
                -- TODO: insertSecret x
                return "caseBasis"
      False -> do
                trace "IAMHEREYES" (insertNotBasisElem x)
                --                
                (ru, c, faConc) <- insertFreshNodeConcOut rules
                z1 <- freshLVar "Z1" LSortE
                let indx = fAppdhTimesE (x, LIT (Var z1) )
                trace (show ("WORKING", indx, x)) (insertDHEdge True (c, faConc, kdhFact x,(i, PremIdx 0)) indx x)  --TODO: this should not be x, but x*Z1+Z2 (with adversary knowing Z1 and Z2). 
                -- return $ showRuleCaseName ru
                --
                --insertGoal (PremiseG (i, PremIdx 0) (kIFact x)) False 
                return "caseNotBasis" -- TODO: make this appear somehow, maybe with an extra case. 



-- | remove from subterms
-- get split
-- behave according to split
--   insert subterms
--   insert equalities
--   insert eqFormulas
--   ignore TrueD
--   contradict if emptyset
solveSubterm :: (LNTerm, LNTerm) -> Reduction String
solveSubterm st = do
      -- mark subterm as solved
      modM (posSubterms . sSubtermStore) (st `S.delete`)
      modM (solvedSubterms . sSubtermStore) (st `S.insert`)

      -- find all splits
      reducible <- reducibleFunSyms . mhMaudeSig <$> getMaudeHandle
      splitList <- splitSubterm reducible True st
      (i, split) <- disjunctionOfList $ zip [(1::Int)..] splitList  -- make disjunction over all splits

      -- from here on: only look at a single split
      case split of
        TrueD -> return ()
        SubtermD st1 -> modM sSubtermStore (addSubterm st1)
        NatSubtermD st1@(s,t) -> if length splitList == 1
                                    then do
                                      newVar <- freshLVar "newVar" LSortNat
                                      let sPlus = s ++: varTerm newVar
                                      insertFormula $ closeGuarded Ex [newVar] [EqE sPlus t] gtrue
                                    else modM sSubtermStore (addSubterm st1)
        EqualD (l, r) -> insertFormula $ GAto $ EqE (lTermToBTerm l) (lTermToBTerm r)
        ACNewVarD ((smallPlus, big), newVar) -> insertFormula $ closeGuarded Ex [newVar] [EqE smallPlus big] gtrue

      return $ "SubtermSplit" ++ show i
