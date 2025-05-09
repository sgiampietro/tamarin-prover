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

import           Debug.Trace -- .Ignore

import           Prelude                                 hiding (id, (.))

import qualified Data.ByteString.Char8                   as BC
import qualified Data.DAG.Simple                         as D (reachableSet)
-- import           Data.Foldable                           (foldMap)
import qualified Data.Map                                as M
import qualified Data.Monoid                             as Mono
import qualified Data.Set                                as S
import           Data.List                               (nub)

import           Control.Basics
import           Control.Category
import           Control.Monad.Disj
import           Control.Monad.Bind
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
import           Theory.Tools.DHActionFacts
import           Theory.Tools.EquationStore
import           Theory.Model
import           Term.Builtin.Convenience
import           Term.DHMultiplication
import           Term.Rewriting.Norm
import           Theory.Constraint.Solver.Combination

import           Utils.Misc                              (twoPartitions)
-- import Theory.Constraint.Solver.Simplify (simplifySystem)




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
        DHEqG _ _                               -> not solved
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
              fa -> error $ "openChainGoals: impossible fact: " ++ show fa ++ (show $ nodeConcFact c sys)

        -- FIXME: Split goals may be duplicated, we always have to check
        -- explicitly if they still exist.
        SplitG idx -> splitExists (get sEqStore sys) idx
        SubtermG st -> st `elem` L.get (posSubterms . sSubtermStore) sys

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
      ActionG i fa  -> trace (show ("solvingactiongoal", fa)) $ solveAction  (nonSilentRules rules) (i, fa)
      DHEqG t1 t2 -> solveDHEq t1 t2
      PremiseG p fa ->
           solvePremise (get crProtocol rules ++ get crConstruct rules) p fa
      ChainG c p    -> trace (show ("solvingchaingfoal")) $ solveChain (get crDestruct rules) (c, p)
      SplitG i      -> solveSplit i
      DisjG disj    -> solveDisjunction disj
      SubtermG st   -> solveSubterm st
      NoCancG (t1, t2) -> solveNoCanc t1 t2

-- The following functions are internal to 'solveGoal'. Use them with great
-- care.


-- | CR-rule *S_at*: solve an action goal.
solveAction :: [RuleAC]          -- ^ All rules labelled with an action
            -> (NodeId, LNFact)  -- ^ The action we are looking for.
            -> Reduction String  -- ^ A sensible case name.
solveAction rules (i, fa@(Fact _ ann _)) = do
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
            -- Distinguish DH term cases!!
            (Fact KUFact _ [m]) | (isMixedFact fa) -> do
                   ru  <- labelNodeId i (annotatePrems <$> rules) Nothing -- TODO:probably want to also check existing rules
                   act <- disjunctionOfList (get rActs ru)
                   (void (solveFactEqs SplitNow [Equal fa act]))
                   void substSystem
                   return ru
            _ | (isKdhFact fa)                     -> do
                   nbset <- getM sNotBasis 
                   case factTerms fa of 
                    [y] | isDHLit y ->   do
                                            ru  <- labelNodeId i (annotatePrems <$> rules) Nothing -- TODO:probably want to also check existing rules
                                            act <- disjunctionOfList (filter isDHFact $ get rActs ru)
                                            (void (solveFactDHEqs SplitNow fa act (S.fromList $ basisOfRule ru) (S.fromList $ notBasisOfRule ru) (protoCase SplitNow (S.fromList $ basisOfRule ru) (S.fromList $ notBasisOfRule ru))))
                                            void substSystem
                                            return ru 
                    [y] | otherwise ->        do
                           case viewTerm2 y of
                            FdhMu t1  -> do
                                let premLearn = kdhFact t1
                                    concLearn = inFact t1
                                    ruLearn = Rule (IntrInfo ISendRule) [premLearn] [concLearn] [] []
                                    cLearn = (i, ConcIdx 0)
                                    pLearn = (i, PremIdx 0)
                                modM sNodes  (M.insert i ruLearn)
                                solvePremise rules pLearn premLearn
                                return ruLearn 
                            _   -> do
                                let premLearn = fa
                                    concLearn = inFact y
                                    ruLearn = Rule (IntrInfo ISendRule) [premLearn] [concLearn] [] []
                                    cLearn = (i, ConcIdx 0)
                                    pLearn = (i, PremIdx 0)
                                modM sNodes (M.insert i ruLearn)
                                solvePremise rules pLearn premLearn
                                return ruLearn 
            _ | (isDHFact fa)                       -> do
                   ru  <- trace (show ("solvingactionhere", fa)) $ labelNodeId i (annotatePrems <$> rules) Nothing 
                   act <- disjunctionOfList (filter isDHFact $ get rActs ru)
                   (void (solveFactDHEqs SplitNow fa act (S.fromList $ basisOfRule ru) (S.fromList $ notBasisOfRule ru) (protoCase SplitNow (S.fromList $ basisOfRule ru) (S.fromList $ notBasisOfRule ru))))
                   void substSystem
                   --void normSystem
                   return ru 
            _ | (isMixedFact fa)                       -> do
                   ru  <- labelNodeId i (annotatePrems <$> rules) Nothing
                   act <- disjunctionOfList (filter isMixedFact $ get rActs ru)
                   let bset = (S.fromList $ basisOfRule ru)
                       nbset = (S.fromList $ notBasisOfRule ru) 
                   (void (solveMixedFactEqs SplitNow (Equal fa act) bset nbset (protoCase SplitNow bset nbset)))
                   void substSystem
                   --void normSystem
                   return ru
            _                                        -> do
                   ru  <- labelNodeId i (annotatePrems <$> rules) Nothing
                   act <- disjunctionOfList $ get rActs ru
                   (void (solveFactEqs SplitNow [Equal fa act]))
                   return ru

        Just ru ->  case fa of
            (Fact KUFact _ [m]) | (isMixedFact fa)      -> do
                   act <- disjunctionOfList (get rActs ru)
                   (void (solveFactEqs SplitNow [Equal fa act]))
                   void substSystem
                   --void normSystem
                   return ru 
            _ | isDHFact fa                       -> do unless (fa `elem` get rActs ru) $ do
                                                          act <- disjunctionOfList (filter isDHFact $ get rActs ru)
                                                          (void (solveFactDHEqs SplitNow fa act (S.fromList $ basisOfRule ru) (S.fromList $ notBasisOfRule ru) (protoCase SplitNow (S.fromList $ basisOfRule ru) (S.fromList $ notBasisOfRule ru))))
                                                          void substSystem
                                                          --void normSystem
                                                        return ru 
            _ | (isMixedFact fa)                  -> do unless (fa `elem` get rActs ru) $ do
                                                          act <- disjunctionOfList (filter isMixedFact $ get rActs ru)
                                                          let bset = (S.fromList $ basisOfRule ru)
                                                              nbset = (S.fromList $ notBasisOfRule ru)
                                                          (void (solveMixedFactEqs SplitNow (Equal fa act) bset nbset (protoCase SplitNow bset nbset)))
                                                          void substSystem
                                                        return ru
            _                                     -> do unless (fa `elem` get rActs ru) $ do
                                                          act <- disjunctionOfList $ get rActs ru
                                                          (void (solveFactEqs SplitNow [Equal fa act]))
                                                        return ru
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
  | isKdhFact faPrem && isDHFact faPrem =  (solveDHInd rules p faPrem)
  | isKdhFact faPrem && isMixedFact faPrem = (solveDHIndMixed rules p faPrem)
  | isProtoDHFact faPrem =  solveDHIndProto rules p faPrem
  | isProtoMixedFact faPrem = trace (show ("solvingMixedPremise", faPrem)) $ solveDHMixedPremise rules p faPrem
  | isKDFact faPrem = do
      iLearn    <- freshLVar "vl" LSortNode
      mLearn    <- varTerm <$> freshLVar "t" LSortMsg
      let concLearn = kdFact mLearn
          premLearn = outFact mLearn
          -- !! Make sure that you construct the correct rule!
          ruLearn = Rule (IntrInfo IRecvRule) [premLearn] [concLearn] [] []
          cLearn = (iLearn, ConcIdx 0)
          pLearn = (iLearn, PremIdx 0)
      modM sNodes  (M.insert iLearn ruLearn)
      insertChain cLearn p
      solvePremise rules pLearn premLearn
  | isOut faPrem = do    
      nodes <- getM sNodes
      (ru, c, faConc) <- insertFreshNodeConcOutInstMixed rules (M.assocs nodes)
      insertEdges [(c, faConc, faPrem, p)] 
      return $ showRuleCaseName ru  
  | isKIFact faPrem && isDHFact faPrem = do -- should match indicators with indicators (avoiding mu). In paper transform the mu rule also with any 1 way function.
      (ru, c, faConc) <- insertFreshNodeConc rules
      insertOutKIEdge (c, faConc, faPrem, p)
      return $ showRuleCaseName ru
  | isMixedFact faPrem = (solveDHIndMixed rules p faPrem)
  | otherwise = do
      (ru, c, faConc) <- insertFreshNodeConc rules
      insertEdges [(c, faConc, faPrem, p)]
      return $ showRuleCaseName ru

solveDHEq :: LNTerm -> LNTerm -> Reduction String
solveDHEq t1 t2 = do
  _ <- protoCase SplitNow S.empty S.empty (t1, t2)
  return "solveeq"

-- | CR-rule *DG2_chain*: solve a chain constraint.
solveChain :: [RuleAC]              -- ^ All destruction rules.
           -> (NodeConc, NodePrem)  -- ^ The chain to extend by one step.
           -> Reduction String      -- ^ Case name to use.
solveChain rules (c, p) = do
    rules2 <- askM pcRules
    faConc  <- gets $ nodeConcFact c -- instantiated KD conclusion!
    (do  -- solve it by a direct edge
        cRule <- gets $ nodeRule (nodeConcNode c)
        pRule <- gets $ nodeRule (nodePremNode p)
        faPrem <- gets $ nodePremFact p
        contradictoryIf (forbiddenEdge cRule pRule)
        --insertEdges [(c, faConc, faPrem, p)]
        insertDirectEdge faPrem faConc cRule pRule rules2
        --trace (show ("solvededge", faPrem)) $ return ("directedge")
     `disjunction`
     -- extend it with one step
     case kFactView faConc of
         Just (DnK, viewTerm2 -> FUnion args) ->
             do -- If the chain starts at a union message, we
                -- compute the applicable destruction rules directly.
                i <- freshLVar "vr" LSortNode
                let rus = map (ruleACIntrToRuleACInst . mkDUnionRule args)
                              (filter (not . isMsgVar) args)
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
                contradictoryIf (isMsgVar m || isGVar m || isEVar m)
                cRule <- gets $ nodeRule (nodeConcNode c)
                (i, ru) <- insertFreshNode rules (Just cRule)
                contradictoryIf (forbiddenEdge cRule ru)
                -- This requires a modified chain constraint def:
                -- path via first destruction premise of rule ...
                (v, faPrem) <- disjunctionOfList $ take 1 $ enumPrems ru
                --bset <- getM sBasis
                --nbset <- getM sNotBasis
                --if (isMixedFact faConc) 
                --  then extendAndMarkMixed i ru v faPrem faConc bset nbset
                extendAndMark i ru v faPrem faConc
         _ -> error "solveChain: not a down fact" )
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

    insertDirectEdge faPrem faConc cRule pRule rules2
      | isMixedFact faPrem =  (do 
            bset <- getM sBasis
            nbset <- getM sNotBasis
            nodes <- getM sNodes
            case neededexponentslist bset nbset (factTerms faPrem) of
              (Just es) -> do
                              --solveNeededList (\x i -> solvePremise rules (i, PremIdx 0) (kIFact x)) (S.toList es)
                              (newb,newNb) <- disjunctionOfList $ solveNeededList2 (S.toList es)
                              forM_ newb (insertBasisElem)
                              forM_ newNb (insertNotBasisElem)
                              is<- replicateM (length newNb) $ freshLVar "vk" LSortNode
                              forM_ (zip is newNb) (\(i,x)-> insertMuAction rules x i)
                              substSystem
                              insertDirectEdge faPrem faConc cRule pRule rules2
              Nothing -> do 
                          insertDHMixedEdge False (c, faConc, faPrem, p) cRule (S.fromList $ basisOfRule cRule) (S.fromList $ notBasisOfRule cRule) (get crProtocol rules2) (M.assocs nodes) (\x i -> solvePremise (get crProtocol rules2 ++ get crConstruct rules2) (i, PremIdx 0) (kIFact x)) 
                          let mPrem = case kFactView faConc of
                                            Just (DnK, m') -> m'
                                            _              -> error $ "solveChain: impossible"
                              caseName (viewTerm -> FApp o _)    = showFunSymName o
                              caseName (viewTerm -> Lit l)       = showLitName l 
                          void substSystem
                          void normSystem
                          contradictoryIf (illegalCoerce pRule mPrem)
                          trace (show ("comingbackhere>?", faPrem, faConc, (illegalCoerce pRule mPrem), (caseName mPrem))) $ return (caseName mPrem)  ) 
      | otherwise =    (do
                insertEdges [(c, faConc, faPrem, p)]  
                let mPrem = case kFactView faConc of
                      Just (DnK, m') -> m'
                      _              -> error $ "solveChain: impossible"
                    caseName (viewTerm -> FApp o _)    = showFunSymName o
                    caseName (viewTerm -> Lit l)       = showLitName l
                contradictoryIf (illegalCoerce pRule mPrem)
                return (caseName mPrem)   )

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
      then  return "NoCancsolved"
      else (
        if (isNoCanc x y) 
          then return "NoCancsolved" 
          else error "NoCanc does not hold"  
      )

solveDHInd ::  [RuleAC]        -- ^ All rules that have an Out fact as conclusion. 
             -> NodePrem       -- ^ Premise to solve.
             ->LNFact       -- ^ Product term of which we have to find the indicator  
             -> Reduction String -- ^ Case name to use.
solveDHInd rules p faPrem =  do
        bset <- getM sBasis
        nbset <-  getM sNotBasis
        --nodes <-trace (show ("solveDHIND", faPrem, bset, nbset)) $  getM sNodes
        --pRule <- gets $ nodeRule (nodePremNode p)
        case factTerms faPrem of 
          -- [x] -> solveDHIndaux bset nbset x p faPrem (filter isProtocolRule rules) (M.assocs nodes)
          [x] | S.member x bset  -> do 
                    contradictoryIf True
                    return "basis element is not known"
          [x] | otherwise -> solveDHIndaux bset nbset x p rules 
          -- [x] -> solveDHIndaux bset nbset x p faPrem rules (M.assocs nodes)
          _   -> error "In Fact should have arity 1"


solveDHIndMixed ::  [RuleAC]        -- ^ All rules that have an Out fact containing a boxed term as conclusion. 
             -> NodePrem       -- ^ Premise to solve.
             ->LNFact       -- ^ Product term of which we have to find the indicator  
             -> Reduction String -- ^ Case name to use.
solveDHIndMixed rules p faPrem =  do
        bset <- getM sBasis
        nbset <- getM sNotBasis
        nodes <- getM sNodes
        solveDHIndauxMixed bset nbset (filter isMixedTerm $ factTerms faPrem) p faPrem rules (M.assocs nodes)

solveDHIndauxMixed :: S.Set LNTerm -> S.Set LNTerm -> [LNTerm] -> NodePrem -> LNFact -> [RuleAC] -> [(NodeId,RuleACInst)] -> StateT System (FreshT (DisjT (Reader ProofContext))) String
solveDHIndauxMixed bset nbset terms p faPrem rules instrules =
  case neededexponentslist bset nbset terms of
      (Just es) -> do
          solveNeededList (\x i -> solvePremise rules (i, PremIdx 0) (kIFact x)) (S.toList es)
          (solveDHIndMixed rules p faPrem)
          return "LeakedSetInserted"
      Nothing -> do 
          (ru, c, faConc) <- insertFreshNodeConcOutInstMixed rules instrules
          insertDHMixedEdge False (c, faConc, faPrem, p) ru (S.fromList $ basisOfRule ru) (S.fromList $ notBasisOfRule ru) rules instrules (\x i -> solvePremise rules (i, PremIdx 0) (kIFact x))-- instead of root indicator this should be Y.ind^Z.
          return $ showRuleCaseName ru -- (return "done") 


insertMuAction :: [RuleAC] -> Term (Lit Name LVar) -> NodeId -> Reduction String
insertMuAction rules x@(LIT l) i | sortOfLNTerm x == LSortFrNZE = do 
          nodes <- getM sNodes
          let rus = M.elems nodes
              outconcs = concatMap (\ru -> filter isDHFact $ get rConcs ru) rus
          if (elem (outFact x) outconcs || elem (outFact $ fAppdhInv x) outconcs)
            then return "isAlreadyKnown"
            else solvePremise rules (i, PremIdx 0) (kIFact x)
insertMuAction rules x@(LIT l) i = solvePremise rules (i, PremIdx 0) (kIFact x)
insertMuAction _ x i = do
      _ <- insertGoal (ActionG i (kdhFact x)) False
      return "inserted"

--solveDHIndaux :: S.Set LNTerm -> S.Set LNTerm -> LNTerm -> NodePrem -> LNFact -> [RuleAC] -> [(NodeId,RuleACInst)] -> StateT System (FreshT (DisjT (Reader ProofContext))) String
--solveDHIndaux bset nbset term p faPrem rules instrules =
solveDHIndaux :: S.Set LNTerm -> S.Set LNTerm -> LNTerm -> NodePrem -> [RuleAC]  -> StateT System (FreshT (DisjT (Reader ProofContext))) String
solveDHIndaux bset nbset term p rules = do
  nodes <- getM sNodes
  pRule <-   gets $ nodeRule (nodePremNode p)
  let instrules =  (filter (\i-> snd i /= pRule) $ M.assocs nodes)
  case  neededexponents bset nbset term of
      [] -> do  -- TODO: this is where we need to check multiple Out facts!! 
          hndNormal <-  getMaudeHandle
          let nterm = runReader (norm' term) hndNormal
              --xrooterms = multRootList (clterm nterm)
              xrooterms = roots nterm
              inds = case xrooterms of 
                            RootSet Nothing [ts] -> [map (\x -> (rootIndKnown2 hndNormal bset nbset x,x)) $ ts]
                            RootSet (Just _) [ts] -> [map (\x -> (rootIndKnown2 hndNormal bset nbset x,x)) $ ts]
                            RootSet _ tss -> map (map (\x -> (rootIndKnown2 hndNormal bset nbset x,x))) tss
              --inds = map (\x -> (rootIndKnown2 hndNormal bset nbset x,x)) $ xrooterms
              neededInds = map (filter (\(a,b)-> not $ isPublic a)) inds
              newterm = foldr (\a b -> if b == fAppdhEg then a else fAppdhMult (a,b)) fAppdhEg $ map snd $ concat neededInds
              {-clterm t = case viewTerm2 t of --todo: need to refine this. 
                              FdhMu t1 -> if S.member t nbset then t else clterm t1
                              FdhMinus t1 -> clterm t1
                              FdhInv t1 -> clterm t1
                              FdhGinv t1 -> clterm t1
                              _        -> t -}
              n = length $ concat neededInds
              h = head $ extractRoot xrooterms
              toaddnocanc = filter (\t -> not $ isNoCanc h t) (tail $ extractRoot xrooterms)
          forM_ (toaddnocanc) (insertNoCanc h )
          if null neededInds 
            then return "Indicators are public"
            else do   
              possibletuple <- insertFreshNodeConcOutInst (filter isProtocolRule rules) instrules (extractRootSym xrooterms) n Nothing
              let rules2add = map (\(a,(i,_),_,_,c,_) -> (i,a,c)) $ filter (\(a,_,_,_,c,b) -> b) possibletuple
              --is <- replicateM (length rules2add) $ freshLVar "jru" LSortNode
              forM_ rules2add (\(i,ru,c) -> exploitNodeId i ru c)
              --todo: the possibletuple needs to be split in possibletuple 1 2 and 3.
              case neededInds of 
                [nInds] -> insertDHEdges possibletuple (map fst nInds) newterm p (\x i -> solvePremise rules (i, PremIdx 0) (kIFact x)) 
                [nInds, nInds2] -> do 
                    insertDHEdges possibletuple (map fst nInds) newterm p (\x i -> solvePremise rules (i, PremIdx 0) (kIFact x)) 
                    insertDHEdges possibletuple (map fst nInds2) newterm p (\x i -> solvePremise rules (i, PremIdx 0) (kIFact x)) 
                [nInds, nInds2, nInds3] -> do
                    insertDHEdges possibletuple (map fst nInds) newterm p (\x i -> solvePremise rules (i, PremIdx 0) (kIFact x)) 
                    insertDHEdges possibletuple (map fst nInds2) newterm p (\x i -> solvePremise rules (i, PremIdx 0) (kIFact x)) 
                    insertDHEdges possibletuple (map fst nInds3) newterm p (\x i -> solvePremise rules (i, PremIdx 0) (kIFact x)) 
              return "FindingIndicators" 
      es -> do
          -- solveNeededList (\x i -> solvePremise rules (i, PremIdx 0) (kIFact x)) es
          --solveNeededList (insertMuAction rules) es
          (newb,newNb) <- disjunctionOfList $ solveNeededList2 es
          forM_ newb (insertBasisElem)
          forM_ newNb (insertNotBasisElem)
          is<- replicateM (length newNb) $ freshLVar "vk" LSortNode
          forM_ (zip is newNb) (\(i,x)-> insertMuAction rules x i)
          substSystem
          bset2 <- getM sBasis
          nbset2 <- getM sNotBasis
          substs <- getM sSubst
          (solveDHIndaux bset2 nbset2 (applyVTerm substs term) p rules)
          return "LeakedSetInserted"



solveDHIndProto ::  [RuleAC]        -- ^ All rules that have an Out fact containing a boxed term as conclusion. 
             -> NodePrem       -- ^ Premise to solve.
             ->LNFact
             -> Reduction String -- ^ Case name to use.
solveDHIndProto rules p faPrem = do
      nodes <- getM sNodes
      (ru, c, faConc) <-  insertFreshNodeConcInst rules (M.assocs nodes)
      insertDHEdge (c, faConc, faPrem, p) (S.fromList $ basisOfRule ru) (S.fromList $ notBasisOfRule ru) -- instead of root indicator this should be Y.ind^Z.
      return $ showRuleCaseName ru

solveDHMixedPremise ::  [RuleAC]        -- ^ All rules that have an Out fact containing a boxed term as conclusion. 
             -> NodePrem       -- ^ Premise to solve.
             ->LNFact
             -> Reduction String -- ^ Case name to use.
solveDHMixedPremise rules p faPrem = do
      nodes <- getM sNodes
      (ru, c@(i,ci), faConc) <-  insertFreshNodeConcMixed rules (M.assocs nodes)
      insertDHMixedEdge True (c, faConc, faPrem, p) ru (S.fromList $ basisOfRule ru) (S.fromList $ notBasisOfRule ru) rules (M.assocs nodes) (\x i -> solvePremise rules (i, PremIdx 0) (kIFact x))
      newnodes <- getM sNodes
      let newlist = [ t | (_, ru2) <- M.assocs newnodes, (isFreshRule ru2), (_,fa) <- enumConcs ru2 , t<- factTerms fa ]
      contradictoryIf (nub newlist /= newlist)
      (return $ showRuleCaseName ru)



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
