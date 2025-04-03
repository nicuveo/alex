{-# LANGUAGE BlockArguments   #-}
{-# LANGUAGE CPP              #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiWayIf       #-}

module DFAMin (minimizeDFA) where

import           AbsSyn

import           Data.IntMap         (IntMap)
import           Data.IntSet         (IntSet)
import           Data.Map            (Map)
#if !MIN_VERSION_containers(0,6,0)
import           Data.Maybe          (mapMaybe)
#endif

import qualified Data.IntMap         as IntMap
import qualified Data.IntSet         as IntSet
import qualified Data.List           as List
import qualified Data.Map            as Map

import           Control.Monad.Loops
import qualified Control.Monad.State as S

import           Control.Monad       (guard)
import           Data.Traversable    (for)

import           Debug.Trace


-- % Hopcroft's Algorithm for DFA minimization (cut/pasted from Wikipedia):
-- % X refines Y into Y1 and Y2 means
-- %  Y1 := Y ∩ X
-- %  Y2 := Y \ X
-- %  where both Y1 and Y2 are nonempty
--
-- P := {{all accepting states}, {all nonaccepting states}};
-- Q := {{all accepting states}};
-- while (Q is not empty) do
--      choose and remove a set A from Q
--      for each c in ∑ do
--           let X be the set of states for which a transition on c leads to a state in A
--           for each set Y in P for which X refines Y into Y1 and Y2 do
--                replace Y in P by the two sets Y1 and Y2
--                if Y is in Q
--                     replace Y in Q by the same two sets
--                else
--                     add the smaller of the two sets to Q
--           end;
--      end;
-- end;
--
-- % X is a preimage of A under transition function.

-- % observation : Q is always subset of P
-- % let R = P \ Q. then following algorithm is the equivalent of the Hopcroft's Algorithm
--
-- R := {{all nonaccepting states}};
-- Q := {{all accepting states}};
-- while (Q is not empty) do
--      choose a set A from Q
--      remove A from Q and add it to R
--      for each c in ∑ do
--           let X be the set of states for which a transition on c leads to a state in A
--           for each set Y in R for which X refines Y into Y1 and Y2 do
--                replace Y in R by the greater of the two sets Y1 and Y2
--                add the smaller of the two sets to Q
--           end;
--           for each set Y in Q for which X refines Y into Y1 and Y2 do
--                replace Y in Q by the two sets Y1 and Y2
--           end;
--      end;
-- end;
--
-- % The second for loop that iterates over R mutates Q,
-- % but it does not affect the third for loop that iterates over Q.
-- % Because once X refines Y into Y1 and Y2, Y1 and Y2 can't be more refined by X.

minimizeDFA :: forall a. Ord a => DFA Int a -> DFA Int a
minimizeDFA  dfa@(DFA { dfa_start_states = starts,
                        dfa_states       = statemap
                      })
  = DFA { dfa_start_states = starts,
          dfa_states       = Map.fromList states }
  where
      equiv_classes   :: [EquivalenceClass]
      equiv_classes   = groupEquivStates dfa

      numbered_states :: [(Int, EquivalenceClass)]
      numbered_states = number (length starts) equiv_classes

      -- assign each state in the minimized DFA a number, making
      -- sure that we assign the numbers [0..] to the start states.
      number :: Int -> [EquivalenceClass] -> [(Int, EquivalenceClass)]
      number _ [] = []
      number n (ss:sss) =
        case filter (`IntSet.member` ss) starts of
          []      -> (n,ss) : number (n+1) sss
          starts' -> map (,ss) starts' ++ number n sss
          -- if one of the states of the minimized DFA corresponds
          -- to multiple starts states, we just have to duplicate
          -- that state.

      states :: [(Int, State Int a)]
      states = [
                let old_states = map (lookup statemap) (IntSet.toList equiv)
                    accs = map fix_acc (state_acc (headWithDefault undefined old_states))
                           -- accepts should all be the same
                    out  = IntMap.fromList [ (b, get_new old)
                                           | State _ out <- old_states,
                                             (b,old) <- IntMap.toList out ]
                in (n, State accs out)
               | (n, equiv) <- numbered_states
               ]

      fix_acc :: Accept a -> Accept a
      fix_acc acc = acc { accRightCtx = fix_rctxt (accRightCtx acc) }

      fix_rctxt :: RightContext SNum -> RightContext SNum
      fix_rctxt (RightContextRExp s) = RightContextRExp (get_new s)
      fix_rctxt other                = other

      lookup :: Ord k => Map k v -> k -> v
      lookup m k = Map.findWithDefault (error "minimizeDFA") k m

      get_new :: Int -> Int
      get_new = lookup old_to_new

      old_to_new :: Map Int Int
      old_to_new = Map.fromList [ (s,n) | (n,ss) <- numbered_states,
                                          s <- IntSet.toList ss ]

type EquivalenceClass = IntSet
type HopcroftM = S.State ([EquivalenceClass], [EquivalenceClass])

groupEquivStates :: forall a. Ord a => DFA Int a -> [EquivalenceClass]
groupEquivStates DFA { dfa_states = statemap } =
  fst $ S.execState go (initialSets, initialSets)
  where
    -- Initial P and W sets as defined in Hopcroft's algorithm.
    -- They are each composed of two inner sets: the sets of all accepting
    -- states (F), and the set of all non-accepting states (Q \ F).
    initialSets :: [EquivalenceClass]
    initialSets = Map.elems $ Map.fromListWith IntSet.union do
      (index, stateInfo) <- Map.toList statemap
      pure (state_acc stateInfo, IntSet.singleton index)

    -- To each token c in Σ, this map contains a reverse map of transitions.
    -- That is, for each c, we have a map that, to a state s, associate the set
    -- of states that can reach s via c.
    reverseTransitionCache :: [IntMap EquivalenceClass]
    reverseTransitionCache = IntMap.elems $
      IntMap.fromListWith (IntMap.unionWith IntSet.union) do
        (startingState, stateInfo) <- Map.toList statemap
        (token, targetState) <- IntMap.toList $ state_out stateInfo
        pure (token, IntMap.singleton targetState $ IntSet.singleton startingState)

    -- Given an IntMap and an IntSet, restrict the IntMap to the keys that are
    -- within the IntSet.
    restrictKeys :: forall a. IntMap a -> IntSet -> IntMap a
    restrictKeys m s =
#if MIN_VERSION_containers(0,6,0)
      IntMap.restrictKeys m s
#else
      IntMap.filterWithKey (\k _ -> k `IntSet.member` s) m
#endif

    -- Given a set of states A, compute X for each c in Σ.
    -- For a given c, X is the set of states that can reach A via c.
    -- We use the precomputed 'reverseTransitionCache'.
    computeAllXs :: EquivalenceClass -> [EquivalenceClass]
    computeAllXs a = do
      allPreviousStates <- reverseTransitionCache
      let filteredPreviousStates = IntSet.unions $ restrictKeys allPreviousStates a
      guard $ not $ IntSet.null filteredPreviousStates
      pure filteredPreviousStates

    -- Given two sets X and Y, compute their intersection and difference.
    -- Only returns both if both are non-empty, otherwise return neither.
    refine
      :: EquivalenceClass
      -> EquivalenceClass
      -> Maybe (EquivalenceClass, EquivalenceClass)
    refine x y =
      let intersection = IntSet.intersection y x
          difference   = IntSet.difference   y x
      in if IntSet.null intersection || IntSet.null difference
        then Nothing
        else Just (intersection, difference)

    -- Attempt to unpack an A from W.
    unpackA :: HopcroftM (Maybe EquivalenceClass)
    unpackA = do
      w <- getW
      for (List.uncons w) \(a, newW) -> do
        setW newW
        pure a

    -- Main outer loop of the algorithm: we iterate until W is empty.
    go :: HopcroftM ()
    go =
      whileJust_ unpackA \a ->
        for (computeAllXs a) \x -> do
          p <- getP
          newPs <- for p \y ->
            case refine x y of
              Nothing       -> pure [y]
              Just (y1, y2) -> do
                w <- getW
                if | y `List.elem` w                  -> setW $ y1 : y2 : (w List.\\ [y])
                   | IntSet.size y1 <= IntSet.size y2 -> setW $ y1 : w
                   | otherwise                        -> setW $ y2 : w
                pure [y1, y2]
          setP $ concat newPs

    getP = S.gets fst
    getW = S.gets snd
    setP p = S.modify \(_, w) -> (p, w)
    setW w = S.modify \(p, _) -> (p, w)


-- To pacify GHC 9.8's warning about 'head'
headWithDefault :: a -> [a] -> a
headWithDefault a []    = a
headWithDefault _ (a:_) = a
