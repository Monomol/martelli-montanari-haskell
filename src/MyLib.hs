module MyLib where

import Data.List

import Data.Set (Set)
import qualified Data.Set as Set

import Data.Tuple (swap)
import Data.Maybe (fromJust, isNothing)

import Data.MultiSet (MultiSet)
import qualified Data.MultiSet as MultiSet


data Term = Var String
    | Function String [Term]
    deriving (Show, Ord, Eq)

-- Predicates
isConstant :: Term -> Bool
isConstant (Function _ []) = True
isConstant _ = False

isVar :: Term -> Bool
isVar (Var _) = True
isVar _ = False

hasSingleElem :: [a] -> Bool
hasSingleElem [_] = True
hasSingleElem _ = False

-- Projections
fHead :: Term -> String
fHead (Function x _) = x
fHead _ = error "not a function"

fParams :: Term -> [Term]
fParams (Function _ x) = x
fParams _ = error "not a function"

fArity :: Term -> Int
fArity (Function _ x) = length x
fArity _ = error "not a function"

type Meqn = (Set Term, MultiSet Term)

-- Predicate
meqn_right_empty :: Meqn -> Bool
meqn_right_empty (_, m) = MultiSet.null m

type T =  [Meqn]
type U = Set Meqn
type R = (T, U)

-- Dec Part

splitVarNonVar :: MultiSet Term -> (MultiSet Term, MultiSet Term)
splitVarNonVar x = MultiSet.partition isVar x

doubleMulSetToMeqn :: (MultiSet Term, MultiSet Term) -> (Set Term, MultiSet Term)
doubleMulSetToMeqn (l, r) = (MultiSet.toSet l, r)

makeMultEq :: MultiSet Term -> (Set Term, MultiSet Term)
makeMultEq x = (doubleMulSetToMeqn . splitVarNonVar) x

dec :: MultiSet Term -> Maybe (Term, Set Meqn)
decTerm :: MultiSet Term -> Term -> Maybe (Term, Set Meqn)
decNonvar :: MultiSet Term -> MultiSet Term -> Maybe (Term, Set Meqn)

decTerm m t =
    if isConstant t then
        Just (t, Set.empty)
    else
        let termArgs = MultiSet.fold (\x y -> (fParams x):y) [] m
            ithM = (transpose . reverse) termArgs -- reverse undoes reversion in the previous fold
            ithMMulSet = map MultiSet.fromList ithM in (
                mapM dec ithMMulSet >>= (\lt -> Just (unzip lt)) >>= (\(miCParams, miFrontEqs) -> Just (Function (fHead t) miCParams, Set.unions miFrontEqs)) 
        )

decNonvar m nonVarMultiset =
    let terms = (MultiSet.distinctElems) nonVarMultiset
-- TODO: here we allow multiple same symbols (say f with different arity) to have different arguments
        termSymbols = (nub . map fHead) terms
        headTerm = head terms in (
            if hasSingleElem termSymbols then
                decTerm m headTerm
            else
                Nothing
    )

dec m =
    let (varMultiset, nonVarMultiset) = splitVarNonVar m in (
        if (not . MultiSet.null) varMultiset then 
            Just ((head . MultiSet.elems) varMultiset, (Set.singleton . makeMultEq) m)
        else
            decNonvar m nonVarMultiset
    )

-- Unify Part


remove_meqn_with_nonempty_m :: U -> Maybe (Meqn, U)
remove_meqn_with_nonempty_m u =
    let (m_empty, m_nonempty) = (partition meqn_right_empty . Set.toList) u in
        do
            (meqn, m_empty_rest) <- uncons m_empty
            Just (meqn, Set.fromList (m_empty_rest ++ m_nonempty))

-- unify :: R -> T
-- unify r =
--     let (t, u) = r in
--         if Set.null u then
--             Just t
--         else
--             do
--                 (removed_meqn, u_rest) <- remove_meqn_with_nonempty_m

