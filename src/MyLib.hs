module MyLib where

import Data.List

import Data.Set (Set)
import qualified Data.Set as Set

import Data.Tuple (swap)
import Data.Maybe (fromJust, isNothing)

import Data.MultiSet (MultiSet)
import qualified Data.MultiSet as MultiSet

-- Term

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

-- Substitution
-- QQ : This does not much correspond to your implementation from minuska, may be a good show point.
-- QQ : Should I use maps? How close should the Haskell implementation resemble the Coq counterpart?
subTVar :: Term -> Term -> Term -> Term
subTVar (Var y) (Var x) t' = if x == y then t' else (Var y)
subTVar (Function s ts) v@(Var x) t' = Function s (map (\t -> subTVar t v t') ts)
-- QQ: should there be rather error?
subTVar _ _ _ = error "second argument should be variable"


subT :: Term -> [(Term, Term)] -> Term
subT t [] = t
subT t (st:sts) = let (sub_by, sub_to) = st in subT (subTVar t sub_by sub_to) sts 

type Meqn = (Set Term, MultiSet Term)

subMeqn :: Meqn -> [(Term, Term)] -> Meqn
subMeqn meqn st = let (s, m) = meqn in (s, MultiSet.map (\meqn' -> subT meqn' st) m)

-- Predicate
meqn_right_empty :: Meqn -> Bool
meqn_right_empty (_, m) = MultiSet.null m

type T =  [Meqn]
type U = Set Meqn
type R = (T, U)

subUAux :: U -> U -> [(Term, Term)] -> U
subUAux u u_sub st   | null u = u_sub
                    | otherwise = let (meqn, u_rest) = Set.deleteFindMin u in subUAux u_rest (Set.insert (subMeqn meqn st) u_sub) st

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

-- Multiequation reduction and compactification
meqnIntersect :: Meqn -> Meqn -> Bool
meqnIntersect (s1, _) (s2, _) = (not . Set.disjoint s1) s2

combineMeqn :: Meqn -> Meqn -> Meqn
combineMeqn (s1, m1) (s2, m2) = (Set.union s1 s2, MultiSet.union m1 m2)

combineMeqns :: (Foldable f) => f Meqn -> Meqn
combineMeqns meqnToCombine = foldl combineMeqn (Set.empty, MultiSet.empty) meqnToCombine


compactifyByVar :: U -> Term -> Maybe U
compactifyByVar u (Var x) = let (u_with_var, u_without_var) = Set.partition (\(s, _) -> Set.member (Var x) s) u in return (Set.union u_without_var ((Set.singleton . combineMeqns) u_with_var))
compactifyByVar u _ = Nothing

compactifyByVars :: U -> [Term] -> Maybe U
compactifyByVars u [] = return u
compactifyByVars u (v:vs) = compactifyByVar u v >>= (\u' -> compactifyByVars u' vs)

compactify :: U -> Maybe U
compactify u = let (vars, _) = combineMeqns u in compactifyByVars u (Set.toList vars)

-- Unify Part

removeMeqnWithNonemptyM :: U -> Maybe (Meqn, U)
removeMeqnWithNonemptyM u =
    let (m_empty, m_nonempty) = (partition meqn_right_empty . Set.toList) u in
        do
            (meqn, m_empty_rest) <- uncons m_empty
            Just (meqn, Set.fromList (m_empty_rest ++ m_nonempty))

-- unify :: R -> Maybe T
-- unify r =
--     let (t, u) = r in
--         if Set.null u then
--             return t
--         else
--             do
--                 ((s, m), u_rest) <- removeMeqnWithNonemptyM u
--                 (common_part, frontier) <- dec m
--                 if any (meqnIntersect (s, m)) frontier then
--                     Nothing
--                 else

--                     let u_meqn_reduced = (Set.union u_rest frontier) in (
--                         do
--                             u_compactified <- compactify u_meqn_reduced
--                             subU u_compactified
--                             return (t ++ [(s, MultiSet.singleton common_part)])
--                     )


