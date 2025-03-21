module MyLib where

import Data.List

import Data.Map (Map)
import qualified Data.Map as Map

import Data.Set (Set)
import qualified Data.Set as Set

import Data.MultiSet (MultiSet)
import qualified Data.MultiSet as MultiSet

{-

* BASIC TYPES AND ASSOCIATED FUNCTIONS *

-}
type VarName = String
type SymbolName = String

-- QQ : What types should I use? Should I as well generalize this and use just some type?
data Term = Var VarName
    | Function SymbolName [Term]
    deriving (Show, Ord, Eq)

isConstant :: Term -> Bool
isConstant (Function _ []) = True
isConstant _ = False

isVar :: Term -> Bool
isVar (Var _) = True
isVar _ = False

termHead :: Term -> String
termHead (Var x) = x
termHead (Function x _) = x

hasSingleElem :: [a] -> Bool
hasSingleElem [_] = True
hasSingleElem _ = False

fParams :: Term -> [Term]
fParams (Function _ x) = x
fParams _ = error "not a function"

-- QQ : This does not much correspond to your implementation from minuska, may be a good show point.
-- QQ : Should I use maps? How close should the Haskell implementation resemble the Coq counterpart?

subT :: Term -> Map VarName Term -> Term
subT v@(Var x) lt = case (Map.lookup x lt) of
    Nothing -> v
    Just t -> t
subT (Function s ts) lt = Function s (map (\t -> subT t lt) ts)

type Meqn = (Set Term, MultiSet Term)

meqnIntersect :: Meqn -> Meqn -> Bool
meqnIntersect (s1, _) (s2, _) = (not . Set.disjoint s1) s2

combineMeqn :: Meqn -> Meqn -> Meqn
combineMeqn (s1, m1) (s2, m2) = (Set.union s1 s2, MultiSet.union m1 m2)

combineMeqns :: (Foldable f) => f Meqn -> Meqn
combineMeqns meqnToCombine = foldl combineMeqn (Set.empty, MultiSet.empty) meqnToCombine

subMeqn :: Meqn -> Map VarName Term -> Meqn
subMeqn meqn lt = let (s, m) = meqn in (s, MultiSet.map (\meqn' -> subT meqn' lt) m)

meqn_right_empty :: Meqn -> Bool
meqn_right_empty (_, m) = MultiSet.null m

type T =  [Meqn]
type U = Set Meqn
type R = (T, U)

-- for coq use function fresh
uniqueTermName :: Term -> String
uniqueTermName (Var x) = x
uniqueTermName (Function x xs) = x ++ (concat . map uniqueTermName) xs

varsOfTerm :: Term ->  Set Term
varsOfTerm (Var x) = Set.singleton (Var x)
varsOfTerm (Function _ xs) = (Set.unions . map varsOfTerm) xs

initR :: Term -> Term -> R
initR t t' =
    let unique_vars_of_terms = Set.union (varsOfTerm t) (varsOfTerm t')
        up = (Set.singleton (Var ((uniqueTermName t) ++ (uniqueTermName t'))), MultiSet.fromList [t, t'])
        u_without_up = Set.map (\x -> (Set.singleton x, MultiSet.empty)) unique_vars_of_terms in ([],  Set.insert up u_without_up)

-- QQ : Should I implement this using maps?
subUAux :: U -> U -> Map VarName Term -> U
subUAux u u_sub lt  | null u = u_sub
                    | otherwise = let (meqn, u_rest) = Set.deleteFindMin u in subUAux u_rest (Set.insert (subMeqn meqn lt) u_sub) lt

subU :: U -> Map VarName Term -> U
subU u lt = subUAux u (Set.empty) lt

{-

* DECOMPOSITION *

-}

splitVarNonVar :: MultiSet Term -> (MultiSet Term, MultiSet Term)
splitVarNonVar x = MultiSet.partition isVar x

doubleMulSetToMeqn :: (MultiSet Term, MultiSet Term) -> (Set Term, MultiSet Term)
doubleMulSetToMeqn (l, r) = (MultiSet.toSet l, r)

dec :: MultiSet Term -> Maybe (Term, Set Meqn)
decTerm :: MultiSet Term -> Term -> Maybe (Term, Set Meqn)
decNonvar :: MultiSet Term -> Maybe (Term, Set Meqn)

decTerm m t =
    if isConstant t then
        Just (t, Set.empty)
    else
        let termArgs = MultiSet.fold (\x y -> (fParams x):y) [] m
            ithM = transpose termArgs -- TODO: here used to be a reverse, but it shoul be useless as we dont care about positions but just purely about contents (the equalities);reverse undoes reversion in the previous fold
            ithMMulSet = map MultiSet.fromList ithM in (
                mapM dec ithMMulSet >>= (\lt -> Just (unzip lt)) >>= (\(miCParams, miFrontEqs) -> Just (Function (termHead t) miCParams, Set.unions miFrontEqs)) 
        )

decNonvar m =
    let terms = (MultiSet.distinctElems) m
-- QQ: TODO: here we allow multiple same symbols (say f with different arity) to have different arguments
        termSymbols = (nub . map termHead) terms
        headTerm = head terms in (
            if hasSingleElem termSymbols then
                decTerm m headTerm
            else
                Nothing
    )

dec m =
    let vNSplit@(varMultiset, _) = splitVarNonVar m in (
        if (not . MultiSet.null) varMultiset then 
            Just (MultiSet.findMin varMultiset, (Set.singleton . doubleMulSetToMeqn) vNSplit)
        else
            decNonvar m
    )

{-

* COMPACTIFICATION *

-}

-- QQ - What is the level that I should care for other users? If I use VarName instead of Term,
-- then this function does not fail on a function name that may correspond to some variable name.
compactifyByVar :: U -> Term -> Maybe U
compactifyByVar u (Var x) = let (u_with_var, u_without_var) = Set.partition (\(s, _) -> Set.member (Var x) s) u in return (Set.union u_without_var ((Set.singleton . combineMeqns) u_with_var))
compactifyByVar _ _ = Nothing

compactifyByVars :: U -> [Term] -> Maybe U
compactifyByVars u [] = return u
compactifyByVars u (v:vs) = compactifyByVar u v >>= (\u' -> compactifyByVars u' vs)

compactify :: U -> Maybe U
compactify u = let (vars, _) = combineMeqns u in compactifyByVars u (Set.toList vars)

{-

* UNIFICATION *

-}

removeMeqnWithNonemptyM :: U -> Maybe (Meqn, U)
removeMeqnWithNonemptyM u =
    let (m_empty, m_nonempty) = (partition meqn_right_empty . Set.toList) u in
        do
            (meqn, m_nonempty_rest) <- uncons m_nonempty
            Just (meqn, Set.fromList (m_empty ++ m_nonempty_rest))

meqnValid :: Meqn -> Bool
meqnValid (s, m) = s_valid && m_valid
    where
        s_valid = (not . Set.null) s && (Set.null . snd . Set.partition isVar) s
        m_valid = (MultiSet.null . fst . MultiSet.partition isVar) m

unify :: R -> Maybe T
unify r =
    let (t, u) = r in
        if Set.null u then
            -- QQ : Should the order correspond to paper? Generally, should I just care about equality?
            return (reverse t)
        else
            do
                ((s, m), u_rest) <- removeMeqnWithNonemptyM u
                (common_part, frontier) <- dec m
                if any (meqnIntersect (s, m)) frontier then
                    Nothing
                else
                    let sub = Map.fromList (zip (map termHead (Set.toList s)) (repeat common_part))
                        u_meqn_reduced = (Set.union u_rest frontier) in (
                        do
                            u_compactified <- compactify u_meqn_reduced
                            unify ((subMeqn (s, MultiSet.singleton common_part) sub):t, subU u_compactified sub)
                    )

{-

* PRINTING *

-}

encapsulate :: String -> String -> [String] -> String
encapsulate l r xs = l ++ (intercalate ", ") xs ++ r

extract_term :: Term -> String
extract_term (Var x) = x
extract_term (Function x []) = x 
extract_term (Function x xs) = x ++ encapsulate "(" ")" (map extract_term xs)

print_s :: Set Term -> IO()
print_s s = putStr (((encapsulate "{ " " }") . (map extract_term) . Set.elems) s)

print_m :: MultiSet Term -> IO()
print_m m = putStr (((encapsulate "( " " )") . (map extract_term) . MultiSet.distinctElems) m)

print_meqn :: Meqn -> IO()
print_meqn (s, m) = putStr "    " >> print_s s >> putStr " = " >> print_m m >> putStrLn ","

print_meqns :: [Meqn] -> IO()
print_meqns [] = putStr ""
print_meqns (meqn:sm) = print_meqn meqn >> print_meqns sm

encapsulate_print :: String -> IO() -> String -> IO()
encapsulate_print left to_print right = putStr left >> to_print >> putStr right

print_dec :: (Term, Set Meqn) -> IO()
print_dec (f, set_sm) = encapsulate_print ("Common part\n    " ++ extract_term f ++ "\nFrontier\n{\n") (print_meqns (Set.elems set_sm)) "}"

print_U :: U -> IO()
print_U u = encapsulate_print "U\n{\n" (print_meqns (Set.elems u)) "}\n"

print_T :: T -> IO()
print_T t = encapsulate_print "T\n[\n" (print_meqns t) "]\n"

print_R :: R -> IO()
print_R (t, u) = print_T t >> putStrLn "" >> print_U u
