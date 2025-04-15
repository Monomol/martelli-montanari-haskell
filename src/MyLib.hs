module MyLib where

import Data.List

import Data.Map (Map)
import qualified Data.Map as Map

import Data.Set (Set)
import qualified Data.Set as Set

{-

* BASIC TYPES AND ASSOCIATED FUNCTIONS *

-}
type VarName = String
type SymbolName = String

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

fParams :: Term -> Maybe [Term]
fParams (Function _ x) = Just x
fParams _ = Nothing

subT :: Term -> Map VarName Term -> Term
subT v@(Var x) lt = case (Map.lookup x lt) of
    Nothing -> v
    Just t -> t
subT (Function s ts) lt = Function s (map (\t -> subT t lt) ts)

type Meqn = (Set Term, [Term])

meqnIntersect :: Meqn -> Meqn -> Bool
meqnIntersect (s1, _) (s2, _) = (not . Set.disjoint s1) s2

combineMeqn :: Meqn -> Meqn -> Meqn
combineMeqn (s1, m1) (s2, m2) = (Set.union s1 s2, m1 ++ m2)

combineMeqns :: (Foldable f) => f Meqn -> Meqn
combineMeqns meqnToCombine = foldl combineMeqn (Set.empty, []) meqnToCombine

subMeqn :: Meqn -> Map VarName Term -> Meqn
subMeqn meqn lt = let (s, m) = meqn in (s, map (\meqn' -> subT meqn' lt) m)

meqn_right_empty :: Meqn -> Bool
meqn_right_empty (_, m) = null m

type T =  [Meqn]
type U = Set Meqn
type R = (T, U)

uniqueTermName :: Term -> String
uniqueTermName (Var x) = x
uniqueTermName (Function x xs) = x ++ (concat . map uniqueTermName) xs

varsOfTerm :: Term ->  Set Term
varsOfTerm (Var x) = Set.singleton (Var x)
varsOfTerm (Function _ xs) = (Set.unions . map varsOfTerm) xs

initR :: Term -> Term -> R
initR t t' =
    let unique_vars_of_terms = Set.union (varsOfTerm t) (varsOfTerm t')
        up = (Set.singleton (Var ((uniqueTermName t) ++ (uniqueTermName t'))), [t, t'])
        u_without_up = Set.map (\x -> (Set.singleton x, [])) unique_vars_of_terms in ([],  Set.insert up u_without_up)

subUAux :: U -> U -> Map VarName Term -> U
subUAux u u_sub lt  | null u = u_sub
                    | otherwise = let (meqn, u_rest) = Set.deleteFindMin u in subUAux u_rest (Set.insert (subMeqn meqn lt) u_sub) lt

subU :: U -> Map VarName Term -> U
subU u lt = subUAux u (Set.empty) lt

{-

* DECOMPOSITION *

-}

splitVarNonVar :: [Term] -> ([Term], [Term])
splitVarNonVar x = partition isVar x

doubleMulSetToMeqn :: ([Term], [Term]) -> (Set Term, [Term])
doubleMulSetToMeqn (l, r) = (Set.fromList l, r)

dec :: [Term] -> Maybe (Term, Set Meqn)
decNonvar :: [Term] -> Maybe (Term, Set Meqn)
decTerm :: [Term] -> Term -> Maybe (Term, Set Meqn)

decTerm m t =
    if isConstant t then
        Just (t, Set.empty)
    else
        do
            termArgs <- mapM fParams m
            ithMs <- Just (transpose termArgs)
            ithMsDeced <- (mapM dec ithMs)
            (miCParams, miFrontEqs) <- Just (unzip ithMsDeced)
            Just (Function (termHead t) miCParams, Set.unions miFrontEqs)

-- QQ: TODO: here we allow multiple same symbols (say f with different arity) to have different arguments
decNonvar m =
    let termSymbols = (nub . map termHead) m
        headTerm = head m in (
            if hasSingleElem termSymbols then
                decTerm m headTerm
            else
                Nothing
    )

dec m =
    let vNSplit@(varList, _) = splitVarNonVar m in (
        if null varList then
            decNonvar m
        else
            Just (head varList, (Set.singleton . doubleMulSetToMeqn) vNSplit)
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

unify :: R -> Maybe T
unify r =
    let (t, u) = r in
        if Set.null u then
            return (reverse t)
        else
            do
                let removeRes = removeMeqnWithNonemptyM u in
                    case removeRes of
                        Nothing -> return (reverse t ++ Set.toList u)
                        Just ((s, m), u_rest) ->
                            do
                                (common_part, frontier) <- dec m
                                if any (meqnIntersect (s, m)) frontier then
                                    Nothing
                                else
                                    let sub = Map.fromList (zip (map termHead (Set.toList s)) (repeat common_part))
                                        u_meqn_reduced = (Set.union u_rest frontier) in (
                                        do
                                            u_compactified <- compactify u_meqn_reduced
                                            unify ((subMeqn (s, [common_part]) sub):t, subU u_compactified sub)
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

print_m :: [Term] -> IO()
print_m m = putStr (((encapsulate "( " " )") . (map extract_term)) m)

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
