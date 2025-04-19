module Main (main) where

import MyLib

import qualified Data.Set as Set

import Data.Map (Map)
import qualified Data.Map as Map

import Test.HUnit
import qualified System.Exit as Exit

sSubTVar :: Term -> VarName -> Term -> Term
sSubTVar (Var y) x t' = if x == y then t' else (Var y)
sSubTVar (Function s ts) x t' = Function s (map (\t -> sSubTVar t x t') ts)

sSubTAux :: Term -> [(VarName, Term)] -> Term
sSubTAux t [] = t
sSubTAux t (st:sts) = let (sub_by, sub_to) = st in sSubTAux (sSubTVar t sub_by sub_to) sts 

tToSubAux :: T -> [(VarName, Term)] -> [(VarName, Term)]
tToSubAux [] res = res
tToSubAux ((vs, tms):ts) res = if null tms
    then tToSubAux ts (res ++ map (\x -> (termHead x, Set.findMin vs)) (Set.elems vs))
    else tToSubAux ts (res ++ map (\x -> (termHead x, head tms)) (Set.elems vs))


tToSub :: T -> [(VarName, Term)]
tToSub t = tToSubAux t []

sSubT :: Term -> T -> Term
sSubT t tt = sSubTAux t (tToSub tt)

dec_paper_input1 :: [Term]
dec_paper_input1 = [
    Function "f"
        [
            Var "x1",
            Function "g"
                [Function "a" [],
                    Function "f"
                        [ Var "x5", Function "b" [] ]
                ]
        ],
    Function "f"
        [
            Function "h"
                [ Function "c" [] ],
            Function "g"
                [Var "x2",
                    Function "f"
                        [ Function "b" [], Var "x5" ]
                ]
        ],
    Function "f"
        [
            Function "h"
                [ Var "x4" ],
            Function "g"
                [Var "x6",
                 Var "x3"
                ]
        ]
    ]

dec_paper_output1 :: Maybe (Term, U)
dec_paper_output1 = Just (Function "f" [Var "x1", Function "g" [Var "x2",Var "x3"]],
    Set.fromList [
        (Set.fromList [Var "x1"], [
            Function "h" [Function "c" []],
            Function "h" [Var "x4"]
            ]
        ),
        (Set.fromList [Var "x2", Var "x6"], [Function "a" []]),
        (Set.fromList [Var "x3"], [
            Function "f" [Var "x5", Function "b" []],
            Function "f" [Function "b" [], Var "x5"]
            ]
        )
        ]
    )

dec_paper1 :: Test
dec_paper1 = dec_paper_output1 ~=? (dec dec_paper_input1)

-- This version of the algorithm does not incorporate diff check in dec
dec_cycle1 :: Test 
dec_cycle1 = (Just (Function "f" [Var "x1"], Set.fromList [(Set.fromList [Var "x1"], [Function "f" [Var "x1"]])])) ~=? (dec ([Function "f" [Var "x1"], Function "f" [Function "f" [Var "x1"]]]))

dec_diff_symbols1 :: Test 
dec_diff_symbols1 = Nothing ~=? (dec ([Function "f" [Var "x1"], Function "g" [Var "x1"]]))

-- test from p. 260
substitution_paper_input1 :: Term
substitution_paper_input1 = Function "f" [Var "x1", Function "g" [Var "x2"], Function "a" []]

substitution_paper_input12_sub :: Map VarName Term
substitution_paper_input12_sub = Map.fromList [("x1", Function "h" [Var "x2"]), ("x2", Function "b" [])]

substitution_paper_output1 :: Term
substitution_paper_output1 = Function "f" [Function "h" [Var "x2"], Function "g" [Function "b" []], Function "a" []]

substitution_paper1 :: Test
substitution_paper1 = substitution_paper_output1 ~=? subT substitution_paper_input1 substitution_paper_input12_sub

substitution_paper_input2 :: Term
substitution_paper_input2 = Function "f" [Function "h" [Var "x2"], Function "g" [Function "b" []], Function "a" []]

substitution_paper_output2 :: Term
substitution_paper_output2 = Function "f" [Function "h" [Function "b" []], Function "g" [Function "b" []], Function "a" []]

substitution_paper2 :: Test
substitution_paper2 = substitution_paper_output2 ~=? subT substitution_paper_input2 substitution_paper_input12_sub

substitution_paper_input3 :: Term
substitution_paper_input3 = Function "f" [Var "x1", Function "g" [Var "x2"], Function "a" []]

substitution_paper_output3 :: Term
substitution_paper_output3 = Function "f" [Function "h" [Function "b" []], Function "g" [Function "b" []], Function "a" []]

substitution_paper3 :: Test
substitution_paper3 = substitution_paper_output3 ~=? subT (subT substitution_paper_input3 substitution_paper_input12_sub) substitution_paper_input12_sub

dec_unit_input1 :: [Term]
dec_unit_input1 = [
    Var "x1",
    Function "f" [Function "a" []]
    ]

dec_unit_output1 :: Maybe (Term, U)
dec_unit_output1 = Just (Var "x1", Set.fromList [ (Set.fromList [Var "x1"], [Function "f" [Function "a" []]]) ] )

dec_unit1 :: Test
dec_unit1 = dec_unit_output1 ~=? (dec dec_unit_input1)

dec_unit_input2 :: [Term]
dec_unit_input2 = [
    Function "f" [Function "a" []],
    Function "f" [Function "a" []]
    ]

dec_unit_output2 :: Maybe (Term, U)
dec_unit_output2 = Just (Function "f" [Function "a" []], Set.empty)

dec_unit2 :: Test
dec_unit2 = dec_unit_output2 ~=? (dec dec_unit_input2)

unify_paper1_input1 :: Term
unify_paper1_input1 = Function "f" [Var "x1", Function "g" [Var "x2", Var "x3"], Var "x2", Function "b" []]

unify_paper1_input2 :: Term
unify_paper1_input2 = Function "f" [Function "g" [Function "h" [Function "a" [], Var "x5"], Var "x2"], Var "x1", Function "h" [Function "a" [], Var "x4"], Var "x4"]

terms_to_unify_paper_output :: U
terms_to_unify_paper_output = Set.fromList [
    (Set.singleton (Var "fx1gx2x3x2bfghax5x2x1hax4x4"), [unify_paper1_input1, unify_paper1_input2]),
    (Set.singleton (Var "x1"), []),
    (Set.singleton (Var "x2"), []),
    (Set.singleton (Var "x3"), []),
    (Set.singleton (Var "x4"), []),
    (Set.singleton (Var "x5"), [])
    ]

test_initR :: Test
test_initR = ([], terms_to_unify_paper_output) ~=? (initR unify_paper1_input1 unify_paper1_input2)

terms_remove_paper_beginning_output :: (Meqn, U)
terms_remove_paper_beginning_output = ((Set.singleton (Var "fx1gx2x3x2bfghax5x2x1hax4x4"), [unify_paper1_input1, unify_paper1_input2]), Set.fromList [
    (Set.singleton (Var "x1"), []),
    (Set.singleton (Var "x2"), []),
    (Set.singleton (Var "x3"), []),
    (Set.singleton (Var "x4"), []),
    (Set.singleton (Var "x5"), [])
    ])

remove_paper_beginning :: Test
remove_paper_beginning = (Just terms_remove_paper_beginning_output) ~=? (removeMeqnWithNonemptyM terms_to_unify_paper_output)

terms_remove_dec_unit_input1 :: U
terms_remove_dec_unit_input1 = Set.fromList [
    (Set.singleton (Var "x"), [Function "f" [Var "x1", Var "x1", Var "x1"]]),
    (Set.singleton (Var "x1"), [])
    ]

terms_remove_dec_unit_output1 :: (Meqn, U)
terms_remove_dec_unit_output1 = ((Set.singleton (Var "x"), [Function "f" [Var "x1", Var "x1", Var "x1"]]),
    Set.fromList [
        (Set.singleton (Var "x1"), [])
    ])

terms_remove_unit1 :: Test
terms_remove_unit1 = (Just terms_remove_dec_unit_output1) ~=? (removeMeqnWithNonemptyM terms_remove_dec_unit_input1)

{-
This test result directly do not correspond to the resolution on p. 268.
This is caused by the different nature of choice of multiequation 
that is removed in step (1.1). The following unifiers are checked by hand
for equality. The following test keeps more familiar unifier.
-}
unify_paper1_output :: T
unify_paper1_output = [
    (Set.fromList [Var "fx1gx2x3x2bfghax5x2x1hax4x4"],
    [Function "f" [Var "x1",Var "x1",Var "x2",Var "x4"]]),
    (Set.fromList [Var "x1"],
    [Function "g" [Var "x2",Var "x3"]]),
    (Set.fromList [Var "x2",Var "x3"],
    [Function "h" [Function "a" [],Var "x4"]]),
    (Set.fromList [Var "x4",Var "x5"],
    [Function "b" []])
    ]

unify_terms_paper1 :: Test
unify_terms_paper1 = (Just unify_paper1_output) ~=? (unify (initR unify_paper1_input1 unify_paper1_input2))

unify_terms_paper1_eq_sub :: Test
unify_terms_paper1_eq_sub = (sSubT unify_paper1_input1 unify_paper1_output) ~=? (sSubT unify_paper1_input2 unify_paper1_output)

unify_terms_paper2_input :: R
unify_terms_paper2_input = (
    [(Set.fromList [Var "x2"], [Function "h" [Function "a" [], Var "x4"]]),
    (Set.fromList [Var "fx1gx2x3x2bfghax5x2x1hax4x4"], [Function "f" [Var "x1",Var "x1",Var "x2",Var "x4"]])
    ],
    Set.fromList [
        (Set.fromList [Var "x1"], [Function "g" [Function "h" [Function "a" [], Var "x5"], Function "h" [Function "a" [], Var "x4"]], Function "g" [Function "h" [Function "a" [], Var "x4"], Var "x3"] ]),
        (Set.fromList [Var "x3"], []),
        (Set.fromList [Var "x4"], [Function "b" []]),
        (Set.fromList [Var "x5"], [])]) 

unify_terms_paper2_output :: T
unify_terms_paper2_output = [
    (Set.fromList [Var "fx1gx2x3x2bfghax5x2x1hax4x4"], [Function "f" [Var "x1",Var "x1",Var "x2",Var "x4"]]),
    (Set.fromList [Var "x2"], [Function "h" [Function "a" [],Var "x4"]]),
    (Set.fromList [Var "x1"], [Function "g" [Function "h" [Function "a" [],Var "x5"],Var "x3"]]),
    (Set.fromList [Var "x3"], [Function "h" [Function "a" [],Var "x4"]]),
    (Set.fromList [Var "x4",Var "x5"], [Function "b" []])
    ]

unify_terms_paper2 :: Test
unify_terms_paper2 = (Just unify_terms_paper2_output) ~=? (unify unify_terms_paper2_input)

unify_cycle1 :: Test 
unify_cycle1 = Nothing ~=? (unify (initR (Function "f" [Var "x1"]) (Function "f" [Function "f" [Var "x1"]])))

unify_diff_symbols1 :: Test 
unify_diff_symbols1 = Nothing ~=? (unify (initR (Function "g" [Var "x1"]) (Function "f" [Var "x1"])))

unify_naive1_input1 :: Term
unify_naive1_input1 = Function "g" [Var "x1", Function "f" [Var "x2"], Function "f" [Function "f" [Var "x3"]], Function "f" [Function "f" [Function "f" [Var "x4"]]], Function "f" [Function "f" [Function "f" [Function "f" [Var "x4"]]]]]

unify_naive1_input2 :: Term
unify_naive1_input2 = Function "g" [Var "x6", Var "x7", Var "x8", Var "x9", Var "x10"]

unify_naive1_output :: T
unify_naive1_output = [
    (Set.fromList [Var "gx1fx2ffx3fffx4ffffx4gx6x7x8x9x10"], [Function "g" [Var "x1",Var "x7",Var "x8",Var "x9",Var "x10"]]),
    (Set.fromList [Var "x10"], [Function "f" [Function "f" [Function "f" [Function "f" [Var "x4"]]]]]),
    (Set.fromList [Var "x7"], [Function "f" [Var "x2"]]),
    (Set.fromList [Var "x8"], [Function "f" [Function "f" [Var "x3"]]]),
    (Set.fromList [Var "x9"], [Function "f" [Function "f" [Function "f" [Var "x4"]]]]),
    (Set.fromList [Var "x1", Var "x6"], []),
    (Set.fromList [Var "x2"], []),
    (Set.fromList [Var "x3"], []),
    (Set.fromList [Var "x4"], [])]

unify_naive1 :: Test
unify_naive1 = (Just unify_naive1_output) ~=? (unify (initR unify_naive1_input1 unify_naive1_input2))

unify_naive1_eq_sub :: Test
unify_naive1_eq_sub = (sSubT unify_naive1_input1 unify_naive1_output) ~=? (sSubT unify_naive1_input2 unify_naive1_output)

unify_naive2_input12 :: Term
unify_naive2_input12 = Function "g" [Var "x6", Var "x7", Var "x8", Var "x9", Var "x10"]

unify_naive2_output :: T
unify_naive2_output = [
    (Set.fromList [Var "gx6x7x8x9x10gx6x7x8x9x10"], [Function "g" [Var "x6",Var "x7",Var "x8",Var "x9",Var "x10"]]),
    (Set.fromList [Var "x10"], []),
    (Set.fromList [Var "x6"], []),
    (Set.fromList [Var "x7"], []),
    (Set.fromList [Var "x8"], []),
    (Set.fromList [Var "x9"], [])]

unify_naive2 :: Test
unify_naive2 = (Just unify_naive2_output) ~=? (unify (initR unify_naive2_input12 unify_naive2_input12))

unify_naive2_eq_sub :: Test
unify_naive2_eq_sub = (sSubT unify_naive2_input12 unify_naive2_output) ~=? (sSubT unify_naive2_input12 unify_naive2_output)

unify_naive3_input1 :: Term
unify_naive3_input1 = Function "g" [Var "x6", Var "x7", Var "x8", Var "x9", Var "x10"]

unify_naive3_input2 :: Term
unify_naive3_input2 = Function "g" [Var "x1", Var "x1", Var "x1", Var "x1", Var "x1"]

unify_naive3_output :: T
unify_naive3_output = [
    (Set.fromList [Var "gx6x7x8x9x10gx1x1x1x1x1"], [Function "g" [Var "x6",Var "x7",Var "x8",Var "x9",Var "x10"]]),
    (Set.fromList [Var "x1", Var "x6", Var "x7", Var "x8", Var "x9", Var "x10"], [])]

unify_naive3 :: Test
unify_naive3 = (Just unify_naive3_output) ~=? (unify (initR unify_naive3_input1 unify_naive3_input2))

unify_naive3_eq_sub :: Test
unify_naive3_eq_sub = (sSubT unify_naive3_input1 unify_naive3_output) ~=? (sSubT unify_naive3_input2 unify_naive3_output)

unify_naive4_input1 :: Term
unify_naive4_input1 = Function "g" [Var "x6", Var "x7", Function "a" [], Var "x9", Var "x10"]

unify_naive4_input2 :: Term
unify_naive4_input2 = Function "g" [Var "x1", Var "x1", Var "x1", Var "x1", Var "x1"]

unify_naive4_output :: T
unify_naive4_output = [
    (Set.fromList [Var "gx6x7ax9x10gx1x1x1x1x1"], [Function "g" [Var "x6",Var "x7",Var "x1",Var "x9",Var "x10"]]),
    (Set.fromList [Var "x1", Var "x6", Var "x7", Var "x9", Var "x10"], [Function "a" []])]

unify_naive4 :: Test
unify_naive4 = (Just unify_naive4_output) ~=? (unify (initR unify_naive4_input1 unify_naive4_input2))

unify_naive4_eq_sub :: Test
unify_naive4_eq_sub = (sSubT unify_naive4_input1 unify_naive4_output) ~=? (sSubT unify_naive4_input2 unify_naive4_output)

unify_naive5_input1 :: Term
unify_naive5_input1 = Function "g" [Var "x1", Var "x2", Var "x3", Var "x4", Var "x5", Var "x6"]

unify_naive5_input2 :: Term
unify_naive5_input2 = Function "g" [Var "x2", Var "x3", Var "x4", Var "x5", Var "x6", Function "a" []]

unify_naive5_output :: T
unify_naive5_output = [(Set.fromList [Var "gx1x2x3x4x5x6gx2x3x4x5x6a"], [Function "g" [Var "x1",Var "x2",Var "x3",Var "x4",Var "x5",Var "x6"]]),
    (Set.fromList [Var "x1",Var "x2",Var "x3",Var "x4",Var "x5",Var "x6"], [Function "a" []])]

unify_naive5 :: Test
unify_naive5 = (Just unify_naive5_output) ~=? (unify (initR unify_naive5_input1 unify_naive5_input2))

unify_naive5_eq_sub :: Test
unify_naive5_eq_sub = (sSubT unify_naive5_input1 unify_naive5_output) ~=? (sSubT unify_naive5_input2 unify_naive5_output)

-- Even though this test seems the same to the previous, it has different behavior, since dec extract minimal element and "x10" < "x9", therefore there are two "x10" at the end of output 
unify_naive6_input1 :: Term
unify_naive6_input1 = Function "g" (map (\x -> Var ("x" ++ show x)) ([1..10] :: [Integer]))

unify_naive6_input2 :: Term
unify_naive6_input2 = Function "g" ((map (\x -> Var ("x" ++ show x)) ([2..10] :: [Integer])) ++ [Function "a" []])

unify_naive6_output :: T
unify_naive6_output = [(Set.fromList [Var ("g" ++ concat (map (\x -> "x" ++ show x) ([1..10] :: [Integer])) ++ "g" ++ concat (map (\x -> "x" ++ show x) ([2..10] :: [Integer])) ++ "a")],
    [Function "g" [Var "x1",Var "x2",Var "x3",Var "x4",Var "x5",Var "x6", Var "x7", Var "x8", Var "x9", Var "x10"]]),
    (Set.fromList (map (\x -> Var ("x" ++ show x)) ([1..10] :: [Integer])), [Function "a" []])]

unify_naive6 :: Test
unify_naive6 = (Just unify_naive6_output) ~=? (unify (initR unify_naive6_input1 unify_naive6_input2))

unify_naive6_eq_sub :: Test
unify_naive6_eq_sub = (sSubT unify_naive6_input1 unify_naive6_output) ~=? (sSubT unify_naive6_input2 unify_naive6_output)

unify_terms1_output :: T
unify_terms1_output = [
    (Set.fromList [Var "fx1gx1bx2x2hx3gbx4x2fx4x5kdchx5x5"], [Function "f" [Var "x1",Var "x5",Var "x2",Function "h" [Var "x3"],Var "x5"]]),
    (Set.fromList [Var "x2"], [Function "k" [Function "d" [],Function "c" []]]),
    (Set.fromList [Var "x3",Var "x5"], [Function "g" [Var "x1",Var "x4",Function "k" [Function "d" [],Function "c" []]]]),
    (Set.fromList [Var "x1",Var "x4"], [Function "b" []])
    ]

unify_terms1_input_term1 :: Term
unify_terms1_input_term1 = Function "f" [Var "x1", Function "g" [Var "x1", Function "b" [], Var "x2"], Var "x2", Function "h" [Var "x3"], Function "g" [Function "b" [], Var "x4", Var "x2"]]

unify_terms1_input_term2 :: Term
unify_terms1_input_term2 = Function "f" [Var "x4", Var "x5", Function "k" [Function "d" [], Function "c" []], Function "h" [Var "x5"], Var "x5"]

unify_terms1 :: Test
unify_terms1 = (Just unify_terms1_output) ~=? (unify (initR unify_terms1_input_term1 unify_terms1_input_term2))

unify_terms1_eq_sub :: Test
unify_terms1_eq_sub = (sSubT unify_terms1_input_term1 unify_terms1_output) ~=? (sSubT unify_terms1_input_term2 unify_terms1_output)

dec_tests :: Test
dec_tests = TestList [
    TestLabel "DEC p. 264" dec_paper1,
    
    TestLabel "DEC CYCLE 1" dec_cycle1,
    TestLabel "DEC FAIL DIFF SYMBOLS 1" dec_diff_symbols1,

    TestLabel "DEC Unit 1" dec_unit1,
    TestLabel "DEC Unit 2" dec_unit2
    ]

unif_tests :: Test
unif_tests = TestList [
    TestLabel "UNIFICATION ON P. 268" unify_terms_paper1,
    TestLabel "UNIFICATION ON P. 268 RESULT SUB EQUALITY" unify_terms_paper1_eq_sub,
    TestLabel "UNIFICATION ON P. 268 stepped one step (better keeps order following the paper)" unify_terms_paper2,

    TestLabel "UNIFY FAIL CYCLE 1" unify_cycle1,
    TestLabel "UNIFY FAIL DIFF SYMBOLS 1" unify_diff_symbols1,

    TestLabel "UNIFY NAIVE 1" unify_naive1,
    TestLabel "UNIFY NAIVE 1 RESULT SUB EQUALITY" unify_naive1_eq_sub,
    TestLabel "UNIFY NAIVE 2" unify_naive2,
    TestLabel "UNIFY NAIVE 2 RESULT SUB EQUALITY" unify_naive2_eq_sub,
    TestLabel "UNIFY NAIVE 3" unify_naive3,
    TestLabel "UNIFY NAIVE 3 RESULT SUB EQUALITY" unify_naive3_eq_sub,
    TestLabel "UNIFY NAIVE 4" unify_naive4,
    TestLabel "UNIFY NAIVE 4 RESULT SUB EQUALITY" unify_naive4_eq_sub,
    TestLabel "UNIFY NAIVE 5" unify_naive5,
    TestLabel "UNIFY NAIVE 5 RESULT SUB EQUALITY" unify_naive5_eq_sub,
    TestLabel "UNIFY NAIVE 6" unify_naive6,
    TestLabel "UNIFY NAIVE 6 RESULT SUB EQUALITY" unify_naive6_eq_sub,

    TestLabel "OWN TEST 1" unify_terms1,
    TestLabel "OWN TEST 1 RESULT SUB EQUALITY" unify_terms1_eq_sub
    ]

misc_tests :: Test
misc_tests = TestList [
    TestLabel "SUBSTITUTION p. 260; fst application" substitution_paper1,
    TestLabel "SUBSTITUTION p. 260; snd application" substitution_paper2,
    TestLabel "SUBSTITUTION p. 260; repeated application" substitution_paper3,

    TestLabel "INIT R Test paper" test_initR,

    TestLabel "REMOVE MEQN FROM U Test paper" remove_paper_beginning,
    TestLabel "REMOVE MEQN FROM U Unit 1" terms_remove_unit1
    ]

tests :: Test
tests = TestList [
    TestLabel "DECOMPOSE" dec_tests,
    TestLabel "UNIFICATION" unif_tests,
    TestLabel "MISCELLANEOUS" misc_tests
    ]

main :: IO ()
main = do
    runned_tests <- runTestTT tests
    if failures runned_tests > 0 then Exit.exitFailure else Exit.exitSuccess
