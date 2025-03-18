module Main (main) where

import MyLib

import Data.Set (Set)
import qualified Data.Set as Set

import Data.MultiSet (MultiSet)
import qualified Data.MultiSet as MultiSet

import Test.HUnit
import qualified System.Exit as Exit

paper_input :: MultiSet Term
paper_input = MultiSet.fromList [
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

paper_output :: Maybe (Term, U)
paper_output = Just (Function "f" [Var "x1", Function "g" [Var "x2",Var "x3"]],
    Set.fromList [
        (Set.fromList [Var "x1"], MultiSet.fromOccurList [
            (Function "h" [Var "x4"],1),
            (Function "h" [Function "c" []],1)
            ]
        ),
        (Set.fromList [Var "x2", Var "x6"], MultiSet.fromOccurList [(Function "a" [],1)]),
        (Set.fromList [Var "x3"], MultiSet.fromOccurList [
            (Function "f" [Var "x5", Function "b" []],1),
            (Function "f" [Function "b" [], Var "x5"],1)
            ])
        ]
    )

test_paper :: Test
test_paper = TestCase (assertEqual "" paper_output (dec paper_input))

unit1_input :: MultiSet Term
unit1_input = MultiSet.fromList [
    Var "x1",
    Function "f" [Function "a" []]
    ]

unit1_output :: Maybe (Term, U)
unit1_output = Just (Var "x1", Set.fromList [ (Set.fromList [Var "x1"], MultiSet.fromList [Function "f" [Function "a" []]]) ] )

test_unit1 :: Test
test_unit1 = TestCase (assertEqual "" unit1_output (dec unit1_input))

unit2_input :: MultiSet Term
unit2_input = MultiSet.fromList [
    Function "f" [Function "a" []],
    Function "f" [Function "a" []]
    ]

unit2_output :: Maybe (Term, U)
unit2_output = Just (Function "f" [Function "a" []], Set.empty)

test_unit2 :: Test
test_unit2 = TestCase (assertEqual "" unit2_output (dec unit2_input))

term_to_unify_paper1 :: Term
term_to_unify_paper1 = Function "f" [Var "x1", Function "g" [Var "x2", Var "x3"], Var "x2", Function "b" []]

term_to_unify_paper2 :: Term
term_to_unify_paper2 = Function "f" [Function "g" [Function "h" [Function "a" [], Var "x5"], Var "x2"], Var "x1", Function "h" [Function "a" [], Var "x4"], Var "x4"]

terms_to_unify_paper_output :: U
terms_to_unify_paper_output = Set.fromList [
    (Set.singleton (Var "fx1gx2x3x2bfghax5x2x1hax4x4"), MultiSet.fromList [term_to_unify_paper1, term_to_unify_paper2]),
    (Set.singleton (Var "x1"), MultiSet.empty),
    (Set.singleton (Var "x2"), MultiSet.empty),
    (Set.singleton (Var "x3"), MultiSet.empty),
    (Set.singleton (Var "x4"), MultiSet.empty),
    (Set.singleton (Var "x5"), MultiSet.empty)
    ]

test_initR :: Test
test_initR = TestCase (assertEqual "" ([], terms_to_unify_paper_output) (initR term_to_unify_paper1 term_to_unify_paper2))

terms_remove_paper_beginning_output :: (Meqn, U)
terms_remove_paper_beginning_output = ((Set.singleton (Var "fx1gx2x3x2bfghax5x2x1hax4x4"), MultiSet.fromList [term_to_unify_paper1, term_to_unify_paper2]), Set.fromList [
    (Set.singleton (Var "x1"), MultiSet.empty),
    (Set.singleton (Var "x2"), MultiSet.empty),
    (Set.singleton (Var "x3"), MultiSet.empty),
    (Set.singleton (Var "x4"), MultiSet.empty),
    (Set.singleton (Var "x5"), MultiSet.empty)
    ])

test_remove_paper_beginning :: Test
test_remove_paper_beginning = TestCase (assertEqual "" (Just terms_remove_paper_beginning_output) (removeMeqnWithNonemptyM terms_to_unify_paper_output))

terms_remove_unit1_input :: U
terms_remove_unit1_input = Set.fromList [
    (Set.singleton (Var "x"), MultiSet.singleton (Function "f" [Var "x1", Var "x1", Var "x1"])),
    (Set.singleton (Var "x1"), MultiSet.empty)
    ]

terms_remove_unit1_output :: (Meqn, U)
terms_remove_unit1_output = ((Set.singleton (Var "x"), MultiSet.singleton (Function "f" [Var "x1", Var "x1", Var "x1"])),
    Set.fromList [
        (Set.singleton (Var "x1"), MultiSet.empty)
    ])

test_terms_remove_unit1 :: Test
test_terms_remove_unit1 = TestCase (assertEqual "" (Just terms_remove_unit1_output) (removeMeqnWithNonemptyM terms_remove_unit1_input))

{-
This test result directly does not correspond to the resolution on p. 268.
This is caused by the nondeterministic nature of choice of multieqatuion 
that is removed in step (1.1). The following unifier are checked by hand
by me that they are equal.
-}
test_unify_terms_paper1_output :: T
test_unify_terms_paper1_output = [
    (Set.fromList [Var "fx1gx2x3x2bfghax5x2x1hax4x4"],
    MultiSet.fromOccurList [(Function "f" [Var "x1",Var "x1",Var "x2",Var "x4"],1)]),
    (Set.fromList [Var "x1"],
    MultiSet.fromOccurList [(Function "g" [Var "x2",Var "x2"],1)]),
    (Set.fromList [Var "x2",Var "x3"],
    MultiSet.fromOccurList [(Function "h" [Function "a" [],Var "x4"],1)]),
    (Set.fromList [Var "x4",Var "x5"],
    MultiSet.fromOccurList [(Function "b" [],1)])
    ]

test_unify_terms_paper1 :: Test
test_unify_terms_paper1 = TestCase (assertEqual "" (Just test_unify_terms_paper1_output) (unify (initR term_to_unify_paper1 term_to_unify_paper2)))

dec_tests :: Test
dec_tests = TestList [
    TestLabel "DEC Test paper" test_paper,
    TestLabel "DEC Unit 1" test_unit1,
    TestLabel "DEC Unit 2" test_unit2
    ]

unif_tests :: Test
unif_tests = TestList [
    TestLabel "REMOVE MEQ FROM U Test paper" test_remove_paper_beginning,
    TestLabel "REMOVE MEQ FROM U Unit 1" test_terms_remove_unit1,

    TestLabel "UNIFICATION ON P. 268" test_unify_terms_paper1
    ]

misc_tests :: Test
misc_tests = TestList [
    TestLabel "INIT R Test paper" test_initR
    ]

tests :: [Test]
tests = [
    dec_tests,
    unif_tests,
    misc_tests
    ]

main :: IO ()
main = do
    runned_tests <- mapM runTestTT tests
    if (sum . map failures) runned_tests > 0 then Exit.exitFailure else Exit.exitSuccess
