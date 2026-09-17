{-# LANGUAGE TemplateHaskell #-}
{-
 Copyright (C) 2013 Luke Brown <http://gsd.uwaterloo.ca>

 Permission is hereby granted, free of charge, to any person obtaining a copy of
 this software and associated documentation files (the "Software"), to deal in
 the Software without restriction, including without limitation the rights to
 use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies
 of the Software, and to permit persons to whom the Software is furnished to do
 so, subject to the following conditions:

 The above copyright notice and this permission notice shall be included in all
 copies or substantial portions of the Software.

 THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 SOFTWARE.
-}
module Suite.Positive (tg_Test_Suite_Positive) where

import Functions
import Language.Clafer.Intermediate.Intclafer
import Data.Foldable hiding (forM_)
import Data.List (isInfixOf)
import Data.Maybe
import Control.Monad
import Language.Clafer
import Language.ClaferT
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.TH
import qualified Data.Map as Map
import Prelude

tg_Test_Suite_Positive :: TestTree
tg_Test_Suite_Positive = $(testGroupGenerator)

positiveClaferModels :: IO [(String, String)]
positiveClaferModels = getClafers "test/positive"

case_compileTest :: Assertion
case_compileTest = do
    claferModels <- positiveClaferModels
    let compiledClafers = map (\(file', model) -> (file', compileOneFragment defaultClaferArgs{keep_unused = True} model)) claferModels
    forM_ compiledClafers (\(file', compiled) ->
        when (not $ compiledCheck compiled) $ putStrLn (file' ++ " Error: " ++ (show $ fromLeft compiled)))
    (andMap (compiledCheck . snd) compiledClafers
        @? "test/positive fail: The above claferModels did not compile.")

case_reference_Unused_Abstract_Clafer :: Assertion
case_reference_Unused_Abstract_Clafer = do
    model <- readFile "test/positive/i235.cfr"
    let compiledClafers = [("None", compileOneFragment defaultClaferArgs{scope_strategy = None} model), ("Simple", compileOneFragment defaultClaferArgs{scope_strategy = Simple} model)]
    forM_ compiledClafers (\(ss, compiled) ->
        when (not $ compiledCheck compiled) $ putStrLn ("i235.cfr failed for scope_strategy = " ++ ss))
    (andMap (compiledCheck . snd) compiledClafers
        @? "reference_Unused_Abstract_Clafer (i235) failed, error for referencing unused abstract clafer")

-- Sigil-Logic/clafer#12 (PR #14, HOARDE Codex Cycle 1 finding): under the
-- default flags (keep_unused = False) remUnusedAbs prunes abstract Container
-- together with its nested Child, so the `parent` translation for the
-- top-level abstract Feature must enumerate the optimized module, not the
-- resolver-time map -- otherwise it emits the pruned relation r_c0_Child.
case_parent_ref_skips_pruned_extenders :: Assertion
case_parent_ref_skips_pruned_extenders = do
    let model = "abstract Feature\n    [ no parent ]\n\nabstract Container\n    Child : Feature\n\nConcrete : Feature"
    let compiled = compileOneFragment defaultClaferArgs model
    compiledCheck compiled @? "parent_ref_skips_pruned_extenders: model failed to compile"
    let alloyCode = outputCode $ fromJust $ Map.lookup Alloy $ fromRight compiled
    (not ("r_c0_Child" `isInfixOf` alloyCode)
        @? "parent_ref_skips_pruned_extenders: output references the pruned containment relation r_c0_Child")
    (("~(none -> none)" `isInfixOf` alloyCode)
        @? "parent_ref_skips_pruned_extenders: expected the empty parent relation ~(none -> none) when no emitted nested extender exists")

-- Sigil-Logic/clafer#15: under the default flags (keep_unused = False)
-- remUnusedAbs dropped every top-level abstract no concrete clafer
-- extends -- including those the retained module still mentions as a
-- reference target or in a constraint -- while the generators kept
-- emitting the mention, so the output dangled (`one c0_Target`,
-- `no c0_Extra`; rejected by Alloy and chocosolver alike).  A mentioned
-- unused abstract is now kept with the zero cardinality --keep-unused
-- has always given every unused abstract, so for it the default output
-- equals the --keep-unused output; an unmentioned one is still dropped,
-- and a mention inside a dropped abstract retains nothing.

si15_refTargetModel, si15_constraintMentionModel :: String
si15_refTargetModel = "abstract Target\n\nuser\n    pick -> Target"
si15_constraintMentionModel = "abstract Extra\n\nThing\n    [ no Extra ]"

si15_alloy :: ClaferArgs -> String -> String
si15_alloy args' model = outputCode $ fromJust $ Map.lookup Alloy $ fromRight $ compileOneFragment args' model

case_mentioned_unused_abstract_is_kept_with_zero_card :: Assertion
case_mentioned_unused_abstract_is_kept_with_zero_card =
    forM_ [ ("reference target", si15_refTargetModel, "c0_Target")
          , ("constraint mention", si15_constraintMentionModel, "c0_Extra") ] $ \(variant, model, uid) -> do
        let compiled = compileOneFragment defaultClaferArgs model
        compiledCheck compiled @? (variant ++ ": model failed to compile")
        let alloyCode = outputCode $ fromJust $ Map.lookup Alloy $ fromRight compiled
        (("abstract sig " ++ uid) `isInfixOf` alloyCode)
            @? (variant ++ ": the mentioned abstract " ++ uid ++ " was dropped, leaving its mention dangling")
        (("fact { #" ++ uid ++ " = 0 }") `isInfixOf` alloyCode)
            @? (variant ++ ": the kept abstract " ++ uid ++ " must carry the zero cardinality (no instances)")

case_mentioned_unused_abstract_default_equals_keep_unused :: Assertion
case_mentioned_unused_abstract_default_equals_keep_unused =
    forM_ [ ("reference target", si15_refTargetModel), ("constraint mention", si15_constraintMentionModel) ] $ \(variant, model) ->
        (si15_alloy defaultClaferArgs model == si15_alloy defaultClaferArgs{keep_unused = True} model)
            @? (variant ++ ": the default-flag Alloy output differs from the --keep-unused output")

case_mentioned_unused_abstract_choco_defines_target :: Assertion
case_mentioned_unused_abstract_choco_defines_target = do
    let compiled = compileOneFragment defaultClaferArgs{mode = [Alloy, Choco]} si15_refTargetModel
    compiledCheck compiled @? "reference target: model failed to compile"
    let chocoCode = outputCode $ fromJust $ Map.lookup Choco $ fromRight compiled
    ("c0_Target = Abstract(\"c0_Target\")" `isInfixOf` chocoCode)
        @? "reference target: the Choco output refers to c0_Target without defining it"

case_unmentioned_unused_abstract_is_still_dropped :: Assertion
case_unmentioned_unused_abstract_is_still_dropped = do
    let model = "abstract Unused\n\nThing"
    (not ("c0_Unused" `isInfixOf` si15_alloy defaultClaferArgs model))
        @? "an abstract nothing mentions must still be dropped under the default flags"
    ("fact { #c0_Unused = 0 }" `isInfixOf` si15_alloy defaultClaferArgs{keep_unused = True} model)
        @? "--keep-unused must still keep an unmentioned abstract with zero cardinality"

case_mention_inside_dropped_abstract_retains_nothing :: Assertion
case_mention_inside_dropped_abstract_retains_nothing = do
    let alloyCode = si15_alloy defaultClaferArgs "abstract Outer\n    [ no Inner ]\n\nabstract Inner\n\nThing"
    (not ("c0_Outer" `isInfixOf` alloyCode) && not ("c0_Inner" `isInfixOf` alloyCode))
        @? "a mention inside a dropped abstract must not retain the mentioned abstract"

case_mention_inside_kept_abstract_retains_transitively :: Assertion
case_mention_inside_kept_abstract_retains_transitively = do
    let alloyCode = si15_alloy defaultClaferArgs "abstract Outer\n    [ no Inner ]\n\nabstract Inner\n\nThing\n    pick -> Outer"
    forM_ ["c0_Outer", "c0_Inner"] $ \uid ->
        (("abstract sig " ++ uid) `isInfixOf` alloyCode && ("fact { #" ++ uid ++ " = 0 }") `isInfixOf` alloyCode)
            @? ("a mention inside a kept abstract must retain " ++ uid ++ " with zero cardinality")

case_local_name_colliding_with_uid_mentions_nothing :: Assertion
case_local_name_colliding_with_uid_mentions_nothing = do
    -- HOARDE Codex, PR #28 Cycle 1: a quantifier variable is bound
    -- locally, so its name mentions no clafer even when it coincides
    -- with a generated UID; the unextended, unmentioned Target must
    -- still be dropped under the default flags.
    let model = "abstract Target\n\nThing\n    [ all c0_Target : Thing | no c0_Target ]"
    let alloyCode = si15_alloy defaultClaferArgs model
    (not ("abstract sig c0_Target" `isInfixOf` alloyCode))
        @? "a local name that coincides with a UID must not retain the abstract of that UID"
    (("all  c0_Target : c0_Thing | no c0_Target" `isInfixOf` alloyCode)
        @? "the quantified constraint must still be emitted unchanged")
    -- the Choco generator classified identifiers as global by name
    -- lookup alone, so the same local was emitted as global(c0_Target)
    let compiled = compileOneFragment defaultClaferArgs{mode = [Alloy, Choco]} model
    compiledCheck compiled @? "collision model failed to compile"
    let chocoCode = outputCode $ fromJust $ Map.lookup Choco $ fromRight compiled
    (("none(c0_Target)" `isInfixOf` chocoCode) && not ("global(c0_Target)" `isInfixOf` chocoCode))
        @? "the Choco output must emit the locally bound c0_Target as a local, not global(c0_Target)"

-- Sigil-Logic/clafer#18: the Choco generator emitted .refTo/.refToUnique
-- only for a plain clafer target and dropped every other reference
-- target -- set expressions over clafers, integer and string
-- enumerations, `integer -- e` -- as a bare `cN_uid;` statement, or,
-- for a single literal, emitted the primitive type without the
-- literal.  chocosolver's AstRef takes exactly one target type, so such
-- targets are now emitted as a carrier type plus a membership
-- constraint on joinRef($this()); a target the chocosolver DSL cannot
-- express declines Choco output through the unsupported-feature path,
-- as reals do.  The expected texts below are the encodings validated
-- against chocosolver -v in the #18 spike.

si18_results :: String -> Map.Map ClaferMode CompilerResult
si18_results model = fromRight $ compileOneFragment defaultClaferArgs{mode = [Alloy, Choco]} model

si18_choco :: String -> String
si18_choco model = outputCode $ fromJust $ Map.lookup Choco $ si18_results model

si18_personModel :: String
si18_personModel = "abstract Person\n    abstract Head\n\nAlice : Person\n    `Head\n\nElla : Person\n\n"

si18_isBareStatement :: String -> Bool
si18_isBareStatement l = take 1 l == "c" && take 1 (reverse l) == ";" && all (`notElem` ".(= ") l

si18_assertEncoding :: String -> String -> String -> Assertion
si18_assertEncoding variant model expected = do
    let chocoCode = si18_choco model
    (expected `isInfixOf` chocoCode)
        @? (variant ++ ": expected the Choco output to contain\n" ++ expected ++ "but got\n" ++ chocoCode)
    (not $ any si18_isBareStatement $ lines chocoCode)
        @? (variant ++ ": the Choco output must not contain a bare cN_uid; statement:\n" ++ chocoCode)

case_set_expression_ref_targets_over_clafers_are_encoded :: Assertion
case_set_expression_ref_targets_over_clafers_are_encoded =
    forM_ [ ("union", "friend -> Alice ++ Ella 2\n",
             "c0_friend.refToUnique(c0_Person);\nc0_friend.addConstraint($in(joinRef($this()), union(global(c0_Alice), global(c0_Ella))));\n")
          , ("intersection", "onlyAlice -> Alice ** Person\n",
             "c0_onlyAlice.refToUnique(c0_Person);\nc0_onlyAlice.addConstraint($in(joinRef($this()), inter(global(c0_Alice), global(c0_Person))));\n")
          , ("difference", "exceptElla -> Person -- Ella\n",
             "c0_exceptElla.refToUnique(c0_Person);\nc0_exceptElla.addConstraint($in(joinRef($this()), diff(global(c0_Person), global(c0_Ella))));\n")
          , ("bag", "buddies ->> Alice ++ Ella 2\n",
             "c0_buddies.refTo(c0_Person);\nc0_buddies.addConstraint($in(joinRef($this()), union(global(c0_Alice), global(c0_Ella))));\n")
          , ("join inside a set expression", "someone -> Person.Head ++ Ella\n",
             "c0_someone.refToUnique(rc.getModel().getTypeRoot());\nc0_someone.addConstraint($in(joinRef($this()), union(join(global(c0_Person), c0_Head), global(c0_Ella))));\n")
          ] $ \(variant, decl, expected) -> si18_assertEncoding variant (si18_personModel ++ decl) expected

case_unrelated_union_ref_target_uses_the_type_root :: Assertion
case_unrelated_union_ref_target_uses_the_type_root =
    si18_assertEncoding "unrelated union" "A\nB\nr -> A ++ B\n"
        "c0_r.refToUnique(rc.getModel().getTypeRoot());\nc0_r.addConstraint($in(joinRef($this()), union(global(c0_A), global(c0_B))));\n"

case_integer_ref_targets_are_encoded :: Assertion
case_integer_ref_targets_are_encoded =
    forM_ [ ("enumeration", "grade -> 1, 2, 3\n",
             "c0_grade.refToUnique(Int);\nc0_grade.addConstraint($in(joinRef($this()), union(union(constant(1), constant(2)), constant(3))));\n")
          , ("single literal", "single -> 1\n",
             "c0_single.refToUnique(Int);\nc0_single.addConstraint($in(joinRef($this()), constant(1)));\n")
          , ("complement", "nonZero -> integer -- 0\n",
             "c0_nonZero.refToUnique(Int);\nc0_nonZero.addConstraint(notIn(joinRef($this()), constant(0)));\n")
          , ("complement algebra", "x -> integer -- 0 -- 1\n",
             "c0_x.refToUnique(Int);\nc0_x.addConstraint(notIn(joinRef($this()), union(constant(0), constant(1))));\n")
          , ("universe intersection", "y -> integer ** (1 ++ 2)\n",
             "c0_y.refToUnique(Int);\nc0_y.addConstraint($in(joinRef($this()), union(constant(1), constant(2))));\n")
          , ("finite difference", "z -> (1 ++ 2) -- 2\n",
             "c0_z.refToUnique(Int);\nc0_z.addConstraint($in(joinRef($this()), diff(union(constant(1), constant(2)), constant(2))));\n")
          ] $ \(variant, decl, expected) -> si18_assertEncoding variant decl expected

-- HOARDE Codex, PR #30 Cycle 1: pin every reachable operand-class
-- pairing of the finite (F) / co-finite (C) / universe (U) integer set
-- algebra, not just the shapes in the corpus.
case_integer_set_algebra_matrix :: Assertion
case_integer_set_algebra_matrix =
    forM_ [ ("F ++ F", "x -> 1 ++ 2",                          "$in(joinRef($this()), union(constant(1), constant(2)))")
          , ("C ++ F", "x -> (integer -- 0) ++ 1",              "notIn(joinRef($this()), diff(constant(0), constant(1)))")
          , ("F ++ C", "x -> 1 ++ (integer -- 0)",              "notIn(joinRef($this()), diff(constant(0), constant(1)))")
          , ("C ++ C", "x -> (integer -- 0) ++ (integer -- 1)", "notIn(joinRef($this()), inter(constant(0), constant(1)))")
          , ("F ** F", "x -> (1 ++ 2) ** 2",                   "$in(joinRef($this()), inter(union(constant(1), constant(2)), constant(2)))")
          , ("C ** F", "x -> (integer -- 0) ** 1",              "$in(joinRef($this()), diff(constant(1), constant(0)))")
          , ("F ** C", "x -> 1 ** (integer -- 0)",              "$in(joinRef($this()), diff(constant(1), constant(0)))")
          , ("C ** C", "x -> (integer -- 0) ** (integer -- 1)", "notIn(joinRef($this()), union(constant(0), constant(1)))")
          , ("U ** C", "x -> integer ** (integer -- 0)",        "notIn(joinRef($this()), constant(0))")
          , ("F ** U", "x -> 1 ** integer",                     "$in(joinRef($this()), constant(1))")
          , ("C ** U", "x -> (integer -- 0) ** integer",        "notIn(joinRef($this()), constant(0))")
          , ("F -- F", "x -> (1 ++ 2) -- 2",                   "$in(joinRef($this()), diff(union(constant(1), constant(2)), constant(2)))")
          , ("U -- F", "x -> integer -- 0",                     "notIn(joinRef($this()), constant(0))")
          , ("U -- C", "x -> integer -- (integer -- 0)",        "$in(joinRef($this()), constant(0))")
          , ("C -- F", "x -> (integer -- 0) -- 1",              "notIn(joinRef($this()), union(constant(0), constant(1)))")
          , ("F -- C", "x -> 1 -- (integer -- 0)",              "$in(joinRef($this()), inter(constant(1), constant(0)))")
          , ("C -- C", "x -> (integer -- 0) -- (integer -- 1)", "$in(joinRef($this()), diff(constant(1), constant(0)))")
          ] $ \(variant, decl, restriction) ->
        si18_assertEncoding variant (decl ++ "\n") ("c0_x.refToUnique(Int);\nc0_x.addConstraint(" ++ restriction ++ ");\n")

case_integer_universe_results_need_no_restriction :: Assertion
case_integer_universe_results_need_no_restriction =
    forM_ [ ("U ++ F", "x -> integer ++ 1"), ("F ++ U", "x -> 1 ++ integer"), ("U ++ U", "x -> integer ++ integer")
          , ("U ++ C", "x -> integer ++ (integer -- 0)"), ("C ++ U", "x -> (integer -- 0) ++ integer") ] $ \(variant, decl) -> do
        let chocoCode = si18_choco (decl ++ "\n")
        ("c0_x.refToUnique(Int);\n" `isInfixOf` chocoCode && not ("c0_x.addConstraint" `isInfixOf` chocoCode))
            @? (variant ++ ": the result is the whole integer domain and needs no restriction:\n" ++ chocoCode)

case_empty_integer_results_decline_choco_output :: Assertion
case_empty_integer_results_decline_choco_output =
    -- (`integer ** integer` and `integer -- integer` are rejected by the
    -- clafer type checker before any backend runs, so they are not here)
    forM_ [ ("F -- U", "x -> 1 -- integer"), ("C -- U", "x -> (integer -- 0) -- integer") ] $ \(variant, decl) ->
        case Map.lookup Choco (si18_results (decl ++ "\n")) of
            Just NoCompilerResult{reason = why} -> ("c0_x" `isInfixOf` why && "empty set of integers" `isInfixOf` why)
                @? (variant ++ ": the decline reason must name c0_x and the empty set, got: " ++ why)
            other -> assertFailure (variant ++ ": an empty integer set must decline Choco output, got: " ++ show other)

case_integer_universe_ref_target_needs_no_restriction :: Assertion
case_integer_universe_ref_target_needs_no_restriction = do
    let chocoCode = si18_choco "u -> integer ++ 1\n"
    ("c0_u.refToUnique(Int);\n" `isInfixOf` chocoCode && not ("c0_u.addConstraint" `isInfixOf` chocoCode))
        @? ("integer ++ 1 is the whole integer domain and needs no restriction:\n" ++ chocoCode)

case_string_ref_targets_are_encoded :: Assertion
case_string_ref_targets_are_encoded =
    forM_ [ ("single literal", "name -> \"Alice\"\n",
             "c0_name.refToUnique(string);\nc0_name.addConstraint(equal(joinRef($this()), constant(\"\\\"Alice\\\"\")));\n")
          , ("enumeration", "tag -> \"a\", \"b\"\n",
             "c0_tag.refToUnique(string);\nc0_tag.addConstraint(or(equal(joinRef($this()), constant(\"\\\"a\\\"\")), equal(joinRef($this()), constant(\"\\\"b\\\"\"))));\n")
          ] $ \(variant, decl, expected) -> si18_assertEncoding variant decl expected

-- The same finite (F) / co-finite (C) / universe (U) algebra over string
-- literal lists (Sigil-Logic/clafer#18, post-cycle scope addition agreed
-- with Frank Zeyda on 2026-09-16): a co-finite string set is a conjunction
-- of inequalities, the complement of the enumeration's disjunction.
case_string_set_algebra_matrix :: Assertion
case_string_set_algebra_matrix =
    forM_ [ ("F ++ F", "s -> \"a\" ++ \"b\"", "or(equal(joinRef($this()), constant(\"\\\"a\\\"\")), equal(joinRef($this()), constant(\"\\\"b\\\"\")))")
          , ("C ++ F", "s -> (string -- \"a\") ++ \"b\"", "notEqual(joinRef($this()), constant(\"\\\"a\\\"\"))")
          , ("F ** F", "s -> (\"a\" ++ \"b\") ** \"b\"", "equal(joinRef($this()), constant(\"\\\"b\\\"\"))")
          , ("C ** F", "s -> (string -- \"a\") ** \"b\"", "equal(joinRef($this()), constant(\"\\\"b\\\"\"))")
          , ("F ** C", "s -> \"a\" ** (string -- \"b\")", "equal(joinRef($this()), constant(\"\\\"a\\\"\"))")
          , ("C ** C", "s -> (string -- \"a\") ** (string -- \"b\")", "and(notEqual(joinRef($this()), constant(\"\\\"a\\\"\")), notEqual(joinRef($this()), constant(\"\\\"b\\\"\")))")
          , ("U ** C", "s -> string ** (string -- \"a\")", "notEqual(joinRef($this()), constant(\"\\\"a\\\"\"))")
          , ("C ** U", "s -> (string -- \"a\") ** string", "notEqual(joinRef($this()), constant(\"\\\"a\\\"\"))")
          , ("F -- F", "s -> (\"a\" ++ \"b\") -- \"b\"", "equal(joinRef($this()), constant(\"\\\"a\\\"\"))")
          , ("U -- F", "s -> string -- \"a\"", "notEqual(joinRef($this()), constant(\"\\\"a\\\"\"))")
          , ("U -- F -- F", "s -> string -- \"a\" -- \"b\"", "and(notEqual(joinRef($this()), constant(\"\\\"a\\\"\")), notEqual(joinRef($this()), constant(\"\\\"b\\\"\")))")
          , ("U -- C", "s -> string -- (string -- \"a\")", "equal(joinRef($this()), constant(\"\\\"a\\\"\"))")
          , ("C -- F", "s -> (string -- \"a\") -- \"b\"", "and(notEqual(joinRef($this()), constant(\"\\\"a\\\"\")), notEqual(joinRef($this()), constant(\"\\\"b\\\"\")))")
          , ("F -- C", "s -> \"a\" -- (string -- \"a\")", "equal(joinRef($this()), constant(\"\\\"a\\\"\"))")
          , ("C -- C", "s -> (string -- \"a\") -- (string -- \"b\")", "equal(joinRef($this()), constant(\"\\\"b\\\"\"))")
          ] $ \(variant, decl, restriction) ->
        si18_assertEncoding variant (decl ++ "\n") ("c0_s.refToUnique(string);\nc0_s.addConstraint(" ++ restriction ++ ");\n")

case_string_universe_results_need_no_restriction :: Assertion
case_string_universe_results_need_no_restriction =
    forM_ [ ("F ++ C", "s -> \"a\" ++ (string -- \"a\")")
          , ("C ++ C (disjoint exclusions)", "s -> (string -- \"a\") ++ (string -- \"b\")")
          , ("U ++ F", "s -> string ++ \"a\"")
          , ("F ++ U", "s -> \"a\" ++ string")
          , ("U ++ C", "s -> string ++ (string -- \"a\")")
          , ("C ++ U", "s -> (string -- \"a\") ++ string") ] $ \(variant, decl) -> do
        let chocoCode = si18_choco (decl ++ "\n")
        ("c0_s.refToUnique(string);\n" `isInfixOf` chocoCode && not ("c0_s.addConstraint" `isInfixOf` chocoCode))
            @? (variant ++ ": the result is the whole string domain and needs no restriction:\n" ++ chocoCode)

case_empty_string_results_decline_choco_output :: Assertion
case_empty_string_results_decline_choco_output =
    -- (`"a" -- "a"`, `string ** string`, and `string -- string` are rejected by
    -- the clafer type checker before any backend runs, so they are not here)
    forM_ [ ("F -- U", "s -> \"a\" -- string")
          , ("C -- U", "s -> (string -- \"a\") -- string")
          , ("F ** F (disjoint)", "s -> \"a\" ** \"b\"")
          , ("F -- C (subsumed)", "s -> \"a\" -- (string -- \"b\")") ] $ \(variant, decl) ->
        case Map.lookup Choco (si18_results (decl ++ "\n")) of
            Just NoCompilerResult{reason = why} -> ("c0_s" `isInfixOf` why && "empty set of strings" `isInfixOf` why)
                @? (variant ++ ": the decline reason must name c0_s and the empty set, got: " ++ why)
            other -> assertFailure (variant ++ ": an empty string set must decline Choco output, got: " ++ show other)

case_plain_ref_targets_keep_the_pre_18_emission :: Assertion
case_plain_ref_targets_keep_the_pre_18_emission =
    forM_ [ ("clafer", "likes -> Person\n", "c0_likes.refToUnique(c0_Person);\n")
          , ("join path", "heads -> Person.Head *\n", "c0_heads.refToUnique(c0_Head);\n")
          , ("bag of clafers", "likes ->> Person\n", "c0_likes.refTo(c0_Person);\n")
          , ("integer", "n -> integer\n", "c0_n.refToUnique(Int);\n")
          , ("string", "s -> string\n", "c0_s.refToUnique(string);\n")
          ] $ \(variant, decl, expected) -> do
        let chocoCode = si18_choco (si18_personModel ++ decl)
        (expected `isInfixOf` chocoCode && not (".addConstraint(" `isInfixOf` chocoCode))
            @? (variant ++ ": a plain target must keep the pre-#18 emission with no restriction:\n" ++ chocoCode)

case_unsupported_ref_targets_decline_choco_output :: Assertion
case_unsupported_ref_targets_decline_choco_output =
    forM_ [ ("clafer/integer mix", "mixed -> Person ++ 1\n", "c0_mixed")
          , ("string/integer mix", "s -> \"a\" ++ 1\n", "c0_s")
          , ("empty integer set", "e -> 1 -- integer\n", "c0_e")
          ] $ \(variant, decl, uid) -> do
        let results = si18_results (si18_personModel ++ decl)
        case Map.lookup Choco results of
            Just NoCompilerResult{reason = why} ->
                (("Choco output unavailable because the model contains: " `isInfixOf` why) && (uid `isInfixOf` why))
                    @? (variant ++ ": the decline reason must name the unsupported reference " ++ uid ++ ", got: " ++ why)
            other -> assertFailure (variant ++ ": Choco output must be declined for a reference target the backend cannot express, got: " ++ show other)
        (isJust $ Map.lookup Alloy results >>= \r -> case r of { CompilerResult{} -> Just (); _ -> Nothing })
            @? (variant ++ ": the Alloy output must still be generated")

case_nonempty_cards :: Assertion
case_nonempty_cards = do
    claferModels <- positiveClaferModels
    let compiledClafeIrs = foldMap getIR $ map (\(file', model) -> (file', compileOneFragment defaultClaferArgs{keep_unused = True} model)) claferModels
    forM_ compiledClafeIrs (\(file', ir') ->
        let emptys = foldMapIR isEmptyCard ir'
        in when (emptys /= []) $ putStrLn (file' ++ " Error: Contains empty cardinalities after analysis at\n" ++ emptys))
    (andMap ((==[]) . foldMapIR isEmptyCard . snd) compiledClafeIrs
        @? "nonempty card test failed. Files contain empty cardinalities after fully compiling")
    where
        getIR (file', (Right (resultMap))) =
            case Map.lookup Alloy resultMap of
                Just CompilerResult{claferEnv = ClaferEnv{cIr = Just (iMod, _, _)}} -> [(file', iMod)]
                _ -> []
        getIR (_, _) = []
        isEmptyCard (IRClafer (IClafer{_cinPos=(Span (Pos l c) _), _card = Nothing})) = "Line " ++ show l ++ " column " ++ show c ++ "\n"
        isEmptyCard _ = ""

case_stringEqual :: Assertion
case_stringEqual = do
    let strMap = stringMap $ fromJust $ Map.lookup Alloy $ fromRight $ compileOneFragment defaultClaferArgs "A\n    text1 -> string = \"some text\"\n    text2 -> string = \"some text\""
    (Map.size strMap) == 1 @? "Error: same string assigned to differnet numbers!"

-- Sigil-Logic/clafer#29: dotted paths as super types (`h : Person.Head`).
-- The resolver normalizes the path to the abstract clafer it names, so both
-- backends emit ordinary inheritance for it -- exactly what the plain form
-- `h : Head` yields when Head is unique.

si29_resultsWith :: ClaferArgs -> String -> Map.Map ClaferMode CompilerResult
si29_resultsWith args' model = fromRight $ compileOneFragment args'{mode = [Alloy, Choco]} model

si29_alloyWith, si29_chocoWith :: ClaferArgs -> String -> String
si29_alloyWith args' model = outputCode $ fromJust $ Map.lookup Alloy $ si29_resultsWith args' model
si29_chocoWith args' model = outputCode $ fromJust $ Map.lookup Choco $ si29_resultsWith args' model

si29_alloy, si29_choco :: String -> String
si29_alloy = si29_alloyWith defaultClaferArgs
si29_choco = si29_chocoWith defaultClaferArgs

-- | The reproducer from the issue, parameterized over Ella's super type.
si29_personModel :: String -> String
si29_personModel superType = "abstract Person\n    abstract Head\n\nAlice : Person\n    `Head\n\nElla : Person\n    h : " ++ superType ++ "\n"

-- | Two nested abstracts named Head, parameterized over both super types.
si29_twoHeadsModel :: String -> String -> String
si29_twoHeadsModel ellaSuper rexSuper = "abstract Person\n    abstract Head\n\nabstract Animal\n    abstract Head\n\nElla : Person\n    h : " ++ ellaSuper ++ "\n\nRex : Animal\n    h : " ++ rexSuper ++ "\n"

si29_assertContains :: String -> String -> String -> Assertion
si29_assertContains label expected code =
    (expected `isInfixOf` code) @? (label ++ ": expected `" ++ expected ++ "` in:\n" ++ code)

case_si29_dotted_super_emits_inheritance_in_both_backends :: Assertion
case_si29_dotted_super_emits_inheritance_in_both_backends = do
    let alloyCode = si29_alloy $ si29_personModel "Person.Head"
        chocoCode = si29_choco $ si29_personModel "Person.Head"
    si29_assertContains "Alloy" "one sig c0_h extends c0_Head" alloyCode
    si29_assertContains "Alloy (redefinition within Ella)" "{ r_c0_h in r_c0_Head }" alloyCode
    si29_assertContains "Choco" "c0_h.extending(c0_Head);" chocoCode
    (not $ any si18_isBareStatement $ lines chocoCode) @? ("Choco: no bare statement may remain:\n" ++ chocoCode)

case_si29_dotted_super_equals_plain_super :: Assertion
case_si29_dotted_super_equals_plain_super = do
    (si29_alloy (si29_personModel "Person.Head") == si29_alloy (si29_personModel "Head"))
        @? "the Alloy output of `h : Person.Head` must equal that of `h : Head`"
    (si29_choco (si29_personModel "Person.Head") == si29_choco (si29_personModel "Head"))
        @? "the Choco output of `h : Person.Head` must equal that of `h : Head`"

case_si29_dotted_super_disambiguates_same_named_abstracts :: Assertion
case_si29_dotted_super_disambiguates_same_named_abstracts = do
    (not $ compiledCheck $ compileOneFragment defaultClaferArgs $ si29_twoHeadsModel "Head" "Head")
        @? "the plain form `h : Head` must be rejected as ambiguous"
    let alloyCode = si29_alloy $ si29_twoHeadsModel "Person.Head" "Animal.Head"
        chocoCode = si29_choco $ si29_twoHeadsModel "Person.Head" "Animal.Head"
    si29_assertContains "Alloy (Ella)" "one sig c0_h extends c0_Head" alloyCode
    si29_assertContains "Alloy (Rex)" "one sig c1_h extends c1_Head" alloyCode
    si29_assertContains "Choco (Ella)" "c0_h.extending(c0_Head);" chocoCode
    si29_assertContains "Choco (Rex)" "c1_h.extending(c1_Head);" chocoCode

case_si29_dotted_super_walks_direct_children :: Assertion
case_si29_dotted_super_walks_direct_children = do
    let model = "abstract Vehicle\n    abstract Engine\n        abstract Cylinder\n\nCar : Vehicle\n    `Engine\n        c : Vehicle.Engine.Cylinder 2\n"
    si29_assertContains "Alloy" "sig c0_c extends c0_Cylinder" $ si29_alloy model
    si29_assertContains "Choco" "c0_c.extending(c0_Cylinder);" $ si29_choco model

-- gsdlab/clafer#67: a top-level abstract clafer extending a nested abstract
-- clafer is relocated next to its super; the path form must take that route too.
case_si29_dotted_super_relocates_top_level_abstract :: Assertion
case_si29_dotted_super_relocates_top_level_abstract = do
    let model = "abstract Person\n    abstract Head\n\nabstract Bust : Person.Head\n\nBob : Person\n    b : Bust\n"
    si29_assertContains "Alloy" "abstract sig c0_Bust extends c0_Head" $ si29_alloy model
    si29_assertContains "Choco" "c0_Bust.extending(c0_Head);" $ si29_choco model
    si29_assertContains "Choco (extender of the relocated abstract)" "c0_b.extending(c0_Bust);" $ si29_choco model

-- The first segment prefers a top-level clafer: with both a top-level Head
-- and Person.Head in scope, `Head.Eye` names the top-level one's Eye (the
-- plain form `: Head` is ambiguous here, so the path is the only way).  The
-- model is all-abstract, so it is compiled with keep_unused: under the
-- default flags the optimizer would prune every clafer and emit nothing.
case_si29_dotted_super_prefers_top_level_first_segment :: Assertion
case_si29_dotted_super_prefers_top_level_first_segment = do
    let model = "abstract Head\n    abstract Eye\n\nabstract Person\n    abstract Head\n\nabstract BigEye : Head.Eye\n"
        keep  = defaultClaferArgs{keep_unused = True}
    si29_assertContains "Alloy" "abstract sig c0_BigEye extends c0_Eye" $ si29_alloyWith keep model
    si29_assertContains "Choco" "c0_BigEye.extending(c0_Eye);" $ si29_chocoWith keep model

-- The HTML and Graph printers render the path through the resolver's single
-- normalized reference: every segment is linked to the clafer it names, and
-- the inheritance edge is drawn as it is for a plain super type.
case_si29_dotted_super_is_linked_in_html_and_graph :: Assertion
case_si29_dotted_super_is_linked_in_html_and_graph = do
    let results  = fromRight $ compileOneFragment defaultClaferArgs{mode = [Html, Graph]} $ si29_personModel "Person.Head"
        htmlCode = outputCode $ fromJust $ Map.lookup Html results
        dotCode  = outputCode $ fromJust $ Map.lookup Graph results
    si29_assertContains "HTML" "<a href=\"#c0_Person\"><span class=\"reference\">Person</span></a>.<a href=\"#c0_Head\"><span class=\"reference\">Head</span></a>" htmlCode
    (not $ "href=\"#Head\"" `isInfixOf` htmlCode) @? ("HTML: no dangling link to the bare ident may remain:\n" ++ htmlCode)
    si29_assertContains "Graph" "\"c0_Ella\" -> \"c0_Head\"" dotCode

case_si29_dotted_super_errors_are_specific :: Assertion
case_si29_dotted_super_errors_are_specific =
    forM_ [ ("missing child", si29_personModel "Person.Nose"
            , "No superclafer found: Person.Nose ('Nose' is not a child of 'Person')")
          , ("missing grandchild", si29_personModel "Person.Head.Eye"
            , "No superclafer found: Person.Head.Eye ('Eye' is not a child of 'Person.Head')")
          , ("concrete target", "abstract Person\n    abstract Head\n    likes -> Person ?\n\nElla : Person\n    h : Person.likes\n"
            , "No superclafer found: Person.likes ('likes' is not abstract)")
          , ("unknown root", si29_personModel "Nobody.Head"
            , "No superclafer found: Nobody.Head (no clafer named 'Nobody')")
          , ("ambiguous nested root", "abstract Person\n    abstract Head\n        abstract Eye\n\nAlice : Person\n    `Head\n\nElla : Person\n    `Head\n        e : Head.Eye\n"
            , "No superclafer found: Head.Eye ('Head' is ambiguous, start the path at a top-level clafer instead; candidates: c0_Person.c0_Head, c0_Alice.c1_Head, c0_Ella.c2_Head)")
          , ("set expression", "abstract Person\nabstract Animal\n\nElla : (Person ++ Animal)\n"
            , "Only a clafer name or a dotted path of clafer names (e.g., Person.Head) is allowed as a super type") ] $ \(variant, model, expected) ->
        case compileOneFragment defaultClaferArgs model of
            Left errors -> (expected `isInfixOf` show errors) @? (variant ++ ": expected `" ++ expected ++ "` in:\n" ++ show errors)
            Right _     -> assertFailure (variant ++ ": the model is not expected to compile")
