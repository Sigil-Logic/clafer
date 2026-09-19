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
import Language.Clafer.Intermediate.ResolverInheritance (rejectArithmeticAggregateOperands)
import Language.Clafer.Front.AbsClafer (Span(..), noSpan)
import Language.Clafer.Generator.Html (highlightErrors)
import Data.Foldable hiding (forM_)
import Data.Char (isAlpha)
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

-- Sigil-Logic/clafer#31: a parenthesized negative literal as a reference
-- target.  `x -> (-1)` -- the unspaced `-> -1` is a syntax error -- is unary
-- minus over the literal in the IR, which Common.getRefIds had no case for,
-- so every output mode crashed before any backend ran.  The literal now
-- folds to `IInt (-1)` at every consumer of a reference target: getRefIds,
-- the Alloy declaration renderer (Alloy 6.2.0 rejects the general
-- `-1.mul[1]` rendering of unary minus in a declaration but accepts the bare
-- literal, which binds tighter than the set operators), and the Choco
-- classifier (`constant(-1)` on top of the #18 encoding).  Facts are not
-- folded, so the constraint rendering of unary minus is unchanged.

si31_results :: [ClaferMode] -> String -> Map.Map ClaferMode CompilerResult
si31_results modes model = fromRight $ compileOneFragment defaultClaferArgs{mode = modes} model

si31_alloy, si31_choco :: String -> String
si31_alloy model = outputCode $ fromJust $ Map.lookup Alloy $ si31_results [Alloy, Choco] model
si31_choco model = outputCode $ fromJust $ Map.lookup Choco $ si31_results [Alloy, Choco] model

si31_reproducer :: String
si31_reproducer = "x -> (-1)\nassert [ x = -1 ]\n"

case_si31_negative_literal_ref_target_compiles_in_every_mode :: Assertion
case_si31_negative_literal_ref_target_compiles_in_every_mode =
    forM_ [Alloy, Choco, Html, Graph, CVLGraph, JSON] $ \m ->
        case Map.lookup m (si31_results [m] si31_reproducer) of
            Just CompilerResult{} -> return ()
            other -> assertFailure (show m ++ ": expected output for `x -> (-1)`, got " ++ show other)

case_si31_alloy_declares_the_negative_literal_bare :: Assertion
case_si31_alloy_declares_the_negative_literal_bare = do
    let alloyCode = si31_alloy si31_reproducer
    si29_assertContains "declaration" "{ c0_x_ref : one -1 }" alloyCode
    -- the fact keeps the general rendering of unary minus (the corpus is byte-identical)
    si29_assertContains "fact" "assert assertOnLine_2 { (c0_x.@c0_x_ref) = (-1.mul[1]) }" alloyCode

-- Alloy 6.2.0 binds a bare negative literal tighter than the set operators
-- (`one -1 + 1` is {-1, 1}, `one 2 - -1` is {2}, `one -1 - -1` is empty;
-- checked with the 6.2.0 jar), so the folded literal needs no brackets
-- inside a set expression.
case_si31_alloy_folds_negative_literals_inside_set_expressions :: Assertion
case_si31_alloy_folds_negative_literals_inside_set_expressions =
    forM_ [ ("union", "s -> (-1) ++ 1\n", "{ c0_s_ref : one -1 + 1 }")
          , ("enumeration", "s -> (-1), 2\n", "{ c0_s_ref : one -1 + 2 }")
          , ("difference", "s -> 2 -- (-1)\n", "{ c0_s_ref : one 2 - -1 }")
          , ("intersection", "s -> (-1) ** integer\n", "{ c0_s_ref : one -1 & Int }")
          , ("nested", "s -> ((-1) ++ 1) -- 1\n", "{ c0_s_ref : one (-1 + 1) - 1 }")
          , ("double negation", "s -> (-(-1))\n", "{ c0_s_ref : one 1 }")
          , ("bag", "s ->> (-1) 2\n", "{ c0_s_ref : one -1 }")
          ] $ \(variant, decl, expected) -> si29_assertContains variant expected (si31_alloy decl)

case_si31_choco_emits_the_negative_literal_constant :: Assertion
case_si31_choco_emits_the_negative_literal_constant = do
    si18_assertEncoding "reproducer" si31_reproducer
        "c0_x.refToUnique(Int);\nc0_x.addConstraint($in(joinRef($this()), constant(-1)));\n"
    si29_assertContains "assertion" "assert(equal(joinRef(global(c0_x)), constant(-1)));" (si31_choco si31_reproducer)
    forM_ [ ("union", "s -> (-1) ++ 1\n",
             "c0_s.refToUnique(Int);\nc0_s.addConstraint($in(joinRef($this()), union(constant(-1), constant(1))));\n")
          , ("complement", "s -> integer -- (-1)\n",
             "c0_s.refToUnique(Int);\nc0_s.addConstraint(notIn(joinRef($this()), constant(-1)));\n")
          , ("difference", "s -> 2 -- (-1)\n",
             "c0_s.refToUnique(Int);\nc0_s.addConstraint($in(joinRef($this()), diff(constant(2), constant(-1))));\n")
          , ("double negation", "s -> (-(-1))\n",
             "c0_s.refToUnique(Int);\nc0_s.addConstraint($in(joinRef($this()), constant(1)));\n")
          , ("bag", "s ->> (-1) 2\n",
             "c0_s.refTo(Int);\nc0_s.addConstraint($in(joinRef($this()), constant(-1)));\n")
          ] $ \(variant, decl, expected) -> si18_assertEncoding variant decl expected

case_si31_double_negation_equals_the_plain_literal :: Assertion
case_si31_double_negation_equals_the_plain_literal = do
    (si31_alloy "s -> (-(-1))\n" == si31_alloy "s -> 1\n") @? "Alloy: `s -> (-(-1))` must compile as `s -> 1`"
    (si31_choco "s -> (-(-1))\n" == si31_choco "s -> 1\n") @? "Choco: `s -> (-(-1))` must compile as `s -> 1`"

-- A negative real literal folds the same way, so the reference is classified
-- as a reference to a real and both backends decline through the existing
-- unsupported-feature path instead of crashing.
case_si31_negative_real_literal_ref_target_declines_instead_of_crashing :: Assertion
case_si31_negative_real_literal_ref_target_declines_instead_of_crashing = do
    let results = si31_results [Alloy, Choco, Html] "d -> (-1.5)\n"
    forM_ [Alloy, Choco] $ \m -> case Map.lookup m results of
        Just NoCompilerResult{reason = why} -> ("a reference to a real" `isInfixOf` why)
            @? (show m ++ ": the decline reason must name the reference to a real, got: " ++ why)
        other -> assertFailure (show m ++ ": a reference to a negative real literal must decline, got: " ++ show other)
    case Map.lookup Html results of
        Just CompilerResult{} -> return ()
        other -> assertFailure ("Html: expected output for `d -> (-1.5)`, got " ++ show other)

-- The temporal Alloy generator has its own reference-declaration renderer
-- (`AlloyLtl.refType`; HOARDE Codex, PR #35 Cycle 1): a model with a temporal
-- modifier or operator routes `-m alloy` through it, so it must fold the
-- literal the same way as the static generator.
case_si31_temporal_alloy_declares_the_negative_literal_bare :: Assertion
case_si31_temporal_alloy_declares_the_negative_literal_bare =
    forM_ [ ("final modifier", "final marker\nx -> (-1)\n", "{ c0_x_ref : -1 -> State }")
          , ("initially constraint", "x -> (-1)\n[ initially x = -1 ]\n", "{ c0_x_ref : -1 -> State }")
          , ("double negation", "final marker\nx -> (-(-1))\n", "{ c0_x_ref : 1 -> State }")
          ] $ \(variant, model, expected) -> do
        let alloyLtlCode = outputCode $ fromJust $ Map.lookup Alloy $ si31_results [Alloy] model
        si29_assertContains variant expected alloyLtlCode
        (not $ "_ref : -1.mul[" `isInfixOf` alloyLtlCode)
            @? (variant ++ ": the declaration must not use the unary-minus rendering:\n" ++ alloyLtlCode)

-- Sigil-Logic/clafer#33: closed integer arithmetic as a reference target.
-- `x -> (1 - 2)` is the binary operator over two literals in the IR (a
-- reference target is parsed above the arithmetic levels, so only the
-- parentheses reach them), which Common.getRefIds had no case for, so every
-- output mode crashed before any backend ran.  The expression now folds to
-- the literal it denotes at every consumer of a reference target
-- (Common.foldLiteralArithmetic, #31's fold extended with the five operators
-- `+ - * / %` over two integer literals, bottom-up), landing on the #31
-- literal encodings of both backends; arithmetic that does not fold is
-- rejected by the resolver with a positioned semantic error before any
-- consumer runs.  Facts are not folded, so the constraint rendering of the
-- operators is unchanged.

si33_reproducer :: String
si33_reproducer = "x -> (1 - 2)\nassert [ x = -1 ]\n"

case_si33_folded_arithmetic_ref_target_compiles_in_every_mode :: Assertion
case_si33_folded_arithmetic_ref_target_compiles_in_every_mode =
    forM_ [Alloy, Choco, Html, Graph, CVLGraph, JSON] $ \m ->
        case Map.lookup m (si31_results [m] si33_reproducer) of
            Just CompilerResult{} -> return ()
            other -> assertFailure (show m ++ ": expected output for `x -> (1 - 2)`, got " ++ show other)

-- Alloy declares the folded literal bare, as for #31's negative literal (the
-- `util/integer` call forms `1.minus[2]` are rejected in declaration position
-- by 6.2.0).  Division and remainder truncate toward zero -- the semantics of
-- Alloy 6.2.0's `div`/`rem` and of chocosolver's `div`/`mod`, checked with
-- both jars on these operands: `alloy exec` finds every `check` of
-- test/positive/si33-literal-arithmetic-ref-target.als UNSAT and chocosolver
-- -v finds no counterexample, while the floored values -4 and 1 produce
-- counterexamples in both.
case_si33_alloy_declares_the_folded_literal_bare :: Assertion
case_si33_alloy_declares_the_folded_literal_bare =
    forM_ [ ("subtraction", "s -> (1 - 2)\n", "{ c0_s_ref : one -1 }")
          , ("addition", "s -> (2 + 3)\n", "{ c0_s_ref : one 5 }")
          , ("multiplication", "s -> (2 * 3)\n", "{ c0_s_ref : one 6 }")
          , ("division truncates toward zero", "s -> ((-7) / 2)\n", "{ c0_s_ref : one -3 }")
          , ("division by a negative divisor", "s -> (7 / (-2))\n", "{ c0_s_ref : one -3 }")
          , ("remainder takes the dividend's sign", "s -> ((-7) % 2)\n", "{ c0_s_ref : one -1 }")
          , ("remainder with a negative divisor", "s -> (7 % (-2))\n", "{ c0_s_ref : one 1 }")
          , ("nested", "s -> ((1 - 2) * (-(2 + 1)))\n", "{ c0_s_ref : one 3 }")
          , ("negated", "s -> (-(1 - 2))\n", "{ c0_s_ref : one 1 }")
          , ("inside a set expression", "s -> (1 - 2) ++ (2 + 3)\n", "{ c0_s_ref : one -1 + 5 }")
          , ("bag", "s ->> (2 * 3) 2\n", "{ c0_s_ref : one 6 }")
          ] $ \(variant, decl, expected) -> si29_assertContains variant expected (si31_alloy decl)

case_si33_choco_emits_the_folded_constant :: Assertion
case_si33_choco_emits_the_folded_constant = do
    si18_assertEncoding "reproducer" si33_reproducer
        "c0_x.refToUnique(Int);\nc0_x.addConstraint($in(joinRef($this()), constant(-1)));\n"
    forM_ [ ("division truncates toward zero", "s -> ((-7) / 2)\n",
             "c0_s.refToUnique(Int);\nc0_s.addConstraint($in(joinRef($this()), constant(-3)));\n")
          , ("remainder takes the dividend's sign", "s -> ((-7) % 2)\n",
             "c0_s.refToUnique(Int);\nc0_s.addConstraint($in(joinRef($this()), constant(-1)));\n")
          , ("nested", "s -> ((1 - 2) * (-(2 + 1)))\n",
             "c0_s.refToUnique(Int);\nc0_s.addConstraint($in(joinRef($this()), constant(3)));\n")
          , ("inside a set expression", "s -> (1 - 2) ++ (2 + 3)\n",
             "c0_s.refToUnique(Int);\nc0_s.addConstraint($in(joinRef($this()), union(constant(-1), constant(5))));\n")
          , ("bag", "s ->> (2 * 3) 2\n",
             "c0_s.refTo(Int);\nc0_s.addConstraint($in(joinRef($this()), constant(6)));\n")
          ] $ \(variant, decl, expected) -> si18_assertEncoding variant decl expected

case_si33_folded_target_equals_the_plain_literal :: Assertion
case_si33_folded_target_equals_the_plain_literal =
    forM_ [ ("s -> (2 * 3)\n", "s -> 6\n")
          , ("s -> ((-7) / 2)\n", "s -> (-3)\n")
          , ("s -> (1 - 2) ++ (2 + 3)\n", "s -> (-1) ++ 5\n")
          ] $ \(folded, plain) -> do
        (si31_alloy folded == si31_alloy plain) @? ("Alloy: `" ++ folded ++ "` must compile as `" ++ plain ++ "`")
        (si31_choco folded == si31_choco plain) @? ("Choco: `" ++ folded ++ "` must compile as `" ++ plain ++ "`")

-- The temporal Alloy generator has its own declaration renderer
-- (AlloyLtl.refType, #31), which shares the fold.
case_si33_temporal_alloy_declares_the_folded_literal :: Assertion
case_si33_temporal_alloy_declares_the_folded_literal =
    forM_ [ ("final modifier", "final marker\nx -> (1 - 2)\n", "{ c0_x_ref : -1 -> State }")
          , ("inside a set expression", "final marker\nx -> (2 * 3) ++ 1\n", "{ c0_x_ref : 6 + 1 -> State }")
          ] $ \(variant, model, expected) -> do
        let alloyLtlCode = outputCode $ fromJust $ Map.lookup Alloy $ si31_results [Alloy] model
        si29_assertContains variant expected alloyLtlCode
        (not $ any (`isInfixOf` alloyLtlCode) ["_ref : 1.minus[", "_ref : 2.mul["])
            @? (variant ++ ": the declaration must not use the call-form rendering:\n" ++ alloyLtlCode)

-- Facts are not folded: the constraint side renders the operators through
-- genOp (the corpus diff legs check the same across every baseline).  The
-- binary `-` of `a` rendered as `-1.mul[1]` -- the negation of its left
-- operand -- until Sigil-Logic/clafer#41 (case_si41_* below).
case_si33_constraint_arithmetic_is_not_folded :: Assertion
case_si33_constraint_arithmetic_is_not_folded = do
    let model = "a -> integer\nb -> integer\n[ a = (1 - 2) * 3 ]\n[ b = (-7) / 2 + (-7) % 2 ]\n"
    si29_assertContains "Alloy, a" "fact { (c0_a.@c0_a_ref) = ((1.minus[2]).mul[3]) }" (si31_alloy model)
    si29_assertContains "Alloy, b" "fact { (c0_b.@c0_b_ref) = (((-1.mul[7]).div[2]).plus[((-1.mul[7]).rem[2])]) }" (si31_alloy model)
    si29_assertContains "Choco, a" "Constraint(equal(joinRef(global(c0_a)), mul(sub(constant(1), constant(2)), constant(3))));" (si31_choco model)
    si29_assertContains "Choco, b" "Constraint(equal(joinRef(global(c0_b)), add(div(constant(-7), constant(2)), mod(constant(-7), constant(2)))));" (si31_choco model)

-- Arithmetic that does not fold is a positioned semantic error from the
-- resolver (ResolverInheritance.rejectUnfoldableReferenceTargets), located
-- at the innermost sub-expression that fails to fold and naming its
-- operator; the message text is the one test/negative/si33-* models produce.
si33_rule :: String
si33_rule = ".  Arithmetic in a reference target must be closed integer arithmetic that folds to a literal, as in x -> (1 - 2)"

si33_assertRejected :: String -> ClaferArgs -> String -> Pos -> String -> Assertion
si33_assertRejected variant args' model expectedPos detail =
    case compileOneFragment args' model of
        Left [SemanticErr{pos = ErrPos{modelPos = actualPos}, msg = actual}] -> do
            (actual == expected) @? (variant ++ ": expected the message\n" ++ expected ++ "\nbut got\n" ++ actual)
            (actualPos == expectedPos) @? (variant ++ ": expected the error at " ++ show expectedPos ++ " but got " ++ show actualPos)
        Left errors -> assertFailure (variant ++ ": expected exactly one positioned semantic error, got " ++ show errors)
        Right _     -> assertFailure (variant ++ ": the model is not expected to compile")
  where
    expected = "Unsupported reference target: " ++ detail ++ si33_rule

case_si33_unfoldable_arithmetic_ref_targets_are_rejected_with_position :: Assertion
case_si33_unfoldable_arithmetic_ref_targets_are_rejected_with_position =
    forM_ [ ("set negation", "x -> (-(1 ++ 2))\n", Pos 1 7, "the operand of unary '-' is not a numeric literal")
          , ("clafer operand", "y -> integer\nx -> (y + 1)\n", Pos 2 7, "the operands of '+' are not both integer literals")
          , ("negated clafer", "y -> integer\nx -> (-y)\n", Pos 2 7, "the operand of unary '-' is not a numeric literal")
          , ("division by zero", "x -> (1 / 0)\n", Pos 1 7, "'/' divides by zero")
          , ("remainder by zero", "x -> (1 % 0)\n", Pos 1 7, "'%' divides by zero")
          , ("real literals", "x -> (1.5 + 1.5)\n", Pos 1 7, "the operands of '+' are not both integer literals")
          , ("division by zero inside a set expression", "x -> (1 / 0) ++ 5\n", Pos 1 7, "'/' divides by zero")
          , ("innermost offender", "x -> ((1 / 0) + 2)\n", Pos 1 8, "'/' divides by zero")
          , ("innermost offender under a set negation", "x -> (-(1 ++ (2 / 0)))\n", Pos 1 15, "'/' divides by zero")
          ] $ \(variant, model, expectedPos, detail) -> si33_assertRejected variant defaultClaferArgs model expectedPos detail

-- The check runs over the whole module before any target is resolved:
-- resolving `x -> a.b` navigates through `a` and evaluates its
-- reference-target ids, so a later-declared offender would otherwise reach
-- the getRefIds invariant first; offenders are reported in document order;
-- and the check survives --skip-resolver, which skips reference resolution.
case_si33_rejection_precedes_navigation_and_survives_skip_resolver :: Assertion
case_si33_rejection_precedes_navigation_and_survives_skip_resolver = do
    si33_assertRejected "declared after the reference that navigates it" defaultClaferArgs
        "x -> a.b\na -> (1 / 0)\n    b\n" (Pos 2 7) "'/' divides by zero"
    si33_assertRejected "document order" defaultClaferArgs
        "A\n    x -> (1 / 0)\nC -> (2 / 0)\n" (Pos 2 11) "'/' divides by zero"
    si33_assertRejected "skip resolver" defaultClaferArgs{skip_resolver = True}
        "y -> integer\nx -> (y + 1)\n" (Pos 2 7) "the operands of '+' are not both integer literals"
    forM_ [Alloy, Choco, Html, Graph, CVLGraph, JSON] $ \m ->
        si33_assertRejected ("mode " ++ show m) defaultClaferArgs{mode = [m]}
            "x -> (1 / 0)\n" (Pos 1 7) "'/' divides by zero"

-- Sigil-Logic/clafer#36: the HTML and Graph printers restore the parentheses
-- the parser consumed.  `Html.printExp` parenthesizes a sub-expression
-- exactly when the grammar level of its own production is below the level
-- its position admits, and the Graph generator renders its labels and
-- tooltips through the same printer (`Html.genTooltip`), so one model pins
-- both: a constraint nested under a concrete clafer is rendered in the HTML
-- view and in the clafer's Graph tooltip (which carries nested constraints
-- only).  Each generator escapes the text its own way -- the HTML printer
-- emits entities for `< > && || / %` (but the set operators `<:` and `:>`
-- raw) and the Graph generator escapes `&`, `->`, and `->>` in the tooltip
-- -- so the expectations are stated as source text and encoded per generator
-- here (HOARDE Codex, PR #43 Cycle 1: the encoders must cover every branch
-- the printers take for the shapes under test).

si36_results :: String -> Map.Map ClaferMode CompilerResult
si36_results model = fromRight $ compileOneFragment defaultClaferArgs{mode = [Html, Graph]} model

-- the HTML view with its tags removed (a tag starts with `<` and a letter or
-- `/`; the raw `<:` the printer emits for domain restriction is text), and
-- the Graph output as is
si36_htmlText, si36_graph :: String -> String
si36_htmlText model = stripTags $ outputCode $ fromJust $ Map.lookup Html $ si36_results model
  where
    stripTags ('<':c:rest)
      | isAlpha c || c == '/' = stripTags $ drop 1 $ dropWhile (/= '>') rest
    stripTags (c:rest)        = c : stripTags rest
    stripTags []              = []
si36_graph model = outputCode $ fromJust $ Map.lookup Graph $ si36_results model

-- the constraint nested under a clafer with an integer reference `a`
si36_model :: String -> String
si36_model constraint = "A\n    a -> integer\n    [ " ++ constraint ++ " ]\n"

-- the spellings the HTML printer emits for the operators used below: the
-- set operators `<:` and `:>` are raw (checked before the relational `<`
-- and `>`), the rest are entities (the guard-closing transition arrows
-- `]->`/`]->>` among them)
si36_htmlEncode :: String -> String
si36_htmlEncode ('<':':':rest) = "<:" ++ si36_htmlEncode rest
si36_htmlEncode (':':'>':rest) = ":>" ++ si36_htmlEncode rest
si36_htmlEncode ('&':'&':rest) = "&amp;&amp;" ++ si36_htmlEncode rest
si36_htmlEncode ('|':'|':rest) = "&#124;&#124;" ++ si36_htmlEncode rest
si36_htmlEncode ('<':rest)     = "&lt;" ++ si36_htmlEncode rest
si36_htmlEncode ('>':rest)     = "&gt;" ++ si36_htmlEncode rest
si36_htmlEncode ('/':rest)     = "&#47;" ++ si36_htmlEncode rest
si36_htmlEncode ('%':rest)     = "&#37;" ++ si36_htmlEncode rest
si36_htmlEncode (c:rest)       = c : si36_htmlEncode rest
si36_htmlEncode []             = []

-- the escaping the Graph generator applies to a tooltip (`Graph.htmlChars`:
-- `&`, then `->>` before `->`, in production order)
si36_graphEncode :: String -> String
si36_graphEncode ('&':rest)         = "&amp;" ++ si36_graphEncode rest
si36_graphEncode ('-':'>':'>':rest) = "-&gt;&gt;" ++ si36_graphEncode rest
si36_graphEncode ('-':'>':rest)     = "-&gt;" ++ si36_graphEncode rest
si36_graphEncode (c:rest)           = c : si36_graphEncode rest
si36_graphEncode []                 = []

-- the constraint renders as `expected` in both generators, and the lossy
-- master rendering `lossy` (when given) appears in neither; the constraint
-- is nested under the integer-reference clafer of `si36_model`
si36_assertRenders :: String -> String -> String -> Maybe String -> Assertion
si36_assertRenders variant constraint = si36_assertRendersIn variant (si36_model constraint)

-- the same over a given model (its constraint must be nested under a clafer
-- so that it reaches the Graph tooltip)
si36_assertRendersIn :: String -> String -> String -> Maybe String -> Assertion
si36_assertRendersIn variant model expected lossy = do
    let htmlText = si36_htmlText model
        dotCode  = si36_graph model
    si29_assertContains ("HTML, " ++ variant) ("[ " ++ si36_htmlEncode expected ++ " ]") htmlText
    si29_assertContains ("Graph, " ++ variant) ("[ " ++ si36_graphEncode expected ++ " ]") dotCode
    forM_ lossy $ \lossyText -> do
        (not $ si36_htmlEncode lossyText `isInfixOf` htmlText)
            @? ("HTML, " ++ variant ++ ": the lossy rendering `" ++ lossyText ++ "` must be gone:\n" ++ htmlText)
        (not $ si36_graphEncode lossyText `isInfixOf` dotCode)
            @? ("Graph, " ++ variant ++ ": the lossy rendering `" ++ lossyText ++ "` must be gone:\n" ++ dotCode)

case_si36_html_and_graph_restore_the_parentheses_of_the_reproducer :: Assertion
case_si36_html_and_graph_restore_the_parentheses_of_the_reproducer =
    si36_assertRenders "reproducer" "a = (1 - 2) * 3" "a = (1 - 2) * 3" (Just "a = 1 - 2 * 3")

case_si36_html_and_graph_restore_the_parentheses_under_unary_minus :: Assertion
case_si36_html_and_graph_restore_the_parentheses_under_unary_minus =
    si36_assertRenders "unary minus over a parenthesized sum" "a = -(2 + 1)" "a = -(2 + 1)" (Just "a = -2 + 1")

-- One shape per operator family, and the shapes that must NOT gain
-- parentheses: a same-level left operand of a left-associative operator, a
-- unary operator whose operand's level is at or above the one it admits
-- (`!` admits an Exp11, so a comparison under it stays bare), and source
-- parentheses precedence does not need.
case_si36_parentheses_follow_the_grammar_levels :: Assertion
case_si36_parentheses_follow_the_grammar_levels =
    forM_ [ ("same-level right operand of -", "a = 1 - (2 - 3)", "a = 1 - (2 - 3)", Just "a = 1 - 2 - 3")
          , ("same-level left operand of - stays bare", "a = (1 - 2) - 3", "a = 1 - 2 - 3", Nothing)
          , ("lower-level operand of / under unary minus", "a = -(1 + 2) / 3", "a = -(1 + 2) / 3", Just "a = -1 + 2 / 3")
          , ("set union under difference", "a in ((-1) ++ 1) -- 1", "a in ((-1)++1)--1", Just "a in -1++1--1")
          , ("disjunction under &&", "(a = 1 || a = 2) && a != 2", "(a = 1 || a = 2) && a != 2", Just "a = 1 || a = 2 && a != 2")
          , ("negated conjunction", "!(a = 1 && a = 2)", " ! (a = 1 && a = 2)", Just " ! a = 1 && a = 2")
          , ("negated comparison stays bare", "!(a = 4)", " ! a = 4", Nothing)
          , ("implication as the right operand of =>", "a = 1 => (a = 2 => a = 3)", "a = 1 => (a = 2 => a = 3)", Just "a = 1 => a = 2 => a = 3")
          , ("redundant parentheses are not restored", "(a + 1) = 2", "a + 1 = 2", Nothing)
          ] $ \(variant, constraint, expected, lossy) -> si36_assertRenders variant constraint expected lossy

-- The shapes whose spellings the encoders above had to learn (HOARDE Codex,
-- PR #43 Cycle 1): right-nested and mixed domain/range restriction, guarded
-- next and synchronous transitions (a transition inside the guard and as the
-- left operand, both `Exp1`-restricted positions), and the three pattern
-- scopes (`Exp11` bounds).  The model differs per family: the set operators
-- need an abstract type with a subtype, the temporal shapes a state clafer.
case_si36_parentheses_in_set_operator_transition_and_pattern_scope_shapes :: Assertion
case_si36_parentheses_in_set_operator_transition_and_pattern_scope_shapes = do
    let setModel constraint  = "abstract A\nB : A\n\nScope\n    [ " ++ constraint ++ " ]\n"
        stateModel constraint = "State\n    xor flag\n        a\n        b\n        c\n    [ " ++ constraint ++ " ]\n"
    forM_ [ ("right-nested domain restriction", setModel "some (A <: (A <: B))", "some A<:(A<:B)", Just "some A<:A<:B")
          , ("right-nested range restriction", setModel "some (A :> (A :> B))", "some A:>(A:>B)", Just "some A:>A:>B")
          , ("domain restriction under range restriction", setModel "some ((A <: B) :> A)", "some (A<:B):>A", Just "some A<:B:>A")
          , ("left-nested domain then range stays bare", setModel "some (A <: A :> B)", "some A<:A:>B", Nothing)
          , ("guarded next transition", stateModel "(a --> b) -[(b --> c)]-> c", "(a --> b) -[(b --> c)]-> c", Just "a --> b -[b --> c]-> c")
          , ("guarded synchronous transition", stateModel "(a -->> b) -[(b -->> c)]->> c", "(a -->> b) -[(b -->> c)]->> c", Just "a -->> b -[b -->> c]->> c")
          , ("before scope", stateModel "sometime a before (b || c)", "sometime a before (b || c)", Just "before b || c")
          , ("between-and scope", stateModel "always b between (b && c) and (b => c)", "always b between (b && c) and (b => c)", Just "between b && c and b => c")
          , ("after-until scope", stateModel "never c after (b || c) until (a && b)", "never c after (b || c) until (a && b)", Just "after b || c until a && b")
          , ("quantified declarations under &&", setModel "(all x : A | some x) && (some y : A | some y)", "(all x : A | some x) && (some y : A | some y)", Just "all x : A | some x && some y : A | some y")
          ] $ \(variant, model, expected, lossy) -> si36_assertRendersIn variant model expected lossy

-- Sigil-Logic/clafer#41: binary subtraction in constraints and assertions.
-- Common spells unary minus (iMin) and binary subtraction (iSub) as the same
-- string `-`, and the Alloy generators' transformExp rewrote every
-- `IFunExp "-" (e1:_)` -- a binary subtraction included -- to `-1.mul[e1]`,
-- so `[ x = 5 - 2 ]` rendered as `(-1.mul[5])` with the right operand
-- dropped, and `alloy exec` found counterexamples to `assert [ x = 3 ]`
-- (Choco was right: `sub(constant(5), constant(2))`).  The rewrite now
-- matches a single operand only, so a binary `-` reaches genOp's `.minus[`
-- in both the static and the temporal generator, while unary minus keeps
-- its `-1.mul[e]` rendering.  Goals are not emitted by either Alloy
-- generator (an IEGoal renders as the empty string), so a fact and an
-- assertion are the two positions in which a subtraction reaches the
-- renderer.  The temporal generator (AlloyLtl) has its own transformExp; the
-- `final` modifier routes a model through it, as in the #31/#33 tests.

si41_model :: String -> String
si41_model constraint = "x -> integer\ny -> integer\n" ++ constraint ++ "\n"

case_si41_alloy_renders_binary_subtraction_with_minus :: Assertion
case_si41_alloy_renders_binary_subtraction_with_minus =
    forM_ [ ("literal operands", "[ x = 5 - 2 ]", "(c0_x.@c0_x_ref) = (5.minus[2])")
          , ("right-nested", "[ x = 1 - (2 - 3) ]", "(c0_x.@c0_x_ref) = (1.minus[(2.minus[3])])")
          , ("left-nested", "[ x = (1 - 2) - 3 ]", "(c0_x.@c0_x_ref) = ((1.minus[2]).minus[3])")
          , ("under a product", "[ x = (1 - 2) * 3 ]", "(c0_x.@c0_x_ref) = ((1.minus[2]).mul[3])")
          , ("clafer operands", "[ x = y - x ]", "(c0_x.@c0_x_ref) = ((c0_y.@c0_y_ref).minus[(c0_x.@c0_x_ref)])")
          ] $ \(variant, constraint, expected) -> do
        let alloyCode = si31_alloy (si41_model constraint)
        si29_assertContains variant ("fact { " ++ expected ++ " }") alloyCode
        (not $ "-1.mul[" `isInfixOf` alloyCode)
            @? (variant ++ ": a binary `-` must not be rendered as the negation of its left operand:\n" ++ alloyCode)

case_si41_alloy_renders_binary_subtraction_in_assertions :: Assertion
case_si41_alloy_renders_binary_subtraction_in_assertions = do
    let alloyCode = si31_alloy "x -> integer\n[ x = 5 - 2 ]\nassert [ x = 5 - 2 ]\nassert [ x = 3 ]\n"
    si29_assertContains "fact" "fact { (c0_x.@c0_x_ref) = (5.minus[2]) }" alloyCode
    si29_assertContains "assertion" "assert assertOnLine_3 { (c0_x.@c0_x_ref) = (5.minus[2]) }" alloyCode
    si29_assertContains "literal assertion" "assert assertOnLine_4 { (c0_x.@c0_x_ref) = 3 }" alloyCode

case_si41_alloy_still_renders_unary_minus_as_a_product :: Assertion
case_si41_alloy_still_renders_unary_minus_as_a_product =
    forM_ [ ("literal", "[ x = -1 ]", "(c0_x.@c0_x_ref) = (-1.mul[1])")
          , ("sum", "[ x = -(2 + 1) ]", "(c0_x.@c0_x_ref) = (-1.mul[(2.plus[1])])")
          , ("subtraction", "[ x = -(5 - 2) ]", "(c0_x.@c0_x_ref) = (-1.mul[(5.minus[2])])")
          , ("clafer", "[ x = -x ]", "(c0_x.@c0_x_ref) = (-1.mul[(c0_x.@c0_x_ref)])")
          ] $ \(variant, constraint, expected) ->
        si29_assertContains variant ("fact { " ++ expected ++ " }") (si31_alloy (si41_model constraint))

case_si41_temporal_alloy_renders_binary_subtraction_with_minus :: Assertion
case_si41_temporal_alloy_renders_binary_subtraction_with_minus = do
    let alloyLtlCode = si31_alloy "final marker\nx -> integer\ny -> integer\n[ x = 5 - 2 ]\n[ x = -(5 - 2) ]\n[ x = y - x ]\nassert [ x = 5 - 2 ]\n"
    si29_assertContains "fact" "(@r_c0_x.t.@c0_x_ref.t) = (5.minus[2])" alloyLtlCode
    si29_assertContains "unary minus over a subtraction" "(@r_c0_x.t.@c0_x_ref.t) = (-1.mul[(5.minus[2])])" alloyLtlCode
    si29_assertContains "clafer operands" "(@r_c0_x.t.@c0_x_ref.t) = ((@r_c0_y.t.@c0_y_ref.t).minus[(@r_c0_x.t.@c0_x_ref.t)])" alloyLtlCode
    si29_assertContains "assertion" "assert assertOnLine_7 { let t = first | (@r_c0_x.t.@c0_x_ref.t) = (5.minus[2]) }" alloyLtlCode
    (not $ "-1.mul[5]" `isInfixOf` alloyLtlCode)
        @? ("temporal: a binary `-` must not be rendered as the negation of its left operand:\n" ++ alloyLtlCode)

-- The shapes the corpus lacks (HOARDE Codex, PR #45 Cycle 1): a subtraction
-- in a quantified body and in the branches of a numeric if-then-else, and
-- under each LTL operator (`G`, `F`, `X`, `U`, `W`) in the temporal
-- generator.  Two positions are not covered here: `product` gets no Alloy
-- output at all (Language.Clafer declines the whole model, `NoCompilerResult`
-- "the product operator"), and an integer operand of `sum` (`sum (N - 1)`),
-- which used to render the illegal join `temp.1`, is declined by the
-- resolver since Sigil-Logic/clafer#46 (`case_si46_*` below).
case_si41_alloy_renders_subtraction_in_quantifiers_and_if_then_else :: Assertion
case_si41_alloy_renders_subtraction_in_quantifiers_and_if_then_else = do
    let alloyCode = si31_alloy "abstract N ->> integer\nn1 : N = 5\nn2 : N = 2\nx -> integer\nflag ?\n[ all n : N | n - 1 > 0 ]\n[ x = (if some flag then 5 - 2 else 8 - 3) ]\n"
    si29_assertContains "quantified body" "fact { all  n : c0_N | ((n.@c0_N_ref).minus[1]) > 0 }" alloyCode
    si29_assertContains "if-then-else branches" "fact { (c0_x.@c0_x_ref) = ((some c0_flag) => (5.minus[2]) else (8.minus[3])) }" alloyCode
    (not $ "-1.mul[" `isInfixOf` alloyCode)
        @? ("quantifier / if-then-else: a binary `-` must not be rendered as the negation of its left operand:\n" ++ alloyCode)

case_si41_temporal_alloy_renders_subtraction_under_ltl_operators :: Assertion
case_si41_temporal_alloy_renders_subtraction_under_ltl_operators = do
    let alloyLtlCode = si31_alloy "final marker\nx -> integer\nflag ?\n[ G (x = 5 - 2) ]\n[ F (x = 8 - 3) ]\n[ X (x = 9 - 4) ]\n[ (x = 7 - 2) U (x = 6 - 1) ]\n[ (x = 4 - 1) W (x = 3 - 1) ]\n[ G (x = (if some flag then 5 - 2 else 8 - 3)) ]\n"
    forM_ [ ("G", "(infinite and all t':t.*next | (@r_c0_x.t'.@c0_x_ref.t') = (5.minus[2]))")
          , ("F", "(some t':t.*next | (@r_c0_x.t'.@c0_x_ref.t') = (8.minus[3]))")
          , ("X", "(some t.next and let t' = t.next | (@r_c0_x.t'.@c0_x_ref.t') = (9.minus[4]))")
          , ("U", "(some t':t.future | (@r_c0_x.t'.@c0_x_ref.t') = (6.minus[1]) and ( all t'': upto[t, t'] | (@r_c0_x.t''.@c0_x_ref.t'') = (7.minus[2])))")
          , ("W", "(some t':t.future | (@r_c0_x.t'.@c0_x_ref.t') = (3.minus[1]) and ( all t'': upto[t, t'] | (@r_c0_x.t''.@c0_x_ref.t'') = (4.minus[1])))")
          , ("if-then-else under G", "(@r_c0_x.t'.@c0_x_ref.t') = ((some @r_c0_flag.t') => (5.minus[2]) else (8.minus[3]))")
          ] $ \(variant, expected) -> si29_assertContains variant expected alloyLtlCode
    (not $ "-1.mul[" `isInfixOf` alloyLtlCode)
        @? ("LTL operators: a binary `-` must not be rendered as the negation of its left operand:\n" ++ alloyLtlCode)

-- Sigil-Logic/clafer#42: the printer spelled the LTL next operator `X` as
-- `F` (the `LtlX` alternative of `Html.printExp` emitted the eventually
-- operator's spelling), and the HTML view spelled the guard-closing
-- transition arrows with an extra dash, `]-->`/`]-->>` for the source's
-- `]->`/`]->>` (the `html` branch of the guarded alternatives of `printExp`
-- and `printTransition`; the Graph text was right).  Both views render
-- through the same printer, so the si36 helpers pin the fixed spelling in
-- the HTML view and in the Graph tooltip together, and pin the old spelling
-- absent.  The guarded arrows are pinned in both positions the grammar
-- gives them: the transition expression in a constraint (`printExp`) and
-- the clafer-level transition (`printTransition`).

-- a state clafer with three alternatives, over which the temporal
-- constraint is nested (so that it reaches the Graph tooltip)
si42_stateModel :: String -> String
si42_stateModel constraint = "State\n    xor flag\n        a\n        b\n        c\n    [ " ++ constraint ++ " ]\n"

case_si42_html_and_graph_spell_the_next_operator_as_X :: Assertion
case_si42_html_and_graph_spell_the_next_operator_as_X =
    forM_ [ ("reproducer", "X a", "X a", Just "F a")
          , ("negated operand", "X !a", "X  ! a", Just "F  ! a")
          , ("next under eventually and globally", "F X a && G X b", "F X a && G X b", Just "F F a")
          , ("the TrafficLight constraint", "G (a && X !b) => X (!b W a)", "G (a && X  ! b) => X ( ! b W a)", Just "F  ! b")
          , ("the keyword form is unchanged", "next a", "next a", Nothing)
          ] $ \(variant, constraint, expected, lossy) ->
        si36_assertRendersIn variant (si42_stateModel constraint) expected lossy

case_si42_html_and_graph_spell_the_guard_closing_arrows_in_constraints :: Assertion
case_si42_html_and_graph_spell_the_guard_closing_arrows_in_constraints =
    forM_ [ ("guarded next transition", "a -[b]-> c", "a -[b]-> c", Just "a -[b]--> c")
          , ("guarded synchronous transition", "a -[b]->> c", "a -[b]->> c", Just "a -[b]-->> c")
          , ("guard with a negation", "a -[!b]->> c", "a -[ ! b]->> c", Just "a -[ ! b]-->> c")
          ] $ \(variant, constraint, expected, lossy) ->
        si36_assertRendersIn variant (si42_stateModel constraint) expected lossy

case_si42_html_and_graph_spell_the_guard_closing_arrows_of_clafer_transitions :: Assertion
case_si42_html_and_graph_spell_the_guard_closing_arrows_of_clafer_transitions =
    forM_ [ ("guarded next transition", "b -[a]-> c", "b -[a]--> c")
          , ("guarded synchronous transition", "b -[a]->> c", "b -[a]-->> c")
          ] $ \(variant, transition, lossy) -> do
        let model    = "State\n    xor flag\n        a\n        " ++ transition ++ "\n        c\n"
            htmlText = si36_htmlText model
            dotCode  = si36_graph model
        si29_assertContains ("HTML, " ++ variant) (si36_htmlEncode transition) htmlText
        si29_assertContains ("Graph, " ++ variant) (si36_graphEncode transition) dotCode
        (not $ si36_htmlEncode lossy `isInfixOf` htmlText)
            @? ("HTML, " ++ variant ++ ": the extra-dash spelling `" ++ lossy ++ "` must be gone:\n" ++ htmlText)
        (not $ si36_graphEncode lossy `isInfixOf` dotCode)
            @? ("Graph, " ++ variant ++ ": the extra-dash spelling `" ++ lossy ++ "` must be gone:\n" ++ dotCode)

-- Sigil-Logic/clafer#46: `sum` and `product` take a set of integer clafers;
-- an operand that is an integer expression -- arithmetic, a cardinality, a
-- numeric literal -- has no meaning in either backend (chocosolver rejects
-- the generated `sum(sub(N, 1))` with `Cannot sum(int)`; the Alloy
-- generators decomposed the operand as a navigation path, rendering the
-- illegal join `sum temp : N.ref | temp.1` or aborting on `sum 5` and `sum
-- (-N)` with the `[bug]` invariant of `removeright`; the Choco generator
-- aborted on `product (N + 1)`).  The resolver now declines such operands
-- (ResolverInheritance.rejectArithmeticAggregateOperands) with a semantic
-- error positioned at the operand, after name resolution and before the
-- inheritance, reference, and type resolvers, so the decline also holds
-- under --skip-resolver and covers facts, assertions, goals, and temporal
-- constraints alike.  The aggregate outside the
-- arithmetic (`sum N - 1`) is the supported spelling and is unchanged.
-- Set-operator operands (`sum (x ++ y)`, the i239 shape) are set
-- expressions and are left alone: they dereference only their last operand
-- in both backends, which is Sigil-Logic/clafer#47.

si46_model :: String -> String
si46_model constraint = "abstract N ->> integer\nn1 : N = 5\nn2 : N = 2\nx -> integer\n" ++ constraint ++ "\n"

si46_msg :: String -> String -> String
si46_msg op' detail = "Unsupported operand of '" ++ op' ++ "': " ++ detail ++ ", not a set.  The operand of '" ++ op' ++ "' must be a set of integer clafers, as in " ++ op' ++ " N or " ++ op' ++ " N.dref; apply the arithmetic to the aggregate instead, as in " ++ op' ++ " N - 1"

si46_assertRejected :: String -> ClaferArgs -> String -> Pos -> String -> Assertion
si46_assertRejected variant args' model expectedPos expected =
    case compileOneFragment args' model of
        Left [SemanticErr{pos = ErrPos{modelPos = actualPos}, msg = actual}] -> do
            (actual == expected) @? (variant ++ ": expected the message\n" ++ expected ++ "\nbut got\n" ++ actual)
            (actualPos == expectedPos) @? (variant ++ ": expected the error at " ++ show expectedPos ++ " but got " ++ show actualPos)
        Left errors -> assertFailure (variant ++ ": expected exactly one positioned semantic error, got " ++ show errors)
        Right _     -> assertFailure (variant ++ ": the model is not expected to compile")

case_si46_integer_aggregate_operands_are_rejected_with_position :: Assertion
case_si46_integer_aggregate_operands_are_rejected_with_position =
    forM_ [ ("subtraction", "[ x = sum (N - 1) ]", Pos 5 12, si46_msg "sum" "'-' yields a number")
          , ("addition", "[ x = sum (N + 1) ]", Pos 5 12, si46_msg "sum" "'+' yields a number")
          , ("multiplication", "[ x = sum (N * 2) ]", Pos 5 12, si46_msg "sum" "'*' yields a number")
          , ("explicit dereference", "[ x = sum (N.dref - 1) ]", Pos 5 12, si46_msg "sum" "'-' yields a number")
          , ("unary minus", "[ x = sum (-N) ]", Pos 5 12, si46_msg "sum" "unary '-' yields a number")
          , ("cardinality", "[ x = sum (#N) ]", Pos 5 12, si46_msg "sum" "'#' yields an integer")
          , ("integer literal", "[ x = sum 5 ]", Pos 5 11, si46_msg "sum" "an integer literal is an integer")
          , ("real literal (HOARDE Codex, PR #48 Cycle 1)", "[ x = sum 1.5 ]", Pos 5 11, si46_msg "sum" "a real literal is a real")
          , ("nested aggregate (HOARDE Gemini, PR #48 Cycle 1)", "[ x = sum (sum N) ]", Pos 5 12, si46_msg "sum" "'sum' yields a number")
          , ("nested arithmetic over an aggregate", "[ x = sum (sum N - 1) ]", Pos 5 12, si46_msg "sum" "'-' yields a number")
          , ("minimum", "[ x = sum (min N) ]", Pos 5 12, si46_msg "sum" "'min' yields a number")
          , ("maximum under product", "[ x = product (max N) ]", Pos 5 16, si46_msg "product" "'max' yields a number")
          , ("if-then-else over integers", "[ x = sum (if some n1 then 5 else 6) ]", Pos 5 12, si46_msg "sum" "'if-then-else' with a numeric branch yields a number")
          , ("mixed if-then-else, numeric then-branch (HOARDE Codex, PR #48 Cycle 2)", "[ x = sum (if some n1 then 5 else N.dref) ]", Pos 5 12, si46_msg "sum" "'if-then-else' with a numeric branch yields a number")
          , ("mixed if-then-else, numeric else-branch", "[ x = sum (if some n1 then N.dref else 5) ]", Pos 5 12, si46_msg "sum" "'if-then-else' with a numeric branch yields a number")
          , ("if-then-else over reals", "[ x = sum (if some n1 then 1.5 else 2.5) ]", Pos 5 12, si46_msg "sum" "'if-then-else' with a numeric branch yields a number")
          , ("maximum of a real", "[ x = sum (max 1.5) ]", Pos 5 12, si46_msg "sum" "'max' yields a number")
          , ("the primitive type integer (HOARDE Codex, PR #48 Cycle 2)", "[ x = sum integer ]", Pos 5 11, si46_msg "sum" "the primitive type 'integer' is not a set of clafers")
          , ("the primitive type int", "[ x = sum int ]", Pos 5 11, si46_msg "sum" "the primitive type 'int' is not a set of clafers")
          , ("a local declared over integer", "[ all i : integer | sum i > 0 ]", Pos 5 25, si46_msg "sum" "the local 'i' is declared over the primitive type 'integer'")
          , ("a local declared over integer, under product", "[ all i : integer | product i > 0 ]", Pos 5 29, si46_msg "product" "the local 'i' is declared over the primitive type 'integer'")
          , ("a local declared over a dereference (HOARDE Codex, PR #48 Cycle 3)", "[ all i : N.dref | sum i > 0 ]", Pos 5 24, si46_msg "sum" "the local 'i' is declared over a dereference, i.e. values rather than clafers")
          , ("a local declared over a dereference, under product", "[ all i : N.dref | product i > 0 ]", Pos 5 28, si46_msg "product" "the local 'i' is declared over a dereference, i.e. values rather than clafers")
          , ("a numeric local in the then-branch", "[ all i : integer | sum (if some n1 then i else N.dref) > 0 ]", Pos 5 26, si46_msg "sum" "'if-then-else' with a numeric branch yields a number")
          , ("a numeric local in the else-branch", "[ all i : integer | sum (if some n1 then N.dref else i) > 0 ]", Pos 5 26, si46_msg "sum" "'if-then-else' with a numeric branch yields a number")
          , ("a numeric outer local shadowed by nothing, in a nested quantifier", "[ all i : integer | some n : N | sum i > 0 ]", Pos 5 38, si46_msg "sum" "the local 'i' is declared over the primitive type 'integer'")
          , ("product", "[ x = product (N + 1) ]", Pos 5 16, si46_msg "product" "'+' yields a number")
          , ("assertion", "assert [ x = sum (N - 1) ]", Pos 5 19, si46_msg "sum" "'-' yields a number")
          ] $ \(variant, constraint, expectedPos, expected) ->
        si46_assertRejected variant defaultClaferArgs (si46_model constraint) expectedPos expected

case_si46_rejection_holds_in_goals_temporal_constraints_and_without_the_resolver :: Assertion
case_si46_rejection_holds_in_goals_temporal_constraints_and_without_the_resolver = do
    si46_assertRejected "goal" defaultClaferArgs "abstract N ->> integer\nn1 : N = 5\nn2 : N = 2\n<< minimize sum (N - 1) >>\n" (Pos 4 18) (si46_msg "sum" "'-' yields a number")
    si46_assertRejected "product in a goal" defaultClaferArgs "abstract N ->> integer\nn1 : N = 5\nn2 : N = 2\n<< minimize product (N - 1) >>\n" (Pos 4 22) (si46_msg "product" "'-' yields a number")
    si46_assertRejected "temporal" defaultClaferArgs "final marker\nabstract N ->> integer\nn1 : N = 5\nx -> integer\n[ G (x = sum (N - 1)) ]\n" (Pos 5 15) (si46_msg "sum" "'-' yields a number")
    si46_assertRejected "quantified body" defaultClaferArgs "abstract N ->> integer\nn1 : N = 5\nn2 : N = 2\n[ all x : N | sum (x - 1) > 0 ]\n" (Pos 4 20) (si46_msg "sum" "'-' yields a number")
    si46_assertRejected "nested clafer" defaultClaferArgs "abstract N ->> integer\nn1 : N = 5\nn2 : N = 2\nabstract Feature\n    cost -> integer\n    [ cost = sum (N - 1) ]\n" (Pos 6 19) (si46_msg "sum" "'-' yields a number")
    si46_assertRejected "--skip-resolver" defaultClaferArgs{skip_resolver = True} "abstract N ->> integer\nn1 : N = 5\nx -> integer\n[ x = sum (N - 1) ]\n" (Pos 4 12) (si46_msg "sum" "'-' yields a number")
    si46_assertRejected "--flatten-inheritance" defaultClaferArgs{flatten_inheritance = True} "abstract N ->> integer\nn1 : N = 5\nx -> integer\n[ x = sum (N - 1) ]\n" (Pos 4 12) (si46_msg "sum" "'-' yields a number")

-- The offender reported is the earliest in SOURCE order (HOARDE Codex, PR #48
-- Cycle 1): name resolution has already relocated a top-level abstract that
-- extends a nested abstract under its new parent, so a walk in tree order
-- would report the relocated clafer's operand (line 7) before an earlier
-- top-level one (line 5).
case_si46_the_earliest_offender_in_source_order_is_reported :: Assertion
case_si46_the_earliest_offender_in_source_order_is_reported =
    si46_assertRejected "relocated abstract after a top-level offender" defaultClaferArgs
        "abstract N ->> integer\nn1 : N = 5\nabstract Person\n    abstract Head\n[ sum (N + 2) > 0 ]\nabstract Bust : Person.Head\n    [ sum (N - 1) > 0 ]\n"
        (Pos 5 8) (si46_msg "sum" "'+' yields a number")

-- A positioned offender is preferred to one without a span (HOARDE Codex,
-- PR #48 Cycle 2): parsed expressions always carry a span, so this is reached
-- only by a hand-built module, but `noSpan` sorts before every real span and
-- would otherwise be reported as the "earliest" offender.
case_si46_a_positioned_offender_is_preferred_to_one_without_a_span :: Assertion
case_si46_a_positioned_offender_is_preferred_to_one_without_a_span = do
    let sumOf sp opSp = PExp Nothing "" sp (IFunExp "sum" [PExp Nothing "" opSp (IInt 5)])
        positioned = Span (Pos 3 9) (Pos 3 10)
        imodule = IModule "" [ IEConstraint True (sumOf noSpan noSpan)
                             , IEConstraint True (sumOf (Span (Pos 3 1) (Pos 3 20)) positioned) ]
    case rejectArithmeticAggregateOperands imodule of
        Left SemanticErr{pos = actual} -> (actual == positioned) @? ("expected the positioned offender at " ++ show positioned ++ " but got " ++ show actual)
        other -> assertFailure ("expected one positioned semantic error, got " ++ show other)

-- A local declared over a clafer is a set and is not declined (`some i : N |
-- sum i > 0` renders `sum temp : i | temp.@c0_N_ref`), including when it
-- shadows an outer local declared over a primitive type (HOARDE Codex, PR #48
-- Cycle 3): locals are classified in scope.
case_si46_a_local_declared_over_a_clafer_is_not_declined :: Assertion
case_si46_a_local_declared_over_a_clafer_is_not_declined = do
    si29_assertContains "local over a clafer" "fact { some  i : c0_N | (sum temp : i | temp.@c0_N_ref) > 0 }" (si31_alloy (si46_model "[ some i : N | sum i > 0 ]"))
    si29_assertContains "clafer-bound local shadowing a primitive-bound one" "fact { all  i : Int | some  i : c0_N | (sum temp : i | temp.@c0_N_ref) > 0 }" (si31_alloy (si46_model "[ all i : integer | some i : N | sum i > 0 ]"))
    si29_assertContains "the shadowing survives the inner scope only" "fact { all  i : Int | (some  i : c0_N | (sum temp : i | temp.@c0_N_ref) > 0) && (i.@i_ref > 0) }" (si31_alloy (si46_model "[ all i : integer | (some i : N | sum i > 0) && i > 0 ]"))

case_si46_aggregate_outside_the_arithmetic_is_unchanged :: Assertion
case_si46_aggregate_outside_the_arithmetic_is_unchanged = do
    forM_ [ ("sum N - 1", "[ x = sum N - 1 ]", "fact { (c0_x.@c0_x_ref) = ((sum temp : c0_N | temp.@c0_N_ref).minus[1]) }", "Constraint(equal(joinRef(global(c0_x)), sub(sum(global(c0_N)), constant(1))));")
          , ("sum N", "[ x = sum N ]", "fact { (c0_x.@c0_x_ref) = (sum temp : c0_N | temp.@c0_N_ref) }", "Constraint(equal(joinRef(global(c0_x)), sum(global(c0_N))));")
          , ("sum N.dref", "[ x = sum N.dref ]", "fact { (c0_x.@c0_x_ref) = (sum temp : c0_N | temp.@c0_N_ref) }", "Constraint(equal(joinRef(global(c0_x)), sum(global(c0_N))));")
          , ("arithmetic over the set", "[ x = N - 1 ]", "fact { (c0_x.@c0_x_ref) = ((c0_N.@c0_N_ref).minus[1]) }", "Constraint(equal(joinRef(global(c0_x)), sub(joinRef(global(c0_N)), constant(1))));")
          ] $ \(variant, constraint, alloyExpected, chocoExpected) -> do
        si29_assertContains (variant ++ " (Alloy)") alloyExpected (si31_alloy (si46_model constraint))
        si29_assertContains (variant ++ " (Choco)") chocoExpected (si31_choco (si46_model constraint))
    si29_assertContains "product N (Choco)" "Constraint(equal(joinRef(global(c0_x)), product(global(c0_N))));" (si31_choco (si46_model "[ x = product N ]"))
    let chainModel = "abstract Feature\n    cost -> integer\nf1 : Feature\n    [ cost = 5 ]\nf2 : Feature\n    [ cost = 2 ]\nx -> integer\n[ x = sum Feature.cost ]\n"
    si29_assertContains "reference chain (Alloy)" "(sum temp : (c0_Feature.@r_c0_cost) | temp.@c0_cost_ref)" (si31_alloy chainModel)
    si29_assertContains "reference chain (Choco)" "sum(join(global(c0_Feature), c0_cost))" (si31_choco chainModel)
    let alloyLtlCode = si31_alloy "final marker\nabstract N ->> integer\nn1 : N = 5\nx -> integer\n[ G (x = sum N - 1) ]\n"
    si29_assertContains "temporal sum N - 1" ".minus[1]" alloyLtlCode
    si29_assertContains "temporal sum N - 1 aggregate" "sum temp : " alloyLtlCode

case_si46_set_operator_operands_are_not_declined :: Assertion
case_si46_set_operator_operands_are_not_declined =
    forM_ [ ("union (i239)", "x ->> integer 2..*\ny ->> integer 2..*\nz -> integer = sum (x ++ y)\n")
          , ("difference", "abstract N ->> integer\nn1 : N = 5\nn2 : N = 2\nx -> integer\n[ x = sum (N -- n1) ]\n")
          ] $ \(variant, model) ->
        compiledCheck (compileOneFragment defaultClaferArgs{mode = [Alloy, Choco]} model)
            @? (variant ++ ": a set-operator operand of `sum` is a set expression and must still compile (its rendering is Sigil-Logic/clafer#47)")

-- Sigil-Logic/clafer#44: a let-expression (`let x = a in e`, grammar level
-- Exp1) is parsed but was never implemented; on master it reached the
-- desugarer's catch-all for untransformed pattern shapes and aborted the
-- compiler with a `[bug]` message in every mode.  Per the Decision on #44,
-- `Language.Clafer.desugar` declines the earliest `let` of the module with a
-- semantic error positioned at the `let` keyword, before desugaring, naming
-- the binding as written and the inlining that replaces it -- the right-hand
-- side of a binding is a single identifier (a `Name`), so `let x = a in e`
-- is exactly `e` with `a` written for `x`.

si44_assertRejected :: String -> ClaferArgs -> String -> Pos -> String -> String -> Assertion
si44_assertRejected variant args' model expectedPos local bound =
    case compileOneFragment args' model of
        Left [SemanticErr{pos = ErrPos{modelPos = actualPos}, msg = actual}] -> do
            (actual == expected) @? (variant ++ ": expected the message\n" ++ expected ++ "\nbut got\n" ++ actual)
            (actualPos == expectedPos) @? (variant ++ ": expected the error at " ++ show expectedPos ++ " but got " ++ show actualPos)
        Left errors -> assertFailure (variant ++ ": expected exactly one positioned semantic error, got " ++ show errors)
        Right _     -> assertFailure (variant ++ ": the model is not expected to compile")
  where
    expected = "Unsupported expression: 'let " ++ local ++ " = " ++ bound ++ " in ...'.  Clafer does not implement let-expressions; inline the binding instead, writing " ++ bound ++ " wherever the body uses " ++ local

-- a `State` with an `xor flag` of `a` and `b`, and the given constraint on
-- its fifth line
si44_state :: String -> String
si44_state constraint = "State\n    xor flag\n        a\n        b\n    " ++ constraint ++ "\n"

-- the rejected shapes -- a `let` in a constraint, parenthesized, in a
-- quantified body, in an assertion, in a goal -- with the position of the
-- `let`, the binding, and the model with the binding inlined, which is the
-- rewrite the message asks for
si44_shapes :: [(String, String, Pos, String, String, String)]
si44_shapes =
    [ ("constraint", si44_state "[ let x = a in x ]", Pos 5 7, "x", "a", si44_state "[ a ]")
    , ("parenthesized", si44_state "[ (let x = a in x) ]", Pos 5 8, "x", "a", si44_state "[ (a) ]")
    , ("quantified body", "A *\n    b ?\n[ all y : A | let x = y in x.b ]\n", Pos 3 15, "x", "y", "A *\n    b ?\n[ all y : A | y.b ]\n")
    , ("assertion", "A\n    b ?\nassert [ let x = A in some x.b ]\n", Pos 3 10, "x", "A", "A\n    b ?\nassert [ some A.b ]\n")
    , ("goal", "A *\n    b ?\n<< minimize let x = A in # x.b >>\n", Pos 3 13, "x", "A", "A *\n    b ?\n<< minimize # A.b >>\n")
    ]

case_si44_let_expressions_are_rejected_at_the_let_keyword :: Assertion
case_si44_let_expressions_are_rejected_at_the_let_keyword =
    forM_ si44_shapes $ \(variant, model, expectedPos, local, bound, _) ->
        si44_assertRejected variant defaultClaferArgs model expectedPos local bound

-- the module's earliest `let` is the one reported: the first of two
-- constraints, an outer `let` before the one nested in its body, and a
-- nested clafer's constraint before a later top-level one
case_si44_the_earliest_let_is_reported :: Assertion
case_si44_the_earliest_let_is_reported = do
    si44_assertRejected "first of two constraints" defaultClaferArgs
        "A\n    a\n    b\n[ a ]\n[ let x = a in x ]\n[ let y = b in y ]\n" (Pos 5 3) "x" "a"
    si44_assertRejected "outer before nested" defaultClaferArgs
        "A\n    a\n    b\n[ let x = a in let y = b in x ]\n" (Pos 4 3) "x" "a"
    si44_assertRejected "nested clafer before a later top-level constraint" defaultClaferArgs
        "A\n    [ let x = A in x ]\n    a\n[ let y = A in y ]\n" (Pos 2 7) "x" "A"

-- the decline precedes desugaring, so it holds in every mode and under
-- --skip-resolver
case_si44_rejection_holds_in_every_mode_and_under_skip_resolver :: Assertion
case_si44_rejection_holds_in_every_mode_and_under_skip_resolver = do
    forM_ [Alloy, Choco, Html, Graph, CVLGraph, JSON] $ \m ->
        si44_assertRejected ("mode " ++ show m) defaultClaferArgs{mode = [m]}
            (si44_state "[ let x = a in x ]") (Pos 5 7) "x" "a"
    si44_assertRejected "skip resolver" defaultClaferArgs{skip_resolver = True}
        (si44_state "[ let x = a in x ]") (Pos 5 7) "x" "a"

-- the accepted shapes: the inlined twin of every rejected model compiles in
-- both backends, and a `let` in a comment is text, not an expression
case_si44_the_inlined_twins_compile_and_a_let_in_a_comment_is_text :: Assertion
case_si44_the_inlined_twins_compile_and_a_let_in_a_comment_is_text = do
    forM_ si44_shapes $ \(variant, _, _, _, _, twin) ->
        compiledCheck (compileOneFragment defaultClaferArgs{mode = [Alloy, Choco]} twin)
            @? (variant ++ ": the inlined twin is expected to compile:\n" ++ twin)
    compiledCheck (compileOneFragment defaultClaferArgs{mode = [Alloy, Choco]} (si44_state "// [ let x = a in x ]\n    [ a ]"))
        @? "a let in a comment is expected to compile"

-- on a compile error the HTML view falls back to the raw source with the
-- failed span marked, so the `let` is the marked span
case_si44_the_html_view_marks_the_let :: Assertion
case_si44_the_html_view_marks_the_let =
    case compileOneFragment defaultClaferArgs{mode = [Html]} model of
        Left errors -> si29_assertContains "HTML fallback" "<span class=\"error\" title=\"Compiling failed at line 5 column 7...\nUnsupported expression: 'let x = a in ...'." (highlightErrors model errors)
        Right _     -> assertFailure "the model is not expected to compile"
  where
    model = si44_state "[ let x = a in x ]"
