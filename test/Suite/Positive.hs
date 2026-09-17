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
    forM_ [ ("U ++ F", "x -> integer ++ 1"), ("F ++ U", "x -> 1 ++ integer")
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
          , ("string type in a set expression", "s -> string -- \"a\"\n", "c0_s")
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
