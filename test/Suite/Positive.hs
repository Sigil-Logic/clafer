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
