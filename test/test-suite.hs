{-# LANGUAGE TemplateHaskell, DeriveDataTypeable #-}
{-
 Copyright (C) 2013-2017 Luke Brown, Michal Antkiewicz <http://gsd.uwaterloo.ca>

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
import Control.Lens
import Data.Data.Lens
import Data.List
import qualified Data.Map as Map
import Data.Maybe
import Control.Exception (evaluate)
import System.Timeout (timeout)
import Language.Clafer
import Language.Clafer.QNameUID
import Language.Clafer.Intermediate.Intclafer

import Suite.Positive
import Suite.Negative
import Suite.SimpleScopeAnalyser
import Suite.Redefinition
import Suite.TypeSystem
import Functions
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.TH

tg_Main_Test_Suite :: TestTree
tg_Main_Test_Suite = $(testGroupGenerator)

main :: IO ()
main = defaultMain $ testGroup "Tests"
    [ tg_Test_Suite_TypeSystem
    , tg_Test_Suite_Redefinition
    , tg_Main_Test_Suite
    , tg_Test_Suite_Positive
    , tg_Test_Suite_Negative
    , tg_Test_Suite_SimpleScopeAnalyser
    ]

{-
a            // ::a -> c0_a
    b        // ::a::b -> c0_b
b            // ::b -> c1_b
c            // ::c -> c0_c
    d        // ::c::d -> c0_d
         b   // ::c::d::b -> c2_b
d            // ::d -> c1_d
    b        // ::d::b -> c3_b

"b" -> "c0_b", "c1_b", "c2_b", "c3_b"
"d::b" -> "c2_b", "c3_b"
"c::d" -> "c0_d"
"d" -> "c0_d", "c1_d"
"x" -> []

a\n    b\nb\nc\n    d\n         b\nd\n    b
-}
model :: String
model = "a\n    b\nb\nc\n    d\n         b\nd\n    b"

-- Sigil-Logic/clafer#34: the least-qualified-name derivation looped forever
-- on a single-clafer module (`--meta-data` hung); a plain name is now the
-- base case.  The derivation is forced under a timeout so a recurrence
-- fails the suite instead of hanging it.
si34_qNameMaps :: String -> QNameMaps
si34_qNameMaps model' =
    case cIr $ claferEnv $ fromJust $ Map.lookup Alloy $ fromRight $ compileOneFragment defaultClaferArgs model' of
        Just (iModule, _, _) -> deriveQNameMaps iModule
        Nothing              -> error ("si34: no IR for the model " ++ show model')

si34_assertTriples :: String -> String -> [(FQName, PQName, UID)] -> Assertion
si34_assertTriples variant model' expected = do
    forced <- timeout 10000000 $ evaluate $ length $ show triples
    case forced of
        Nothing -> assertFailure (variant ++ ": deriving the qualified-name maps did not terminate within 10s")
        Just _  -> (triples == expected) @? (variant ++ ": expected " ++ show expected ++ " but got " ++ show triples)
  where
    triples = getQNameUIDTriples $ si34_qNameMaps model'

case_si34_single_clafer_least_qualified_name_terminates :: Assertion
case_si34_single_clafer_least_qualified_name_terminates = do
    si34_assertTriples "single concrete clafer" "A\n" [("::A", "A", "c0_A")]
    si34_assertTriples "single clafer with cardinality" "A 2\n" [("::A", "A", "c0_A")]
    si34_assertTriples "single reference clafer" "x -> integer\n" [("::x", "x", "c0_x")]
    si34_assertTriples "single clafer with a constraint" "A\n[ #A = 1 ]\n" [("::A", "A", "c0_A")]
    (getLPQName (si34_qNameMaps "A\n") "c0_A" == Just "A") @? "the least-qualified name of the only clafer is its own name"

-- multi-clafer modules: a nested child is unqualified when unique, a plain
-- name shared by two children stays qualified, and a plain name that merely
-- prefixes another clafer's name is unique (Sigil-Logic/clafer#38)
case_si34_multi_clafer_least_qualified_names_unchanged :: Assertion
case_si34_multi_clafer_least_qualified_names_unchanged = do
    si34_assertTriples "single top-level clafer with a child" "A\n    B\n"
        [("::A", "A", "c0_A"), ("::A::B", "B", "c0_B")]
    si34_assertTriples "two top-level clafers" "A\nB\n"
        [("::A", "A", "c0_A"), ("::B", "B", "c0_B")]
    si34_assertTriples "a plain name shared by two children" "A\n    B\nC\n    B\n"
        [("::A", "A", "c0_A"), ("::A::B", "A::B", "c0_B"), ("::C", "C", "c0_C"), ("::C::B", "C::B", "c1_B")]
    si34_assertTriples "a plain name prefixing another clafer's name (Sigil-Logic/clafer#38)" "A\nAB\n"
        [("::A", "A", "c0_A"), ("::AB", "AB", "c0_AB")]

case_FQMapLookup :: Assertion
case_FQMapLookup = do
    let
        (Just (iModule, _, _)) = cIr $ claferEnv $ fromJust $ Map.lookup Alloy $ fromRight $ compileOneFragment defaultClaferArgs model
        qNameMaps = deriveQNameMaps iModule
    [ "c0_a" ] == getUIDs qNameMaps "::a"  @? "UID for `::a` different from `c0_a`"
    [ "c0_b" ] == getUIDs qNameMaps "::a::b"  @? "UID for `::a::b` different from `c0_b`"
    [ "c1_b" ] == getUIDs qNameMaps "::b"  @? "UID for `::b` different from `c1_b`"
    [ "c0_c" ] == getUIDs qNameMaps "::c"  @? "UID for `::c` different from `c0_c`"
    [ "c0_d" ] == getUIDs qNameMaps "::c::d"  @? "UID for `::c::d` different from `c0_d`"
    [ "c0_d" ] == getUIDs qNameMaps "c::d"  @? "UID for `c::d` different from `c0_d`"
    [ "c2_b" ] == getUIDs qNameMaps "::c::d::b"  @? "UID for `::c::d::b` different from `c2_b`"
    [ "c1_d" ] == getUIDs qNameMaps "::d"  @? "UID for `::d` different from `c1_d`"
    [ "c3_b" ] == getUIDs qNameMaps "::d::b"  @? "UID for `::d::b` different from `c3_d`"
    -- partially-qualified prefix queries return ALL matches, in ascending
    -- order of the reversed-on-`::` keys (pins the prefixFind order contract)
    [ "c1_b", "c0_b", "c3_b", "c2_b" ] == getUIDs qNameMaps "b"  @? "UIDs for `b` different from `c1_b`, `c0_b`, `c3_b`, `c2_b` in that order"
    [ "c3_b", "c2_b" ] == getUIDs qNameMaps "d::b"  @? "UIDs for `d::b` different from `c3_b`, `c2_b` in that order"
    [ "c1_d", "c0_d" ] == getUIDs qNameMaps "d"  @? "UIDs for `d` different from `c1_d`, `c0_d` in that order"
    -- the empty partially-qualified name prefix-matches every clafer
    [ "c0_a", "c1_b", "c0_b", "c3_b", "c2_b", "c0_c", "c1_d", "c0_d" ] == getUIDs qNameMaps ""  @? "UIDs for the empty name different from all eight clafers in ascending reversed-key order"
    -- boundary misses: names adjacent to populated key ranges must not match
    null (getUIDs qNameMaps "x") @? "UID for `x` different from []"
    null (getUIDs qNameMaps "::x") @? "UID for `::x` different from []"
    null (getUIDs qNameMaps "bb") @? "UID for `bb` different from []"

-- Sigil-Logic/clafer#38: a partially qualified name matches whole segments
-- only.  The search used to be character-wise over the reversed keys, so
-- `a` also matched `ab` and `b` matched `bb`; `a` was then judged ambiguous
-- and over-qualified to `::a` in the .cfr-map, and a `.cfr-scope` entry or a
-- claferIG command naming `a` reached `ab` as well.
si38_model :: String
si38_model = "a\n    b\n    bb\nab\nb\n"

case_si38_partially_qualified_names_match_whole_segments :: Assertion
case_si38_partially_qualified_names_match_whole_segments = do
    let qNameMaps = si34_qNameMaps si38_model
    [ "c0_a" ] == getUIDs qNameMaps "a" @? "`a` must not match `ab`"
    [ "c0_ab" ] == getUIDs qNameMaps "ab" @? "`ab` must match only itself"
    [ "c1_b", "c0_b" ] == getUIDs qNameMaps "b" @? "`b` must match `::b` and `::a::b` (ascending reversed-key order) but not `bb`"
    [ "c0_bb" ] == getUIDs qNameMaps "bb" @? "`bb` must match only itself"
    [ "c0_b" ] == getUIDs qNameMaps "a::b" @? "`a::b` must not match `a::bb`"
    [ "c0_bb" ] == getUIDs qNameMaps "a::bb" @? "`a::bb` must match only itself"
    [ "c0_a", "c0_ab", "c1_b", "c0_b", "c0_bb" ] == getUIDs qNameMaps "" @? "the empty name must still match every clafer in ascending reversed-key order"
    null (getUIDs qNameMaps "x") @? "`x` must match nothing"
    si34_assertTriples "least-qualified names" si38_model
        [ ("::a", "a", "c0_a"), ("::ab", "ab", "c0_ab"), ("::a::b", "a::b", "c0_b"), ("::a::bb", "bb", "c0_bb"), ("::b", "::b", "c1_b") ]
    null (getUIDs qNameMaps "x::b") @? "UID for `x::b` different from []"
    null (getUIDs qNameMaps "e") @? "UID for `e` different from []"

case_AllClafersGenerics :: Assertion
case_AllClafersGenerics = do
    let
        (Just (iModule, _, _)) = cIr $ claferEnv $ fromJust $ Map.lookup Alloy $ fromRight $ compileOneFragment defaultClaferArgs model
        allClafers :: [ IClafer ]
        allClafers = universeOn biplate iModule
        allClafersUids = map _uid allClafers
    allClafersUids == [ "c0_a", "c0_b", "c1_b", "c0_c", "c0_d", "c2_b", "c1_d", "c3_b"] @? "All clafers\n" ++ show allClafersUids
