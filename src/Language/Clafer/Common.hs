{-# LANGUAGE DeriveDataTypeable, RankNTypes, KindSignatures, FlexibleContexts #-}
{-
 Copyright (C) 2012-2017 Kacper Bak, Jimmy Liang, Michal Antkiewicz <http://gsd.uwaterloo.ca>

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
module Language.Clafer.Common where

import           Control.Applicative
import           Control.Lens (transformOf, universeOf, universeOn)
import           Data.Char
import           Data.Data.Lens (biplate, uniplate)
import           Data.List
import qualified Data.Map as Map
import           Data.Maybe
import           Data.Tree
import           Prelude

import Language.Clafer.Front.AbsClafer
import Language.Clafer.Intermediate.Intclafer

-- -----------------------------------------------------------------------------
-- basic functions shared by desugarer, analyzer and code generator
type Result = String

transIdent :: PosIdent -> String
transIdent (PosIdent (_, "ref")) = "dref"
transIdent (PosIdent (_, str)) = str

mkIdent :: String -> PosIdent
mkIdent str = PosIdent ((0, 0), str)

mkInteger :: Read a => PosInteger -> a
mkInteger (PosInteger (_, n)) = read n

-- | Returns only [] or [_]
getSuper :: IClafer -> [String]
getSuper claf = case getSuperId <$> _super claf of
    Nothing       -> []
    Just "clafer" -> error "Bug: The identifier 'clafer' should never be returned as super type"
    Just x        -> [x]

-- | Returns a list of any length
getReference :: IClafer -> [String]
getReference c = case _ref <$> _reference c of
    Nothing   -> []
    Just ref' -> getRefIds ref'

-- | Returns a list of any length
getSuperAndReference :: IClafer -> [String]
getSuperAndReference c = (getSuper c) ++ (getReference c)

-- | The UID that a resolved super type names.  'ResolverInheritance.resolveNSuper'
-- normalizes every super type (plain name or dotted path,
-- Sigil-Logic/clafer#29) to a single 'IClaferId', so any other shape here is
-- an internal invariant violation, not a model error.
getSuperId :: PExp -> String
getSuperId (PExp _ _ _ (IClaferId{ _sident = s})) = s
getSuperId pexp' = error $ "[Bug] Commmon.getSuperId called on unexpected argument '" ++ show pexp' ++ "'"

getRefIds :: PExp -> [String]
getRefIds (PExp _ _ _ (IClaferId{ _sident = s})) = [s]
getRefIds (PExp _ _ _ (IFunExp{_op=".", _exps = [_, rightExp]})) = getRefIds rightExp
getRefIds (PExp _ _ _ (IFunExp{_op="++", _exps = [leftExp, rightExp]})) = getRefIds leftExp ++ getRefIds rightExp
getRefIds (PExp _ _ _ (IFunExp{_op=",",  _exps = [leftExp, rightExp]})) = getRefIds leftExp ++ getRefIds rightExp
getRefIds (PExp _ _ _ (IFunExp{_op="--", _exps = [leftExp, rightExp]})) = getRefIds leftExp ++ getRefIds rightExp
getRefIds (PExp _ _ _ (IFunExp{_op="**", _exps = [leftExp, rightExp]})) = getRefIds leftExp ++ getRefIds rightExp
getRefIds (PExp _ _ _ (IInt _)) = [integerType]
getRefIds (PExp _ _ _ (IDouble _)) = [doubleType]
getRefIds (PExp _ _ _ (IReal _)) = [realType]
getRefIds (PExp _ _ _ (IStr _)) = [stringType]
getRefIds (PExp _ _ _ (IDeclPExp{_quant = ISome})) = []
-- Sigil-Logic/clafer#31 and #33: arithmetic in a reference target is
-- admitted only when it is closed integer arithmetic that folds to a
-- literal -- `x -> (-1)` is unary minus over the literal (the grammar has
-- no negative literals) and `x -> (1 - 2)` is the literal -1 -- so the
-- target's type is the folded literal's.  Arithmetic that does not fold
-- (a clafer operand, unary minus over a set expression, arithmetic over
-- real literals, division by zero) is rejected with a positioned error
-- before any consumer of a reference target runs
-- ('Language.Clafer.Intermediate.ResolverInheritance.rejectUnfoldableReferenceTargets',
-- which locates the offending node with 'residualArithmetic'), so reaching
-- the invariant below with it is a pass-ordering bug, not a model error.
getRefIds pexp'@(PExp _ _ _ (IFunExp{_op = op', _exps = exps'}))
  | isArithmeticApp op' exps', isNumericLiteral (_exp folded) = getRefIds folded
  where
    folded = foldLiteralArithmetic pexp'
getRefIds pexp' = error $ "[Bug] Commmon.getRefIds called on unexpected argument '" ++ show pexp' ++ "'"

isNumericLiteral :: IExp -> Bool
isNumericLiteral IInt{}    = True
isNumericLiteral IDouble{} = True
isNumericLiteral IReal{}   = True
isNumericLiteral _         = False

-- | Folds unary minus over a numeric literal into the negative literal,
-- one node at a time: @(-1)@ parses as 'IFunExp' @"-"@ over 'IInt' @1@,
-- which becomes 'IInt' @(-1)@; any other expression is returned unchanged.
-- Shared, through 'foldLiteralArithmetic', by every consumer of a reference
-- target -- 'getRefIds', the Alloy declaration renderers (static,
-- "Language.Clafer.Generator.Alloy", and temporal,
-- "Language.Clafer.Generator.AlloyLtl"), and the Choco classifier -- and
-- applied on its own by the Choco constraint printer, so they agree on the
-- literal (Sigil-Logic/clafer#31).
negateLiteral :: PExp -> PExp
negateLiteral pexp'@PExp{_exp = IFunExp{_op = "-", _exps = [PExp{_exp = operand}]}} = case operand of
  IInt    k -> pexp'{_exp = IInt    (negate k)}
  IDouble d -> pexp'{_exp = IDouble (negate d)}
  IReal   r -> pexp'{_exp = IReal   (negate r)}
  _         -> pexp'
negateLiteral pexp' = pexp'

-- | Folds one closed arithmetic node over two integer literals into the
-- literal it denotes: @(1 - 2)@ parses as 'IFunExp' @"-"@ over 'IInt' @1@
-- and 'IInt' @2@ and becomes 'IInt' @(-1)@ (Sigil-Logic/clafer#33); the
-- five operators of 'arithBinOps' are covered.  Division and remainder
-- truncate toward zero ('quot' and 'rem'), which is what both validators
-- compute for the same operands -- Alloy 6.2.0's @util/integer@ @div@ and
-- @rem@, and chocosolver's @div@ and @mod@, give @(-7) / 2 = -3@ and
-- @(-7) % 2 = -1@ (checked against both jars) -- so a folded target
-- denotes the value a constraint over the same expression evaluates to.
-- Division by zero is not folded: the node is returned unchanged and the
-- resolver rejects it.  Any other expression, including arithmetic over
-- real literals, is returned unchanged.
foldArithmeticLiteral :: PExp -> PExp
foldArithmeticLiteral pexp'@PExp{_exp = IFunExp{_op = op', _exps = [PExp{_exp = IInt a}, PExp{_exp = IInt b}]}}
  | op' == iPlus = literal (a + b)
  | op' == iSub  = literal (a - b)
  | op' == iMul  = literal (a * b)
  | op' == iDiv, b /= 0 = literal (a `quot` b)
  | op' == iRem, b /= 0 = literal (a `rem` b)
  where
    literal k = pexp'{_exp = IInt k}
foldArithmeticLiteral pexp' = pexp'

-- | 'negateLiteral' and 'foldArithmeticLiteral' applied bottom-up over a
-- whole expression, so nested and negated forms fold too: a literal nested
-- in a set expression, @(-1) ++ 1@ or @(1 - 2) ++ 1@, folds in place, a
-- doubly negated literal, @(-(-1))@, folds to @1@, and @((1 - 2) * (-(2 +
-- 1)))@ folds to @3@.  Shared by every consumer of a reference target and
-- by the resolver's rejection of what it leaves behind
-- ('residualArithmetic').
foldLiteralArithmetic :: PExp -> PExp
foldLiteralArithmetic = transformOf uniplate (foldArithmeticLiteral . negateLiteral)

-- | Whether an operator application is arithmetic: unary minus over one
-- operand, or one of the five 'arithBinOps' over two.
isArithmeticApp :: String -> [PExp] -> Bool
isArithmeticApp op' exps' = case exps' of
  [_]    -> op' == iSub
  [_, _] -> op' `elem` arithBinOps
  _      -> False

-- | The innermost arithmetic node that 'foldLiteralArithmetic' leaves in a
-- reference target, if any: unary minus over something other than a
-- numeric literal, a binary operator whose operands are not both integer
-- literals (a clafer, a set expression, a real literal), or a division by
-- zero.  Innermost, so the position and operator reported name the
-- sub-expression that fails to fold rather than the whole target: in
-- @((1 / 0) + 2)@ it is @1 / 0@.  'Nothing' means the target is free of
-- arithmetic once folded and every consumer can take it.
residualArithmetic :: PExp -> Maybe PExp
residualArithmetic target = listToMaybe
  [ node
  | node <- universeOf uniplate $ foldLiteralArithmetic target
  , isArithmeticNode node
  , not $ any isArithmeticNode $ drop 1 $ universeOf uniplate node ]
  where
    isArithmeticNode PExp{_exp = IFunExp{_op = op', _exps = exps'}} = isArithmeticApp op' exps'
    isArithmeticNode _ = False

isEqClaferId :: String -> IClafer -> Bool
isEqClaferId    uid'      claf'    = _uid claf' == uid'

mkPLClaferId :: Span -> CName -> Bool -> ClaferBinding -> PExp
mkPLClaferId pos' id' isTop' bind' = pExpDefPid pos' $ IClaferId "" id' isTop' bind'

pExpDefPidPos :: IExp -> PExp
pExpDefPidPos = pExpDefPid noSpan

pExpDefPid :: Span -> IExp -> PExp
pExpDefPid = pExpDef ""

pExpDef :: String -> Span -> IExp -> PExp
pExpDef = PExp Nothing

isParent :: PExp -> Bool
isParent (PExp _ _ _ (IClaferId _ id' _ _)) = id' == parentIdent
isParent _ = False

isClaferName :: PExp -> Bool
isClaferName (PExp _ _ _ (IClaferId _ id' _ _)) =
  id' `notElem` (specialNames ++ primitiveTypes)
isClaferName _ = False

isClaferName' :: PExp -> Bool
isClaferName' (PExp _ _ _ (IClaferId _ _ _ _)) = True
isClaferName' _ = False

getClaferName :: PExp -> String
getClaferName (PExp _ _ _ (IClaferId _ id' _ _)) = id'
getClaferName _ = ""

isTopLevel :: IClafer -> Bool
isTopLevel IClafer{_parentUID="root"}   = True
isTopLevel IClafer{_parentUID="clafer"} = True
isTopLevel _                            = False

-- -----------------------------------------------------------------------------
-- conversions
elemToClafer :: IElement -> Maybe IClafer
elemToClafer x = case x of
  IEClafer clafer  -> Just clafer
  _  -> Nothing

toClafers :: [IElement] -> [IClafer]
toClafers = mapMaybe elemToClafer


-- -----------------------------------------------------------------------------
-- UID -> IClafer map construction functions

type UIDIClaferMap = Map.Map UID IClafer

createUidIClaferMap :: IModule -> UIDIClaferMap
createUidIClaferMap    iModule  = foldl'
    (\accumMap' claf -> Map.insert (_uid claf) claf accumMap')
    (Map.singleton rootIdent rootClafer)
    (integerClafer : intClafer : stringClafer : doubleClafer : realClafer : booleanClafer : clafer : allClafers)
  where
    allClafers :: [ IClafer ]
    allClafers = universeOn biplate iModule
    defaultModifiers = IClaferModifiers False True True
    rootClafer = IClafer noSpan defaultModifiers (Just $ IGCard False (0, -1)) rootIdent rootIdent "" Nothing Nothing (Just (1,1)) (1, 1) (_mDecls iModule)
    integerClafer = IClafer noSpan defaultModifiers (Just $ IGCard False (0, -1)) integerType integerType "" (Just $ pExpDefPidPos $ IClaferId "" doubleType True $ GlobalBind doubleType) Nothing (Just (1,1)) (1, 1) []
    intClafer = IClafer noSpan defaultModifiers (Just $ IGCard False (0, -1)) "int" "int" "" (Just $ pExpDefPidPos $ IClaferId "" doubleType True $ GlobalBind doubleType) Nothing (Just (1,1)) (1, 1) []
    stringClafer = IClafer noSpan defaultModifiers (Just $ IGCard False (0, -1)) stringType stringType "" Nothing Nothing (Just (1,1)) (1, 1) []
    doubleClafer = IClafer noSpan defaultModifiers (Just $ IGCard False (0, -1)) doubleType doubleType "" (Just $ pExpDefPidPos $ IClaferId "" realType True $ GlobalBind realType) Nothing (Just (1,1)) (1, 1) []
    realClafer = IClafer noSpan defaultModifiers (Just $ IGCard False (0, -1)) realType realType "" Nothing Nothing (Just (1,1)) (1, 1) []
    booleanClafer = IClafer noSpan defaultModifiers (Just $ IGCard False (0, -1)) booleanType booleanType "" Nothing Nothing (Just (1,1)) (1, 1) []
    clafer = IClafer noSpan defaultModifiers (Just $ IGCard False (0, -1)) baseClafer baseClafer "" Nothing Nothing (Just (1,1)) (1, 1) []

-- -----------------------------------------------------------------------------
-- functions using the UID -> IClafer map

findIClafer :: UIDIClaferMap -> UID -> Maybe IClafer
findIClafer    uidIClaferMap    uid' = Map.lookup uid' uidIClaferMap

isTopLevelByUID :: UIDIClaferMap -> UID -> Maybe Bool
isTopLevelByUID    uidIClaferMap    uid' = isTopLevel <$> (findIClafer uidIClaferMap uid')

-- | Finds all super clafers according to sFun
findHierarchy :: (IClafer -> [String]) -> UIDIClaferMap -> IClafer -> [IClafer]
findHierarchy    sFun                     uidIClaferMap    clafer   = case sFun clafer of
  []           -> [clafer]  -- no super and no reference
  supersOrRefs -> let
                    superOrRefClafers = mapMaybe (findIClafer uidIClaferMap) supersOrRefs
                  in
                    clafer
                    : concatMap (findHierarchy sFun uidIClaferMap) superOrRefClafers

-- | Finds hierarchy and transforms each element
mapHierarchy :: (IClafer -> b)
                -> (IClafer -> [String])
                -> UIDIClaferMap
                -> IClafer
                -> [b]
mapHierarchy f sf = (map f.).(findHierarchy sf)

-- | traverse the inheritance hierarchy upwards to find a clafer with the given uidToFind
findUIDinSupers :: UIDIClaferMap -> UID    -> IClafer      -> Maybe IClafer
findUIDinSupers    uidIClaferMap    uidToFind currentClafer =
  if uidToFind == _uid currentClafer
  then return currentClafer
  else do
      superClaferUID <- getSuperId <$> _super currentClafer
      superClafer <- findIClafer uidIClaferMap superClaferUID
      findUIDinSupers uidIClaferMap uidToFind superClafer

-- | traverse the containment hierarchy upwards to find a clafer with the given uidToFind
findUIDinParents :: UIDIClaferMap -> UID    -> IClafer      -> Maybe IClafer
findUIDinParents    uidIClaferMap    uidToFind currentClafer =
  if uidToFind == _uid currentClafer
  then return currentClafer
  else do
    parentClafer <- findIClafer uidIClaferMap $ _parentUID currentClafer
    findUIDinParents uidIClaferMap uidToFind parentClafer

data NestedInheritanceMatch
  = NestedInheritanceMatch
  { _headClafer :: IClafer               -- ^ the clafer for which the match is computed
  , _parentClafer :: IClafer             -- ^ parent of the head clafer
  , _parentsSuperClafer :: Maybe IClafer -- ^ parent of the super of the head clafer
  , _targetClafer :: [IClafer]           -- ^ targets of the head clafer
  , _targetsSuperClafer :: [IClafer] -- ^ super of the target of the head clafer
  , _superClafer :: IClafer              -- ^ super of the head clafer (must exist, otherwise no match)
  , _superClafersParent :: IClafer       -- ^ parent of the super of the head clafer
  , _superClafersTarget :: [IClafer]     -- ^ targets of the super of the head clafer
  } deriving Show

-- | This represents a match of this shape
--
--    superClafersParent
--         /\           <>
--        ?1|             \*
-- parentsSuperClafer      \
--         /\    [=]   superClafer --*-> superClafersTarget
--         *|              /\                     /\
--    parentClafer          |                      |?2
--               <>        *|       [=]   targetsSuperClafer
--                *\        |                     /\
--                  \       |                     *|
--                   headClafer -----*-----> targetClafer
--
-- The clafers are obtained by navigating from the headClafer
-- by following the links marked by *
-- The link marked by ?1 is checked for correctness of nesting (isProperNesting):
-- - _uid parentsSuperClafer == _parentUID superClafer
-- - top-level abstract clafers which extend nested abstract clafers are made into siblings of their supers (see https://github.com/gsdlab/clafer/issues/67)
-- The link marked by ?2 is checked for correctness of redefinition (isProperRefinement):
-- - proper subtyping, bag to set, proper cardinality restriction
-- Redefinition occurs when the name of headClafer is the same as the name of superClafer (isProperRedefinition):
-- - isProperNesting && isProperRefinement && (_ident headClafer) == (_ident superClafer)

isProperNesting :: UIDIClaferMap -> Maybe NestedInheritanceMatch -> Bool
isProperNesting _ Nothing  = True
isProperNesting uidIClaferMap (Just m) =
  (isTopLevel (_superClafer m) && _isAbstract (_superClafer m))
  ||
  (_parentUID (_headClafer m) == _parentUID (_superClafer m))
  ||
  (case _parentsSuperClafer m of
    Nothing                 -> _uid (_parentClafer m) == _uid (_superClafersParent m)
    Just parentsSuperClafer -> isJust $  findUIDinSupers uidIClaferMap (_parentUID $ _superClafer m) parentsSuperClafer
  )
-- ^ assumes that isProperNesting m == True
isProperRefinement :: UIDIClaferMap -> Maybe NestedInheritanceMatch
  -> (Bool,  Bool,  Bool)
isProperRefinement    _                Nothing
  = ( True
    , True
    , True )
isProperRefinement    uidIClaferMap    (Just m)
  = ( properCardinalityRefinement m
    , properBagToSetRefinement m
    , properTargetSubtyping m )
  where
    properCardinalityRefinement NestedInheritanceMatch{_headClafer=hc, _superClafer=hcs}
      = case (_card hc, _card hcs) of
          (Just (hcl, hcu), Just (hcsl, hcsu)) -> hcl >= hcsl && (hcu <= hcsu || hcsu == -1)
          _ -> True
    properBagToSetRefinement NestedInheritanceMatch{_headClafer=hc, _superClafer=hcs}
      = case (_reference hc, _reference hcs) of
          (Just IReference{_isSet=headIsSet}, Just IReference{_isSet=superIsSet}) -> superIsSet <= headIsSet  -- set (True) implies set (True), bag (False) allows bag (False) or set (True)
          _ -> True -- covers 1) only one of them has a ref, and 2) none of them has a ref
    properTargetSubtyping NestedInheritanceMatch{_targetClafer=[targetClafer], _superClafersTarget=[superClafersTarget]}
      = isJust $ findUIDinSupers uidIClaferMap (_uid superClafersTarget) targetClafer
    properTargetSubtyping _
      = True -- covers 1) only one of the target clafers exists, and 2) none of the target clafers exist

-- ^ assumes that isProperNesting m == True and isProperRefinement m == (True, True, True)
isRedefinition :: Maybe NestedInheritanceMatch -> Bool -- ^ whether the name of headClafer is the same as superClafer
isRedefinition Nothing = True
isRedefinition (Just NestedInheritanceMatch{_headClafer=hc, _superClafer=hs})
  =  (_ident hc) == (_ident hs)



-- ^ try to match the nested inheritance pattern
-- ^ only available after the parentUIDs were computed
matchNestedInheritance :: UIDIClaferMap -> IClafer
  -> Maybe NestedInheritanceMatch
matchNestedInheritance    _                    IClafer{_super=Nothing}    = Nothing
matchNestedInheritance    uidIClaferMap        headClafer                 = do
--  traceM $ "matching nested inheritance for " ++ _uid headClafer
  parentClafer       <- findIClafer uidIClaferMap $ _parentUID headClafer
--  traceM $ "matched parentClafer " ++ _uid parentClafer
  superClafer        <- (findIClafer uidIClaferMap) =<< (getSuperId <$> _super headClafer)
--  traceM $ "matched superClafer " ++ _uid superClafer
  superClafersParent <- findIClafer uidIClaferMap $ _parentUID superClafer
--  traceM $ "matched superClafersParent " ++ _uid superClafersParent
  let
    parentsSuperClafer :: Maybe IClafer
    parentsSuperClafer = findIClafer uidIClaferMap =<< getSuperId <$> _super parentClafer  -- safe to use fromJust becuase _super is not isNothing
    targetClafer :: [IClafer]
    targetClafer = case _ref <$> _reference headClafer of
      Just pexp' -> mapMaybe (findIClafer uidIClaferMap) (getRefIds pexp')
      Nothing    -> []
    targetsSuperClafer :: [IClafer]
    targetsSuperClafer = mapMaybe (findIClafer uidIClaferMap) $ map getSuperId $ catMaybes $ map _super targetClafer
    superClafersTarget :: [IClafer]
    superClafersTarget = case _ref <$> _reference superClafer of
      Just pexp' -> mapMaybe (findIClafer uidIClaferMap) (getRefIds pexp')
      Nothing    -> []
--  traceM $ "matched parentsSuperClafer " ++ show (_uid <$> parentsSuperClafer)
--  traceM $ "matched targetClafer " ++ show (_uid <$> targetClafer)
--  traceM $ "matched targetsSuperClafer " ++ show (_uid <$> targetsSuperClafer)
--  traceM $ "matched superClafersTarget " ++ show (_uid <$> superClafersTarget)
  return $ NestedInheritanceMatch
    { _headClafer = headClafer
    , _parentClafer = parentClafer
    , _parentsSuperClafer = parentsSuperClafer
    , _superClafer = superClafer
    , _superClafersParent = superClafersParent
    , _targetClafer = targetClafer
    , _targetsSuperClafer = targetsSuperClafer
    , _superClafersTarget = superClafersTarget
    }


-- -----------------------------------------------------------------------------
-- generic functions

apply :: forall t t1. (t -> t1) -> t -> (t, t1)
apply f x = (x, f x)

-- lists all nodes of a tree (BFS). Take a function to extract subforest
bfs :: forall b b1. (b1 -> (b, [b1])) -> [b1] -> [b]
bfs toNode seed = map rootLabel $ concat $ takeWhile (not.null) $
  iterate (concatMap subForest) $ unfoldForest toNode seed


toNodeShallow :: IClafer -> (IClafer, [IClafer])
toNodeShallow = apply (getSubclafers._elements)


getSubclafers :: [IElement] -> [IClafer]
getSubclafers = mapMaybe elemToClafer


bfsClafers :: [IClafer] -> [IClafer]
bfsClafers clafers = bfs toNodeShallow clafers

lurry :: forall t t1. ([t1] -> t) -> t1 -> t1 -> t
lurry f x y = f [x,y]

fst3 :: forall t t1 t2. (t, t1, t2) -> t
fst3 (a, _, _) = a
snd3 :: forall t t1 t2. (t, t1, t2) -> t1
snd3 (_, b, _) = b
trd3 :: forall t t1 t2. (t, t1, t2) -> t2
trd3 (_, _, c) = c


toTriple :: forall t t1 t2. t -> (t1, t2) -> (t, t1, t2)
toTriple a (b,c) = (a, b, c)

toMTriple :: forall t t1 t2. t -> (t1, t2) -> Maybe (t, t1, t2)
toMTriple a (b,c) = Just (a, b, c)

-- unary operators
iNot :: String
iNot          = "!"

iG :: String
iG          = "G"

iF :: String
iF          = "F"

iX :: String
iX          = "X"

iInitially :: String
iInitially    = "initially"

iFinally :: String
iFinally    = "finally"

iCSet :: String
iCSet         = "#"

iMin :: String
iMin          = "-"

iMaximum :: String
iMaximum  = "max"

iMinimum :: String
iMinimum  = "min"

iMaximize :: String
iMaximize  = "maximize"

iMinimize :: String
iMinimize  = "minimize"

iSumSet :: String
iSumSet  = "sum"

iProdSet :: String
iProdSet  = "product"

unOps :: [String]
unOps = [iNot, iCSet, iMin, iMaximum, iMinimum, iMaximize, iMinimize, iSumSet, iProdSet, iX, iF, iG, iInitially]

-- binary operators
iIff :: String
iIff          = "<=>"

iImpl :: String
iImpl         = "=>"

iOr :: String
iOr           = "||"

iXor :: String
iXor          = "xor"

iAnd :: String
iAnd          = "&&"

iU :: String
iU          = "U"

iW :: String
iW          = "W"

logBinOps :: [String]
logBinOps = [iIff, iImpl, iOr, iXor, iAnd, iU, iW]

iLt :: String
iLt           = "<"

iGt :: String
iGt           = ">"

iEq :: String
iEq           = "="

iLte :: String
iLte          = "<="

iGte :: String
iGte          = ">="

iNeq :: String
iNeq          = "!="

iIn :: String
iIn           = "in"

iNin :: String
iNin          = "not in"

ltlOps :: [String]
ltlOps = [iW, iU, iX, iG, iF, iInitially]

ltlBinOps :: [String]
ltlBinOps = [iW, iU]

ltlUnOps :: [String]
ltlUnOps = [iX, iG, iF, iInitially]

relGenBinOps :: [String]
relGenBinOps = [iLt, iGt, iEq, iLte, iGte, iNeq]

relSetBinOps :: [String]
relSetBinOps = [iIn, iNin]

relBinOps :: [String]
relBinOps = relGenBinOps ++ relSetBinOps

iPlus :: String
iPlus         = "+"

iSub :: String
iSub          = "-"

iMul :: String
iMul          = "*"

iDiv :: String
iDiv          = "/"

iRem :: String
iRem          = "%"

arithBinOps :: [String]
arithBinOps = [iPlus, iSub, iMul, iDiv, iRem]

iUnion :: String
iUnion        = "++"

iDifference :: String
iDifference   = "--"

iIntersection :: String
iIntersection = "**"

iDomain :: String
iDomain       = "<:"

iRange :: String
iRange        = ":>"

iJoin :: String
iJoin         = "."

setBinOps :: [String]
setBinOps = [iUnion, iDifference, iIntersection, iDomain, iRange, iJoin]

binOps :: [String]
binOps = logBinOps ++ relBinOps ++ arithBinOps ++ setBinOps

-- temporal keywords and property patterns

temporalModifiers :: [String]
temporalModifiers = [ "final", "initial" ]

iLet :: String
iLet = "let"

propertyKeywords :: [String]
propertyKeywords =
  [ "never", "sometime", "lonce", "always"
  , "must", "precede", "follow"
  , "initially", "finally"
  , "until", "weakuntil", "eventually", "globally", "next"
  , "before", "after", "between", "and", "after"
  ]

-- ternary operators
iIfThenElse :: String
iIfThenElse   = "ifthenelse"

mkIFunExp :: Span -> String -> [IExp] -> IExp
mkIFunExp _ _ (x:[]) = x
mkIFunExp pos' op' xs = foldl1 (\x y -> IFunExp op' $ map (PExp Nothing "" pos') [x,y]) xs

toLowerS :: String -> String
toLowerS "" = ""
toLowerS (s:ss) = toLower s : ss

-- -----------------------------------------------------------------------------
-- Constants

rootIdent :: String
rootIdent = "root"

rootUID :: String
rootUID = "root"

thisIdent :: String
thisIdent = "this"

parentIdent :: String
parentIdent = "parent"

drefIdent :: String
drefIdent = "dref"

childrenIdent :: String
childrenIdent = "children"

specialNames :: [String]
specialNames = [thisIdent, parentIdent, drefIdent, rootIdent, childrenIdent]

isSpecial :: String -> Bool
isSpecial = flip elem specialNames

stringType :: String
stringType = "string"

intType :: String
intType = "int"

integerType :: String
integerType = "integer"

realType :: String
realType = "real"

doubleType :: String
doubleType = "double"

booleanType :: String
booleanType = "boolean"

baseClafer :: String
baseClafer = "clafer"

modSep :: String
modSep = "\\"

primitiveTypes :: [String]
primitiveTypes = [stringType, intType, integerType, doubleType, realType]

isPrimitive :: String -> Bool
isPrimitive = flip elem primitiveTypes

-- | reserved keywords which cannot be used as clafer identifiers
keywordIdents :: [String]
keywordIdents =
  baseClafer :
  specialNames ++
  primitiveTypes ++
  [ iMaximum, iMinimum, iMaximize, iMinimize, iSumSet, iProdSet ] ++ -- unary operators
  [ iXor, iIn ] ++ -- binary operators
  [ "if", "then", "else" ] ++ -- ternary operators
  [ "no", "not", "some", "one", "all", "disj" ] ++ -- quantifiers
  [ "opt", "mux", "or", "lone" ] ++ -- group cardinalities
  [ "abstract", "enum" ] ++ -- keywords
  temporalModifiers ++ -- temporal
  ltlOps ++ -- LTL
  propertyKeywords ++ -- temp patterns
  [ iLet ]

data GEnv
  = GEnv
  { identCountMap :: Map.Map String Int
  , expCount :: Int
  , stable :: Map.Map UID [[UID]] -- super clafer names of a given clafer
  , sClafers ::[IClafer]          -- all clafers (no going through references)
  , uidClaferMap :: UIDIClaferMap -- the map needs to be re-created everytime IModule is rewritten
  } deriving (Eq, Show)

safeTail :: [a] -> [a]
safeTail [] = []
safeTail (_:xs) = xs
