{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NamedFieldPuns #-}
{-
 Copyright (C) 2012-2017 Kacper Bak, Michal Antkiewicz <http://gsd.uwaterloo.ca>

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
module Language.Clafer.Intermediate.ResolverInheritance where

import           Control.Applicative
import           Control.Lens  ((^.), (&), (%%~), (.~), universeOn, toListOf)
import           Control.Monad
import           Control.Monad.Except
import           Control.Monad.State
import           Data.Maybe
import           Data.Data.Lens (biplate, uniplate)
import           Data.Graph
import           Data.Tree
import           Data.List
import qualified Data.Map as Map
import           Prelude

import           Language.ClaferT
import           Language.Clafer.Common
import           Language.Clafer.Front.AbsClafer
import           Language.Clafer.Intermediate.Intclafer
import           Language.Clafer.Intermediate.ResolverName

-- | Resolve Non-overlapping inheritance
resolveNModule :: (IModule, GEnv) -> Resolve (IModule, GEnv)
resolveNModule (imodule, genv') =
  do
    let
      unresolvedDecls = _mDecls imodule
      allClafers = bfsClafers $ toClafers unresolvedDecls
    resolvedDecls <- mapM (resolveNElement allClafers) unresolvedDecls
    let
      relocatedDecls = relocateTopLevelAbstractToParents resolvedDecls    -- F> Top-level abstract clafer extending a nested abstract clafer <https://github.com/gsdlab/clafer/issues/67> <F
      uidClaferMap' = createUidIClaferMap imodule{_mDecls = relocatedDecls}
    resolvedHierarchyDecls <- mapM (resolveHierarchy uidClaferMap') relocatedDecls
    let
        resolvedHierarchiesIModule = imodule{_mDecls = resolvedHierarchyDecls}
    return
      ( resolvedHierarchiesIModule
      , genv'{ sClafers = bfs toNodeShallow $ toClafers resolvedHierarchyDecls
             , uidClaferMap = createUidIClaferMap resolvedHierarchiesIModule}
      )

resolveNClafer :: [IClafer] -> IClafer -> Resolve IClafer
resolveNClafer allClafers clafer =
  do
    (super', superIClafer')    <- resolveNSuper allClafers $ _super clafer
    -- F> Top-level abstract clafer extending a nested abstract clafer <https://github.com/gsdlab/clafer/issues/67> F>
    let
      parentUID' =
        case superIClafer' of
          (Just superIClafer'') ->
            if _isAbstract clafer && isTopLevel clafer && not (isTopLevel superIClafer'')
            then _parentUID superIClafer''   -- make clafer a sibling of the superIClafer'
            else _parentUID clafer
          Nothing               -> _parentUID clafer
    -- <F Top-level abstract clafer extending a nested abstract clafer <https://github.com/gsdlab/clafer/issues/67> <F
    elements' <- mapM (resolveNElement allClafers) $ _elements clafer
    return $ clafer
      { _super = super'
      , _parentUID = parentUID'
      , _modifiers = IClaferModifiers
          (_isAbstract clafer)
          (_isInitial clafer || (fromMaybe False $ _isInitial <$> superIClafer'))  -- the clafer is declared as initial or inherits it
          (_isFinal clafer || (fromMaybe False $ _isFinal <$> superIClafer'))      -- the clafer is declared as final or inherits it
      , _elements = elements'
      }

-- | Resolve the super type of a clafer to the abstract clafer it names.
--
-- Two shapes reach here from the desugarer: a plain name (@Person@) and a
-- dotted path (@Person.Head@), which the grammar accepts as a join
-- expression and the desugarer leaves as an 'IFunExp' "." chain over
-- 'IClaferId's.  Both are normalized to the single-'IClaferId' form that
-- every downstream consumer of '_super' expects ('getSuperId', the
-- generators, the hierarchy walkers): the 'IClaferId' carries the resolved
-- UID, its 'GlobalBind', and the 'TClafer' type.  Any other shape is a
-- semantic error rather than a silent pass-through -- before
-- Sigil-Logic/clafer#29 the fall-through returned dotted paths unresolved,
-- and both backends then dropped the super without a diagnostic.
resolveNSuper :: [IClafer] -> Maybe PExp -> Resolve (Maybe PExp, Maybe IClafer)
resolveNSuper _ Nothing = return (Nothing, Nothing)
resolveNSuper allClafers (Just (PExp _ pid' pos' superExp)) =
    case superPathIdents superExp of
      Just [id']
        | isPrimitive id' -> throwError $ SemanticErr pos' $ "Primitive types are not allowed as super types: " ++ id'
        | otherwise -> do
            r <- resolveN pos' (filter _isAbstract allClafers) id'
            superClafer' <- case r of
              Just (_, [superClafer'']) -> return superClafer''
              Just _                    -> error $ "[Bug] ResolverInheritance.resolveN returned a non-singleton path for '" ++ id' ++ "'"
              Nothing                   -> throwError $ SemanticErr pos' ("No superclafer found: " ++ id')
            return (Just $ mkSuperPExp (_uid superClafer') superClafer', Just superClafer')
      Just (first : rest) -> do
        superClafer' <- resolveSuperPath pos' allClafers first rest
        return (Just $ mkSuperPExp (_uid superClafer') superClafer', Just superClafer')
      _ -> throwError $ SemanticErr pos' "Only a clafer name or a dotted path of clafer names (e.g., Person.Head) is allowed as a super type"
  where
    mkSuperPExp uid' superClafer' = PExp (Just $ TClafer [uid']) pid' pos' (IClaferId "" uid' (isTopLevel superClafer') (GlobalBind uid'))

-- | The identifiers of a super-type expression, left to right, or 'Nothing'
-- when the expression is not a plain name or a "."-join of plain names.
superPathIdents :: IExp -> Maybe [String]
superPathIdents (IClaferId _ id' _ _) = Just [id']
superPathIdents IFunExp{_op = ".", _exps = [PExp{_exp = l}, PExp{_exp = r}]} = (++) <$> superPathIdents l <*> superPathIdents r
superPathIdents _ = Nothing

-- | Resolve a dotted super-type path @first.rest...@ (Sigil-Logic/clafer#29).
--
-- The first segment names a top-level clafer or, failing that, the unique
-- nested clafer of that name anywhere in the model; every further segment
-- names a direct child of the clafer reached so far; the clafer the whole
-- path reaches must be abstract.  Inherited children are not navigated --
-- the inheritance hierarchy is what this very pass is resolving -- so a path
-- through an extender (@Student.Head@ for a @Head@ declared in @Person@)
-- must be written against the declaring clafer (@Person.Head@) instead.
resolveSuperPath :: Span -> [IClafer] -> String -> [String] -> Resolve IClafer
resolveSuperPath pos' allClafers first rest =
  do
    start  <- resolveStart
    target <- foldM resolveStep start $ zip rest $ map (first :) $ inits rest
    unless (_isAbstract target) $
      noSuperErr $ "'" ++ _ident target ++ "' is not abstract"
    return target
  where
    dotted = intercalate "." (first : rest)
    noSuperErr detail = throwError $ SemanticErr pos' $ "No superclafer found: " ++ dotted ++ " (" ++ detail ++ ")"
    byIdent ident' = filter ((== ident') . _ident)
    resolveStart =
      case byIdent first $ filter isTopLevel allClafers of
        [start] -> return start
        _       -> case byIdent first allClafers of
          [start] -> return start
          []      -> noSuperErr $ "no clafer named '" ++ first ++ "'"
          starts  -> noSuperErr $ "'" ++ first ++ "' is ambiguous, start the path at a top-level clafer instead; candidates: "
                                  ++ intercalate ", " (map (intercalate "." . map _uid . ancestry) starts)
    resolveStep current (ident', prefix) =
      case byIdent ident' $ getSubclafers $ _elements current of
        [next] -> return next
        []     -> noSuperErr $ "'" ++ ident' ++ "' is not a child of '" ++ intercalate "." prefix ++ "'"
        _      -> noSuperErr $ "'" ++ ident' ++ "' is not a unique child of '" ++ intercalate "." prefix ++ "'"
    uidMap = Map.fromList $ map (\c -> (_uid c, c)) allClafers
    ancestry c = maybe [c] ((++ [c]) . ancestry) $ Map.lookup (_parentUID c) uidMap


resolveNElement :: [IClafer] -> IElement -> Resolve IElement
resolveNElement allClafers x = case x of
  IEClafer clafer  -> IEClafer <$> resolveNClafer allClafers clafer
  IEConstraint _ _  -> return x
  IEGoal _ _ -> return x

resolveN :: Span -> [IClafer] -> String -> Resolve (Maybe (String, [IClafer]))
resolveN pos' abstractClafers id' =
  findUnique pos' id' $ map (\x -> (x, [x])) abstractClafers


resolveHierarchy :: UIDIClaferMap -> IElement           -> Resolve IElement
resolveHierarchy    uidClaferMap'    (IEClafer iClafer') = IEClafer <$> (super.traverse.iType.traverse %%~ addHierarchy $ iClafer')
  where
    addHierarchy :: IType      -> Resolve IType
    addHierarchy    (TClafer _) = TClafer <$> checkForLoop (tail $ mapHierarchy _uid getSuper uidClaferMap' iClafer')
    addHierarchy    x           = return x
    checkForLoop :: [String] -> Resolve [String]
    checkForLoop    supers    = case find (_uid iClafer' ==) supers of
                                  Nothing -> return supers
                                  Just _ -> throwError $ SemanticErr (_cinPos iClafer') $ "ResolverInheritance: clafer " ++ _uid iClafer' ++ " inherits from itself"
resolveHierarchy    _                x                   = return x


-- | Resolve overlapping inheritance
resolveOModule :: (IModule, GEnv) -> Resolve (IModule, GEnv)
resolveOModule (imodule, genv') =
  do
    let decls' = _mDecls imodule
    decls'' <- mapM (resolveOElement (defSEnv genv' decls')) decls'
    let imodule' = imodule{_mDecls = decls''}
    return ( imodule'
           , genv'{sClafers = bfs toNodeShallow $ toClafers decls'', uidClaferMap = createUidIClaferMap imodule'})


resolveOClafer :: SEnv -> IClafer -> Resolve IClafer
resolveOClafer env clafer =
  do
    reference' <- resolveOReference env {context = Just clafer} $ _reference clafer
    elements' <- mapM (resolveOElement env {context = Just clafer}) $ _elements clafer
    return $ clafer {_reference = reference', _elements = elements'}


resolveOReference :: SEnv -> Maybe IReference -> Resolve (Maybe IReference)
resolveOReference _   Nothing                      = return Nothing
resolveOReference env (Just (IReference is' mods exp')) = Just <$> IReference is' mods <$> resolvePExp env exp'


-- | Reject every reference target that still contains arithmetic after
-- 'foldLiteralArithmetic' (Sigil-Logic/clafer#33), with a semantic error
-- positioned at the innermost sub-expression that fails to fold
-- ('residualArithmetic').  Closed integer arithmetic folds to the literal
-- it denotes and is taken by every backend (@x -> (1 - 2)@ declares the
-- literal @-1@); anything else -- a clafer operand, unary minus over a set
-- expression, arithmetic over real literals, a division by zero -- has no
-- declaration-position rendering in Alloy 6.2.0 (which rejects the
-- @util/integer@ call forms there) and no chocosolver encoding, and used to
-- reach the @[Bug]@ invariant of 'getRefIds' in every output mode.
--
-- This runs over the whole module before any target is resolved rather
-- than inside 'resolveOReference', for two reasons: resolving one target
-- navigates through other clafers, and that navigation evaluates their
-- reference-target ids ('getSuperAndReference' via @allChildren@), so a
-- later-declared clafer's arithmetic target could reach the invariant
-- before its own turn; and the reference resolver is skipped altogether
-- under @--skip-resolver@, which must not reopen the crash.  The targets
-- are inspected in document order, so the first offending one is reported.
rejectUnfoldableReferenceTargets :: IModule -> Resolve ()
rejectUnfoldableReferenceTargets imodule =
  forM_ (universeOn biplate imodule :: [IClafer]) $ \clafer ->
    forM_ (residualArithmetic =<< _ref <$> _reference clafer) $ \node ->
      throwError $ SemanticErr (_inPos node) $ unfoldableReferenceTargetMsg node

-- | The message for a rejected arithmetic reference target: the failing
-- sub-expression's operator and why it does not fold, then the rule.
unfoldableReferenceTargetMsg :: PExp -> String
unfoldableReferenceTargetMsg node =
  "Unsupported reference target: " ++ detail ++ ".  Arithmetic in a reference target must be closed integer arithmetic that folds to a literal, as in x -> (1 - 2)"
  where
    detail = case _exp node of
      IFunExp{_exps = [_]} -> "the operand of unary '-' is not a numeric literal"
      IFunExp{_op = op', _exps = [_, PExp{_exp = IInt 0}]}
        | op' `elem` [iDiv, iRem] -> "'" ++ op' ++ "' divides by zero"
      IFunExp{_op = op'} -> "the operands of '" ++ op' ++ "' are not both integer literals"
      other -> error $ "[Bug] ResolverInheritance.unfoldableReferenceTargetMsg called on a non-arithmetic node '" ++ show other ++ "'"

-- | Reject every @sum@ or @product@ whose operand is a number rather than a
-- set of clafers (Sigil-Logic/clafer#46): an arithmetic application (@sum (N
-- - 1)@, @sum (-N)@), a cardinality (@sum (#N)@), a nested aggregate or
-- extremum (@sum (sum N)@, @sum (max N)@), an if-then-else with such a branch
-- (@sum (if c then 5 else N.dref)@), a numeric literal (@sum 5@, @sum 1.5@),
-- a primitive type (@sum integer@), or a local declared over a primitive type
-- or a dereference (@all i : integer | sum i > 0@, @all i : N.dref | sum i@),
-- with a semantic error positioned at the operand; locals are classified in
-- scope, so an inner clafer-bound local shadows an outer numeric one.  Both
-- aggregates take a set of integer clafers -- @sum N@, @sum N.dref@, @sum
-- Feature.cost@ -- and neither backend gives another operand a meaning:
-- chocosolver rejects it when type-checking the generated
-- constraints (@Cannot sum(int)@), and the Alloy generators decompose the
-- operand as a navigation path ('removeright' / 'getRight'), rendering @sum
-- (N - 1)@ as the illegal join @sum temp : N.ref | temp.1@ and aborting on
-- the other shapes with the @[bug]@ invariant of @removeright@.  Arithmetic
-- over a set already denotes the arithmetic over its sum in both backends
-- (@N - 1@ is @(sum N) - 1@), so the aggregate belongs outside the
-- arithmetic: @sum N - 1@.  A set operator over clafers (@sum (x ++ y)@,
-- @sum (N -- n1)@) is a set expression and is not declined: the type
-- resolver dereferences it as a whole and both generators aggregate over
-- every member (Sigil-Logic/clafer#47).  A set operator with a dereference
-- or a number among its operands (@sum (x ++ y.dref)@, @sum (x.dref ++
-- y.dref)@, @sum (x ++ 5)@, nested or not) is declined here, positioned at
-- that operand, with the same message and the remedy of writing the set
-- operator over the clafers.
--
-- Like 'rejectUnfoldableReferenceTargets' this runs from
-- 'Language.Clafer.Intermediate.Resolver.resolveModule' after name
-- resolution and before the inheritance, reference, and type resolvers, so
-- it also holds under @--skip-resolver@.  Name resolution has already
-- relocated top-level abstracts under their nested super-types
-- ('relocateTopLevelAbstractToParents'), so tree order is not source order;
-- the offender with the earliest source position is the one reported, and a
-- positioned offender is preferred to one without a span.
rejectArithmeticAggregateOperands :: IModule -> Resolve ()
rejectArithmeticAggregateOperands imodule =
  case sortOn (\(offender, _, _, _) -> (_inPos offender == noSpan, _inPos offender)) offenders of
    (offender, op', detail, remedy) : _ -> throwError $ SemanticErr (_inPos offender) $ arithmeticAggregateOperandMsg op' detail remedy
    []                                  -> return ()
  where
    -- the outermost expressions of the module (constraints, goals,
    -- reference targets, ...), each walked with the locals in scope
    offenders = concatMap (offendersIn Map.empty) (toListOf biplate imodule :: [PExp])

-- | The offending aggregate operands within one expression, carrying the
-- locals in scope with what they range over ('numericDomain'): a quantifier
-- binds its locals for its body only, and an inner declaration of the same
-- name shadows an outer one -- in @all i : integer | some i : N | sum i > 0@
-- the operand is the inner, clafer-bound @i@ and is a set.  Each offender
-- carries the position to report, the aggregate, why it is not a set, and
-- the remedy the message ends with.
offendersIn :: Map.Map String String -> PExp -> [(PExp, String, String, String)]
offendersIn env pexp = here ++ below
  where
    here = [ (offender, op', detail, remedy)
           | IFunExp{_op = op', _exps = [operand]} <- [_exp pexp]
           , op' `elem` [iSumSet, iProdSet]
           , (offender, detail, remedy) <- aggregateOperandOffenders env op' operand ]
    below = case _exp pexp of
      IDeclPExp{_oDecls = decls, _bpexp = body} ->
        concatMap (offendersIn env . _body) decls ++ offendersIn (foldl bind env decls) body
      _ -> concatMap (offendersIn env) (toListOf uniplate pexp)
    bind env' IDecl{_decls = locals, _body = domain} = case numericDomain env' domain of
      Just what -> foldr (`Map.insert` what) env' locals
      Nothing   -> foldr Map.delete env' locals

-- | The offenders within one operand of @sum@ / @product@.  A set operator
-- (Sigil-Logic/clafer#47) is walked down to its operands: each operand that
-- is a dereference (@x ++ y.dref@ -- values rather than clafers) or a number
-- by 'numericOperandIn' (@x ++ 5@) is an offender positioned at itself, with
-- the remedy of writing the set operator over the clafers; a set operator
-- over clafers alone has no offender and is dereferenced as a whole by the
-- type resolver.  Any other operand is an offender when 'numericOperandIn'
-- says so, with the remedy of applying the arithmetic to the aggregate.
aggregateOperandOffenders :: Map.Map String String -> String -> PExp -> [(PExp, String, String)]
aggregateOperandOffenders env op' operand = case _exp operand of
  IFunExp{_op = setOp, _exps = [l, r]} | setOp `elem` setOperators -> concatMap (setOperandOffenders setOp) [l, r]
  _ -> [ (operand, detail, "apply the arithmetic to the aggregate instead, as in " ++ op' ++ " N - 1")
       | Just detail <- [numericOperandIn env operand] ]
  where
    setOperators = [iUnion, iDifference, iIntersection]
    setOperandOffenders setOp leaf = case _exp leaf of
      IFunExp{_op = inner, _exps = [l, r]} | inner `elem` setOperators -> concatMap (setOperandOffenders inner) [l, r]
      IFunExp{_op = ".", _exps = [_, PExp{_exp = IClaferId{_sident = "dref"}}]} ->
        [ (leaf, "within '" ++ setOp ++ "', a dereference yields values rather than clafers", setRemedy setOp) ]
      _ -> [ (leaf, "within '" ++ setOp ++ "', " ++ detail, setRemedy setOp) | Just detail <- [numericOperandIn env leaf] ]
    setRemedy setOp = "the operands of '" ++ setOp ++ "' under '" ++ op' ++ "' must themselves be sets of integer clafers, as in " ++ op' ++ " (x " ++ setOp ++ " y)"

-- | What a quantifier's local ranges over when that is numbers rather than
-- clafers: a primitive type (@all i : integer@), a dereference (@all i :
-- N.dref@, the values of @N@), an outer local already bound over values
-- (@all i : N.dref | all k : i@), or a set operator with such an operand
-- (@all i : (x.dref ++ y.dref)@, reachable with @--skip-resolver@; before,
-- such a local reached the Alloy generator and aborted it -- HOARDE Codex,
-- PR #52 Cycles 1 and 2).  'Nothing' for a set of clafers.
numericDomain :: Map.Map String String -> PExp -> Maybe String
numericDomain env PExp{_exp = IClaferId{_sident = name}}
  | Just what <- Map.lookup name env = Just what
  | name `elem` primitiveTypes = Just $ "the primitive type '" ++ name ++ "'"
numericDomain _ PExp{_exp = IFunExp{_op = ".", _exps = [_, PExp{_exp = IClaferId{_sident = "dref"}}]}} =
  Just "a dereference, i.e. values rather than clafers"
numericDomain env PExp{_exp = IFunExp{_op = op', _exps = [l, r]}}
  | op' `elem` [iUnion, iDifference, iIntersection]
  , Just what <- numericDomain env l `mplus` numericDomain env r
  = Just $ "a set operator over " ++ what
numericDomain _ _ = Nothing

-- | Why an operand of @sum@ / @product@ is a number rather than a set, if
-- its shape -- or, for a local, its declaration in scope -- says so: the
-- phrase completes @Unsupported operand of 'sum': <phrase>, not a set@.
-- Arithmetic, extrema, and aggregates may be real- or integer-valued, so
-- they "yield a number"; a cardinality and an integer literal are integers,
-- a real literal is a real.  'Nothing' for every other shape -- a clafer, a
-- navigation, a set operator, a local declared over clafers -- which the
-- later resolvers and the generators take as before.
numericOperandIn :: Map.Map String String -> PExp -> Maybe String
numericOperandIn env PExp{_exp = IClaferId{_sident = name}}
  | Just what <- Map.lookup name env = Just $ "the local '" ++ name ++ "' is declared over " ++ what
  | name `elem` primitiveTypes = Just $ "the primitive type '" ++ name ++ "' is not a set of clafers"
numericOperandIn env PExp{_exp = IFunExp{_op = op', _exps = exps'}}
  | isArithmeticApp op' exps' = Just $ case exps' of
      [_] -> "unary '-' yields a number"
      _   -> "'" ++ op' ++ "' yields a number"
  | op' == iCSet = Just "'#' yields an integer"
  | op' `elem` [iSumSet, iProdSet, iMinimum, iMaximum] = Just $ "'" ++ op' ++ "' yields a number"
  | op' == iIfThenElse, [_, thenBranch, elseBranch] <- exps'
  , isJust (numericOperandIn env thenBranch) || isJust (numericOperandIn env elseBranch)
  = Just "'if-then-else' with a numeric branch yields a number"
numericOperandIn _ PExp{_exp = IInt _}    = Just "an integer literal is an integer"
numericOperandIn _ PExp{_exp = IDouble _} = Just "a real literal is a real"
numericOperandIn _ PExp{_exp = IReal _}   = Just "a real literal is a real"
numericOperandIn _ _ = Nothing

-- | The message for a rejected aggregate operand: what the operand is and
-- why it is not a set, then the rule and the remedy with the shape to use
-- instead.
arithmeticAggregateOperandMsg :: String -> String -> String -> String
arithmeticAggregateOperandMsg op' detail remedy =
  "Unsupported operand of '" ++ op' ++ "': " ++ detail ++ ", not a set.  The operand of '" ++ op' ++ "' must be a set of integer clafers, as in " ++ op' ++ " N or " ++ op' ++ " N.dref; " ++ remedy


resolveOElement :: SEnv -> IElement -> Resolve IElement
resolveOElement env x = case x of
  IEClafer clafer  -> IEClafer <$> resolveOClafer env clafer
  IEConstraint _ _ -> return x
  IEGoal _ _ -> return x


-- | Resolve inherited and default cardinalities
analyzeModule :: (IModule, GEnv) -> IModule
analyzeModule (imodule, genv') =
  imodule{_mDecls = map (analyzeElement (defSEnv genv' decls')) decls'}
  where
  decls' = _mDecls imodule


analyzeClafer :: SEnv -> IClafer -> IClafer
analyzeClafer env clafer =
  clafer' {_elements = map (analyzeElement env {context = Just clafer'}) $
           _elements clafer'}
  where
  clafer' = clafer {_gcard = analyzeGCard env clafer,
                    _card  = analyzeCard  env clafer}


-- only for non-overlapping
analyzeGCard :: SEnv -> IClafer -> Maybe IGCard
analyzeGCard env clafer = gcard' `mplus` (Just $ IGCard False (0, -1))
  where
  gcard'
    | isNothing $ _super clafer = _gcard clafer
    | otherwise                 = listToMaybe $ mapMaybe _gcard $ findHierarchy getSuper (uidClaferMap $ genv env) clafer


analyzeCard :: SEnv -> IClafer -> Maybe Interval
analyzeCard env clafer = _card clafer `mplus` Just card'
  where
  card'
    | _isAbstract clafer = (0, -1)
    | (isJust $ context env) && pGcard == (0, -1)
      || (isTopLevel clafer) = (1, 1)
    | otherwise = (0, 1)
  pGcard = _interval $ fromJust $ _gcard $ fromJust $ context env

analyzeElement :: SEnv -> IElement -> IElement
analyzeElement env x = case x of
  IEClafer clafer  -> IEClafer $ analyzeClafer env clafer
  IEConstraint _ _ -> x
  IEGoal _ _ -> x

-- | Expand inheritance
resolveEModule :: (IModule, GEnv) -> (IModule, GEnv)
resolveEModule (imodule, genv') = (imodule', newGenv)
  where
  decls' = _mDecls imodule
  imodule' = imodule{_mDecls = decls''}
  newGenv = genv''{uidClaferMap = createUidIClaferMap imodule'}
  (decls'', genv'') = runState (mapM (resolveEElement []
                                    (unrollableModule imodule)
                                    False decls') decls') genv'

-- -----------------------------------------------------------------------------
unrollableModule :: IModule -> [String]
unrollableModule imodule = getDirUnrollables $
  mapMaybe unrollabeDeclaration $ _mDecls imodule

unrollabeDeclaration :: IElement -> Maybe (String, [String])
unrollabeDeclaration x = case x of
  IEClafer clafer -> if _isAbstract clafer
                        then Just (_uid clafer, unrollableClafer clafer)
                        else Nothing
  IEConstraint _ _ -> Nothing
  IEGoal _ _ -> Nothing

unrollableClafer :: IClafer -> [String]
unrollableClafer clafer = (getSuper clafer) ++ deps
  where
  deps = (toClafers $ _elements clafer) >>= unrollableClafer


getDirUnrollables :: [(String, [String])] -> [String]
getDirUnrollables dependencies = (filter isUnrollable $ map (map v2n) $
                                  map flatten (scc graph)) >>= map fst3
  where
  (graph, v2n, _) = graphFromEdges $ map (\(c, ss) -> (c, c, ss)) dependencies
  isUnrollable [x] = fst3 x `elem` trd3 x
  isUnrollable _ = True

-- -----------------------------------------------------------------------------
resolveEClafer :: MonadState GEnv m => [String] -> [String] -> Bool -> [IElement] -> IClafer -> m IClafer
resolveEClafer predecessors unrollables absAncestor declarations clafer = do
  uidClaferMap' <- gets uidClaferMap
  clafer' <- renameClafer absAncestor (_parentUID clafer) clafer
  let predecessors' = _uid clafer' : predecessors
  (sElements, super', superList) <-
      resolveEInheritance predecessors' unrollables absAncestor declarations
        (findHierarchy getSuper uidClaferMap' clafer)
  let sClafer = Map.fromList $ zip (map _uid superList) $ repeat [predecessors']
  modify (\e -> e {stable = Map.delete "clafer" $
                            Map.unionWith ((nub.).(++)) sClafer $
                            stable e})
  elements' <-
      mapM (resolveEElement predecessors' unrollables absAncestor declarations)
            $ _elements clafer
  return $ clafer' {_super = super', _elements = elements' ++ sElements}

renameClafer :: MonadState GEnv m => Bool -> UID -> IClafer -> m IClafer
renameClafer False _ clafer = return clafer
renameClafer True  puid clafer = renameClafer' puid clafer

renameClafer' :: MonadState GEnv m => UID -> IClafer -> m IClafer
renameClafer' puid clafer = do
  let claferIdent = _ident clafer
  identCountMap' <- gets identCountMap
  let count = Map.findWithDefault 0 claferIdent identCountMap'
  modify (\e -> e { identCountMap = Map.alter (\_ -> Just (count+1)) claferIdent identCountMap' } )
  return $ clafer { _uid = genId claferIdent count, _parentUID = puid }

genId :: String -> Int -> String
genId id' count = concat ["c", show count, "_",  id']

resolveEInheritance :: MonadState GEnv m => [String] -> [String] -> Bool -> [IElement] -> [IClafer]  -> m ([IElement], Maybe PExp, [IClafer])
resolveEInheritance predecessors unrollables absAncestor declarations allSuper = do
    let superList = (if absAncestor then id else tail) allSuper
    let unrollSuper = filter (\s -> _uid s `notElem` unrollables) $ tail allSuper
    elements' <-
        mapM (resolveEElement predecessors unrollables True declarations) $
             unrollSuper >>= _elements

    let super' = case (`elem` unrollables) <$> getSuper clafer of
                    [True] -> _super clafer
                    _      ->  Nothing
    return (elements', super', superList)
  where
  clafer = head allSuper

resolveEElement :: MonadState GEnv m => [String] -> [String] -> Bool -> [IElement] -> IElement -> m IElement
resolveEElement predecessors unrollables absAncestor declarations x = case x of
  IEClafer clafer  -> if _isAbstract clafer then return x else IEClafer `liftM`
    resolveEClafer predecessors unrollables absAncestor declarations clafer
  IEConstraint _ _  -> return x
  IEGoal _ _ -> return x

-- -----------------------------------------------------------------------------

resolveRedefinition :: (IModule, GEnv) -> Resolve IModule
resolveRedefinition    (iModule, _)  =
  if (not $ null improperClafers)
    then throwError $ SemanticErr noSpan ("Refinement errors in the following places:\n" ++  improperClafers)
    else return iModule
  where
    uidIClaferMap' = createUidIClaferMap iModule
    improperClafers :: String
    improperClafers = foldMapIR isImproper iModule

    isImproper :: Ir -> String
    isImproper (IRClafer claf@IClafer{_cinPos = (Span (Pos l c) _) ,_ident=i}) =
      let
        match = matchNestedInheritance uidIClaferMap' claf
      in
        if (isProperNesting uidIClaferMap' match)
        then let
               (properCardinalityRefinement, properBagToSetRefinement, properTargetSubtyping) = isProperRefinement uidIClaferMap' match
             in if (properCardinalityRefinement)
             then if (properBagToSetRefinement)
                  then if (properTargetSubtyping)
                       then ""
                       else ("Improper target subtyping for clafer '" ++ i ++ "' on line " ++ show l ++ " column " ++ show c ++ "\n")
                  else ("Improper bag to set refinement for clafer '" ++ i ++ "' on line " ++ show l ++ " column " ++ show c ++ "\n")
             else ("Improper cardinality refinement for clafer '" ++ i ++ "' on line " ++ show l ++ " column " ++ show c ++ "\n")
        else ("Improperly nested clafer '" ++ i ++ "' on line " ++ show l ++ " column " ++ show c ++ "\n")
    isImproper _ = ""

-- F> Top-level abstract clafer extending a nested abstract clafer <https://github.com/gsdlab/clafer/issues/67> F>
relocateTopLevelAbstractToParents :: [IElement]      -> [IElement]
relocateTopLevelAbstractToParents    originalElements =
  let
    (elementsToBeRelocated, remainingElements) = partition needsRelocation originalElements
  in
    case elementsToBeRelocated of
      [] -> originalElements
      _  -> map (insertElements $ mkParentUIDIElementMap elementsToBeRelocated) remainingElements
  where
    needsRelocation :: IElement -> Bool
    needsRelocation    IEClafer{_iClafer} = not $ isTopLevel _iClafer
    needsRelocation    _                  = False

    -- creates a map from parentUID to a list of elements to be added as children of a clafer with that UID
    mkParentUIDIElementMap :: [IElement] -> Map.Map UID [IElement]
    mkParentUIDIElementMap    elems       = foldl'
        (\accumMap' (parentUID', elem') -> Map.insertWith (++) parentUID' [elem'] accumMap')
        Map.empty
        (map (\e -> (_parentUID $ _iClafer e, e)) elems)

    insertElements :: Map.Map UID [IElement] -> IElement     -> IElement
    insertElements    parentMap               targetElement = let
        targetUID = targetElement ^. iClafer . uid
        newChildren = Map.findWithDefault [] targetUID parentMap
        currentElements = targetElement ^. iClafer . elements
        newElements =  map (insertElements parentMap) currentElements
                    ++ newChildren
      in
        targetElement & iClafer . elements .~ newElements
-- <F Top-level abstract clafer extending a nested abstract clafer <https://github.com/gsdlab/clafer/issues/67> <F
