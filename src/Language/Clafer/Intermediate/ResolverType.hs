{-# LANGUAGE NamedFieldPuns, FlexibleInstances, FlexibleContexts, GeneralizedNewtypeDeriving #-}
{-
 Copyright (C) 2012-2017 Jimmy Liang, Kacper Bak, Michal Antkiewicz <http://gsd.uwaterloo.ca>

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
module Language.Clafer.Intermediate.ResolverType (resolveTModule)  where

import Language.ClaferT
import Language.Clafer.Common
import Language.Clafer.Intermediate.Intclafer hiding (uid)
import Language.Clafer.Intermediate.Desugarer
import Language.Clafer.Intermediate.TypeSystem
import Language.Clafer.Front.PrintClafer

import Control.Applicative
import Control.Exception (assert)
import Control.Lens ((&), (%~), traversed)
import Control.Monad.Except
import Control.Monad.List
import Control.Monad.Reader
import Data.Either
import Data.List
import Data.Maybe
import Prelude hiding (exp)

type TypeDecls = [(String, IType)]
data TypeInfo = TypeInfo {iTypeDecls::TypeDecls, iUIDIClaferMap::UIDIClaferMap, iCurThis::IClafer, iCurPath::Maybe IType}

newtype TypeAnalysis a = TypeAnalysis (ReaderT TypeInfo (Either ClaferSErr) a)
  deriving (MonadError ClaferSErr, Monad, Functor, MonadReader TypeInfo, Applicative)

instance MonadFail TypeAnalysis where
  fail = throwError . ClaferErr

-- return the type of a UID but give preference to local declarations in quantified expressions, which shadow global names
typeOfUid :: MonadTypeAnalysis m => UID -> m IType
typeOfUid uid = fromMaybe (TClafer [uid]) . lookup uid <$> typeDecls

class MonadFail m => MonadTypeAnalysis m where
  -- What "this" refers to
  curThis :: m IClafer
  localCurThis :: IClafer -> m a -> m a

  -- The next path is a child of curPath (or Nothing)
  curPath :: m (Maybe IType)
  localCurPath :: IType -> m a -> m a

  -- Extra declarations
  typeDecls :: m TypeDecls
  localDecls :: TypeDecls -> m a -> m a

instance MonadTypeAnalysis TypeAnalysis where
  curThis = TypeAnalysis $ asks iCurThis
  localCurThis newThis (TypeAnalysis d) =
    TypeAnalysis $ local setCurThis d
    where
    setCurThis t = t{iCurThis = newThis}

  curPath = TypeAnalysis $ asks iCurPath
  localCurPath newPath (TypeAnalysis d) =
    TypeAnalysis $ local setCurPath d
    where
    setCurPath t = t{iCurPath = Just newPath}

  typeDecls = TypeAnalysis $ asks iTypeDecls
  localDecls extra (TypeAnalysis d) =
    TypeAnalysis $ local addTypeDecls d
    where
    addTypeDecls t@TypeInfo{iTypeDecls = c} = t{iTypeDecls = extra ++ c}

instance MonadTypeAnalysis m => MonadTypeAnalysis (ListT m) where
  curThis = lift curThis
  localCurThis = mapListT . localCurThis
  curPath = lift curPath
  localCurPath = mapListT . localCurPath
  typeDecls = lift typeDecls
  localDecls = mapListT . localDecls

instance MonadTypeAnalysis m => MonadTypeAnalysis (ExceptT ClaferSErr m) where
  curThis = lift curThis
  localCurThis = mapExceptT . localCurThis
  curPath = lift curPath
  localCurPath = mapExceptT . localCurPath
  typeDecls = lift typeDecls
  localDecls = mapExceptT . localDecls

-- | Type inference and checking
runTypeAnalysis :: TypeAnalysis a -> IModule -> Either ClaferSErr a
runTypeAnalysis (TypeAnalysis tc) imodule = runReaderT tc $ TypeInfo [] (createUidIClaferMap imodule) undefined Nothing

claferWithUid :: MonadFail m => UIDIClaferMap -> String -> m IClafer
claferWithUid uidIClaferMap' u = case findIClafer uidIClaferMap' u of
  Just c -> return c
  Nothing -> fail $ "ResolverType.claferWithUid: " ++ u ++ " not found!"

parentOf :: MonadFail m => UIDIClaferMap -> UID -> m UID
parentOf uidIClaferMap' c = case _parentUID <$> findIClafer uidIClaferMap' c of
  Just u -> return u
  Nothing -> fail $ "ResolverType.parentOf: " ++ c ++ " not found!"

{-
 - C is an direct child of B.
 -
 -  abstract A
 -    C      // C - child
 -  B : A    // B - parent
 -}
isIndirectChild :: MonadFail m => UIDIClaferMap -> UID -> UID -> m Bool
isIndirectChild uidIClaferMap' child parent = do
  (_:allSupers) <- hierarchy uidIClaferMap' parent
  childOfSupers <- mapM (isChild uidIClaferMap' child._uid) allSupers
  return $ or childOfSupers

isChild :: MonadFail m => UIDIClaferMap -> UID -> UID -> m Bool
isChild uidIClaferMap' child parent =
    case findIClafer uidIClaferMap' child of
        Nothing -> return False
        Just childIClafer -> do
            let directChild = (parent == _parentUID childIClafer)
            indirectChild <- isIndirectChild uidIClaferMap' child parent
            return $ directChild || indirectChild


str :: IType -> String
str t =
  case unionType t of
    [t'] -> t'
    ts   -> "[" ++ intercalate "," ts ++ "]"

showType :: PExp                   -> String
showType    PExp{ _iType=Nothing }  = "unknown type"
showType    PExp{ _iType=(Just t) } = show t

data TAMode
  = TAReferences    -- ^ Phase one: only process references
  | TAExpressions   -- ^ Phase two: only process constraints and goals

resolveTModule :: (IModule, GEnv) -> Either ClaferSErr IModule
resolveTModule (imodule, _) =
  case runTypeAnalysis (analysisReferences $ _mDecls imodule) imodule of
    Right mDecls' -> case runTypeAnalysis (analysisExpressions $ mDecls') imodule{_mDecls = mDecls'} of
      Right mDecls'' -> return imodule{_mDecls = mDecls''}
      Left err      -> throwError err
    Left err      -> throwError err
  where
  analysisReferences = mapM (resolveTElement TAReferences rootIdent)
  analysisExpressions = mapM (resolveTElement TAExpressions rootIdent)

-- Phase one: only process references
resolveTElement :: TAMode     -> String -> IElement          -> TypeAnalysis IElement
resolveTElement    TAReferences  _         (IEClafer iclafer) =
  do
    uidIClaferMap' <- asks iUIDIClaferMap
    reference' <- case _reference iclafer of
      Nothing -> return Nothing
      Just originalReference -> do
        refs' <- resolveTPExp $ _ref originalReference
        case refs' of
          []     -> return Nothing
          [ref'] -> return $ refWithNewType uidIClaferMap' originalReference ref'
          (ref':_) -> return $ refWithNewType uidIClaferMap' originalReference ref'
    elements' <- mapM (resolveTElement TAReferences (_uid iclafer)) (_elements iclafer)
    return $ IEClafer iclafer{_elements = elements', _reference=reference'}
  where
    refWithNewType uMap oRef r = let
        r' = r & iType.traversed %~ (addHierarchy uMap)
      in case _iType r' of
        Nothing -> Nothing
        Just t -> if isTBoolean t
                  then Nothing
                  else Just $ oRef{_ref=r'}
resolveTElement    TAReferences  _         iec@IEConstraint{} = return iec
resolveTElement    TAReferences  _         ieg@IEGoal{} = return ieg

-- Phase two: only process constraints and goals
resolveTElement    TAExpressions  _         (IEClafer iclafer) =
  do
    elements' <- mapM (resolveTElement TAExpressions (_uid iclafer)) (_elements iclafer)
    return $ IEClafer iclafer{_elements = elements'}
resolveTElement    TAExpressions parent'   (IEConstraint _isHard _pexp) =
  IEConstraint _isHard <$> (testBoolean =<< resolveTConstraint parent' _pexp)
  where
  testBoolean pexp' =
    do
      unless (isTBoolean $ typeOf pexp') $
        throwError $ SemanticErr (_inPos pexp') ("A constraint requires an expression of type 'TBoolean' but got '" ++ showType pexp' ++ "'")
      return pexp'
resolveTElement    TAExpressions parent' (IEGoal isMaximize' pexp') =
  IEGoal isMaximize' <$> resolveTConstraint parent' pexp'

resolveTConstraint :: String -> PExp -> TypeAnalysis PExp
resolveTConstraint curThis' constraint =
  do
    uidIClaferMap' <- asks iUIDIClaferMap
    curThis'' <- claferWithUid uidIClaferMap' curThis'
    head <$> localCurThis curThis'' (resolveTPExp constraint :: TypeAnalysis [PExp])


resolveTPExp :: PExp -> TypeAnalysis [PExp]
resolveTPExp p =
  do
    x <- resolveTPExp' p
    case partitionEithers x of
      (f:_, []) -> throwError f                       -- Case 1: Only fails. Complain about the first one.
      ([], [])  -> throwError $ SemanticErr (_inPos p) ("No results but no errors for " ++ show p) -- Case 2: No success and no error message. Bug.
      (_,   xs) -> return xs                          -- Case 3: At least one success.

resolveTPExp' :: PExp -> TypeAnalysis [Either ClaferSErr PExp]
resolveTPExp' p@PExp{_inPos, _exp = IClaferId{_sident = "dref"}} = do
  uidIClaferMap' <- asks iUIDIClaferMap
  runListT $ runExceptT $ do
    curPath' <- curPath
    case curPath' of
      Just curPath'' -> do
        case concatMap (getTMaps uidIClaferMap') $ getTClafers uidIClaferMap' curPath'' of
          [t'] -> return $ p `withType` t'
          (t':_) -> return $ p `withType` t'
          [] -> throwError $ SemanticErr _inPos ("Cannot deref from type '" ++ str curPath'' ++ "'")
      Nothing -> throwError $ SemanticErr _inPos ("Cannot deref at the start of a path")
resolveTPExp' p@PExp{_inPos, _exp = IClaferId{_sident = "parent"}} = do
  uidIClaferMap' <- asks iUIDIClaferMap
  runListT $ runExceptT $ do
    curPath' <- curPath
    case curPath' of
      Just curPath'' -> do
        parent' <- fromUnionType <$> runListT (parentOf uidIClaferMap' =<< liftList (unionType curPath''))
        when (isNothing parent') $
          throwError $ SemanticErr _inPos "Cannot parent from root"
        let result = p `withType` fromJust parent'
        return result
      Nothing -> throwError $ SemanticErr _inPos "Cannot parent at the start of a path"
resolveTPExp' p@PExp{_exp = IClaferId{_sident = "integer"}} = runListT $ runExceptT $ return $ p `withType` TInteger
resolveTPExp' p@PExp{_exp = IClaferId{_sident = "int"}} = runListT $ runExceptT $ return $ p `withType` TInteger
resolveTPExp' p@PExp{_exp = IClaferId{_sident = "string"}} = runListT $ runExceptT $ return $ p `withType` TString
resolveTPExp' p@PExp{_exp = IClaferId{_sident = "double"}} = runListT $ runExceptT $ return $ p `withType` TDouble
resolveTPExp' p@PExp{_exp = IClaferId{_sident = "real"}} = runListT $ runExceptT $ return $ p `withType` TReal
resolveTPExp' p@PExp{_inPos, _exp = IClaferId{_sident="this"}} =
  runListT $ runExceptT $ do
    sident' <- _uid <$> curThis
    result <- (p `withType`) <$> typeOfUid sident'
    return result
      <++>
      addDref result -- Case 2: Dereference the sident 1..* times
resolveTPExp' p@PExp{_inPos, _exp = IClaferId{_sident, _isTop}} = do
  uidIClaferMap' <- asks iUIDIClaferMap
  runListT $ runExceptT $ do
    curPath' <- curPath
    sident' <- if _sident == "this" then _uid <$> curThis else return _sident
    when (isJust curPath') $ do
      c <- mapM (isChild uidIClaferMap' sident') $ unionType $ fromJust curPath'
      let parentId' = str (fromJust curPath')
      unless (or c || parentId' == "root") $ throwError $ SemanticErr _inPos ("'" ++ sident' ++ "' is not a child of type '" ++ parentId' ++ "'")
    result <- (p `withType`) <$> typeOfUid sident'
    if _isTop
    then return result -- Case 1: Use the sident
          <++>
          addDref result -- Case 2: Dereference the sident 1..* times
          <++>
          addSome result
    else return result -- all not top-level identifiers must be in a path


resolveTPExp' p@PExp{_inPos, _exp} =
  runListT $ runExceptT $ (case _exp of
    e@IFunExp {_op = ".", _exps = [arg1, arg2]} -> do
        (iType', exp') <-  do
            arg1' <- lift $ ListT $ resolveTPExp arg1
            localCurPath (typeOf arg1') $ do
                arg2' <- liftError $ lift $ ListT $ resolveTPExp arg2
                (case _iType arg2' of
                    Just (t'@TClafer{}) -> return (t', e{_exps = [arg1', arg2']})
                    Just (TMap{_ta=t'}) -> return (t', e{_exps = [arg1', arg2']})
                    _ -> fail $ "Function '.' cannot be performed on " ++ showType arg1' ++ "\n.\n " ++ showType arg2')
        let result = p{_iType = Just iType', _exp = exp'}
        return result -- Case 1: Use the sident
          <++>
          addDref result -- Case 2: Dereference the sident 1..* times
          <++>
          addSome result
    _ -> do
      (iType', exp') <- ExceptT $ ListT $ resolveTExp _exp
      return p{_iType = Just iType', _exp = exp'})
  where
  resolveTExp :: IExp -> TypeAnalysis [Either ClaferSErr (IType, IExp)]
  resolveTExp e@(IInt _)    = runListT $ runExceptT $ return (TInteger, e)
  resolveTExp e@(IDouble _) = runListT $ runExceptT $ return (TDouble, e)
  resolveTExp e@(IReal _) = runListT $ runExceptT $ return (TReal, e)
  resolveTExp e@(IStr _)    = runListT $ runExceptT $ return (TString, e)

  resolveTExp e@IFunExp {_op, _exps = [arg]} = do
    uidIClaferMap' <- asks iUIDIClaferMap
    runListT $ runExceptT $ do
      arg0 <- lift $ ListT $ resolveTPExp arg
      -- Sigil-Logic/clafer#47: `sum` and `product` aggregate the value of
      -- every member of a set of integer clafers, so a clafer-set operand is
      -- dereferenced as a whole -- `(x ++ y).dref` -- and tried first; the
      -- plain operand follows so that a reference-less operand keeps its
      -- error below.  Before, `sum (x ++ y)` was typed from the operands'
      -- separate dereference alternatives, and the first "integer" one,
      -- `x ++ y.dref` (a union type, on which 'isTInteger' holds), reached
      -- both generators, which rendered it literally.
      arg' <- if _op `elem` [iSumSet, iProdSet] && isTClafer (typeOf arg0)
                then derefAggregateOperand _op uidIClaferMap' arg0 <++> return arg0
                else return arg0
      let t = typeOf arg'
      let
          test c =
            unless c $
              throwError $ SemanticErr _inPos ("Function '" ++ _op ++ "' cannot be performed on " ++ _op ++ " '" ++ showType arg' ++ "'")
          -- a set operator that survived typing only over values: its operands
          -- share no clafer type (`sum (N -- m)` with unrelated N and m), so the
          -- clafer-set alternative failed and the one-by-one dereferences won
          testAggregable =
            unless (aggregableOperand arg') $ throwError $ SemanticErr _inPos $
              case arg' of
                PExp{_exp = IFunExp{_op = setOp}} | isSetOperator arg' ->
                  "Function '" ++ _op ++ "' cannot be performed on '" ++ setOp ++ "' over values: its operands share no clafer type and were dereferenced one by one; the operand of '" ++ _op ++ "' must be a set of integer clafers, as in " ++ _op ++ " (N " ++ setOp ++ " n1) with n1 : N"
                _ -> "Function '" ++ _op ++ "' cannot be performed on " ++ _op ++ " '" ++ showType arg' ++ "'"
      let result
            | _op == iNot = test (isTBoolean t) >> return TBoolean
            | _op `elem` ltlUnOps = test (isTBoolean t) >> return TBoolean
            | _op == iCSet = return TInteger
            | _op == iSumSet = testAggregable >> return TInteger
            | _op == iProdSet = testAggregable >> return TInteger
            | _op `elem` [iMin, iMinimum, iMaximum, iMinimize, iMaximize] = test (numeric t) >> return t
            | otherwise = assert False $ fail $ "Unknown op '" ++ _op ++ "'"
      result' <- result
      return (result', e{_exps = [arg']})

  resolveTExp e@IFunExp {_op = "++", _exps = [arg1, arg2]} = do
      -- arg1s' <- resolveTPExp arg1
      -- arg2s' <- resolveTPExp arg2
      -- let union' a b = typeOf a +++ typeOf b
      -- return [ return (union' arg1' arg2', e{_exps = [arg1', arg2']})
      --        | (arg1', arg2') <- sortBy (comparing $ length . unionType . uncurry union') $ liftM2 (,) arg1s' arg2s'
      --        , not (isTBoolean $ typeOf arg1') && not (isTBoolean $ typeOf arg2') ]
      runListT $ runExceptT $ do
        arg1' <- lift $ ListT $ resolveTPExp arg1
        arg2' <- lift $ ListT $ resolveTPExp arg2
        let t1 = typeOf arg1'
        let t2 = typeOf arg2'
        return (t1 +++ t2, e{_exps = [arg1', arg2']})


  resolveTExp e@IFunExp {_op, _exps = [arg1, arg2]} = do
    uidIClaferMap' <- asks iUIDIClaferMap
    runListT $ runExceptT $ do
      arg1' <- lift $ ListT $ resolveTPExp arg1
      arg2' <- lift $ ListT $ resolveTPExp arg2
      let t1 = typeOf arg1'
      let t2 = typeOf arg2'
      let testIntersect e1 e2 =
            do
              it <- intersection uidIClaferMap' e1 e2
              case it of
                Just it' -> if isTBoolean it'
                            then throwError $ SemanticErr _inPos ("Function '" ++ _op ++ "' cannot be performed on\n" ++ showType arg1' ++ "\n" ++ _op ++ "\n" ++ showType arg2')
                            else return it'
                Nothing  -> throwError $ SemanticErr _inPos ("Function '" ++ _op ++ "' cannot be performed on\n" ++ showType arg1' ++ "\n" ++ _op ++ "\n" ++ showType arg2')
      let testNotSame e1 e2 =
            when (e1 `sameAs` e2) $
              throwError $ SemanticErr _inPos ("Function '" ++ _op ++ "' is redundant because the two subexpressions are always equivalent")
      let test c =
            unless c $
              throwError $ SemanticErr _inPos ("Function '" ++ _op ++ "' cannot be performed on\n" ++ showType arg1' ++ "\n" ++ _op ++ "\n" ++ showType arg2')
      let result
            | _op `elem` logBinOps = test (isTBoolean t1 && isTBoolean t2) >> return TBoolean
            | _op `elem` ltlBinOps = test (isTBoolean t1 && isTBoolean t2) >> return TBoolean
            | _op `elem` [iLt, iGt, iLte, iGte] = test (numeric t1 && numeric t2) >> return TBoolean
            | _op `elem` [iEq, iNeq] = testNotSame arg1' arg2' >> testIntersect t1 t2 >> return TBoolean
            | _op == iDifference = testNotSame arg1' arg2' >> testIntersect t1 t2 >> return t1
            | _op == iIntersection = testNotSame arg1' arg2' >> testIntersect t1 t2
            | _op `elem` [iDomain, iRange] = testIntersect t1 t2
            | _op `elem` relSetBinOps = testIntersect t1 t2 >> return TBoolean
            | _op `elem` [iSub, iMul, iDiv, iRem] = test (numeric t1 && numeric t2) >> return (coerce t1 t2)
            | _op == iPlus =
                (test (isTString t1 && isTString t2) >> return TString) -- Case 1: String concatenation
                `catchError`
                const (test (numeric t1 && numeric t2) >> return (coerce t1 t2)) -- Case 2: Addition
            | otherwise = fail $ "ResolverType: Unknown op: " ++ show e
      result' <- result
      return (result', e{_exps = [arg1', arg2']})

  resolveTExp e@(IFunExp "ifthenelse" [arg1, arg2, arg3]) = do
    uidIClaferMap' <- asks iUIDIClaferMap
    runListT $ runExceptT $ do
      arg1' <- lift $ ListT $ resolveTPExp arg1
      arg2' <- lift $ ListT $ resolveTPExp arg2
      arg3' <- lift $ ListT $ resolveTPExp arg3
      let t1 = typeOf arg1'
      let t2 = typeOf arg2'
      let t3 = typeOf arg3'

      unless (isTBoolean t1) $
        throwError $ SemanticErr _inPos ("The type of condition in 'if/then/else' must be 'TBoolean', insted it is " ++ showType arg1')

      it <- getIfThenElseType uidIClaferMap' t2 t3
      t <- case it of
        Just it' -> return it'
        Nothing  -> throwError $ SemanticErr _inPos ("Function 'if/then/else' cannot be performed on \nif\n" ++ showType arg1' ++ "\nthen\n" ++ showType arg2' ++ "\nelse\n" ++ showType arg3')

      return (t, e{_exps = [arg1', arg2', arg3']})
  -- some P, no P, one P
  -- P must not be TBoolean
  resolveTExp e@IDeclPExp{_oDecls=[], _bpexp} =
    runListT $ runExceptT $ do
      bpexp' <- liftError $ lift $ ListT $ resolveTPExp _bpexp
      case _iType bpexp' of
          Nothing -> fail $ "resolveTExp@IDeclPExp: No type computed for body\n" ++ show bpexp'
          Just t' -> if  isTBoolean t'
                     then throwError $ SemanticErr _inPos "The type of body of a quantified expression without local declarations must not be 'TBoolean'"
                     else return $ (TBoolean, e{_bpexp = bpexp'})
  -- some x : X | P, no x : X | P, one x : X | P
  -- X must not be TBoolean, P must be TBoolean
  resolveTExp e@IDeclPExp{_oDecls, _bpexp} =
    runListT $ runExceptT $ do
      oDecls' <- mapM resolveTDecl _oDecls
      let extraDecls = [(decl, typeOf $ _body oDecl) | oDecl <- oDecls', decl <- _decls oDecl]
      localDecls extraDecls $ do
        bpexp' <- liftError $ lift $ ListT $ resolveTPExp _bpexp
        case _iType bpexp' of
            Nothing -> fail $ "resolveTExp@IDeclPExp: No type computed for body\n" ++ show bpexp'
            Just t' -> if  isTBoolean t'
                       then return $ (TBoolean, e{_oDecls = oDecls', _bpexp = bpexp'})
                       else throwError $ SemanticErr _inPos $ "The type of body of a quantified expression with local declarations must be 'TBoolean', instead it is\n" ++ showType bpexp'
    where
    resolveTDecl d@IDecl{_body} =
      do
        body' <- lift $ ListT $ resolveTPExp _body
        case _iType body' of
            Nothing -> fail $ "resolveTExp@IDeclPExp: No type computed for local declaration\n" ++ show body'
            Just t' -> if  isTBoolean t'
                       then throwError $ SemanticErr _inPos "The type of declaration of a quantified expression must not be 'TBoolean'"
                       else return $ d{_body = body'}
  resolveTExp e = fail $ "Unknown iexp: " ++ show e

-- | Dereference an operand of @sum@ / @product@ as a whole
-- (Sigil-Logic/clafer#47).  A set operator over clafers -- @x ++ y@, @N --
-- n1@, @(n1 ++ n2) ** N@ -- becomes @(...).dref@ typed by the union of its
-- members' nearest reference maps: the reference owners are kept apart in a
-- 'TUnion' so each generator can name every reference relation (Alloy
-- renders @temp.(@c0_x_ref + @c0_y_ref)@; Choco partitions the expression
-- by owner), and the targets are joined, so a mixed target (integer and
-- string) is refused by 'aggregableOperand'.  While the target is itself a
-- set of clafers -- a reference chain, @sum (r1 ++ r2)@ with @r1 -> N@ and
-- @N ->> integer@ -- further hops follow, each again by the union of the
-- target members' nearest references, as 'addDref' follows a chain for a
-- single operand (HOARDE Codex, PR #52 Cycle 1).  A leaf typed over
-- clafers with different references (a local bound to @x ++ y@, reachable
-- with @--skip-resolver@) contributes every one of them: Alloy joins the
-- union of the relations, Choco splits the leaf per reference (@n ** x@,
-- @n ** y@; HOARDE Codex and Gemini, PR #52 Cycles 1 and 2).  A leaf
-- without a reference (@sum (A ++ n1)@ with @A@ reference-less) is an
-- error positioned at the leaf.  Every other clafer-set operand -- a
-- clafer, a navigation, a local -- takes the same hops, which coincide
-- with its own 'addDref' alternatives, so @sum N@, @sum Feature.cost@, and
-- @sum r@ are unchanged.  A dereference written after a set operator in the
-- source fails name resolution, so the union map is reachable only from
-- here.
derefAggregateOperand :: String -> UIDIClaferMap -> PExp -> ExceptT ClaferSErr (ListT TypeAnalysis) PExp
derefAggregateOperand op' uidIClaferMap' operand
  | isSetOperator operand =
      case [ leaf | leaf <- leaves, referenceLess (typeOf leaf) ] of
        leaf : _ -> throwError $ SemanticErr (_inPos leaf) ("Function '" ++ op' ++ "' cannot be performed on a set expression over '" ++ leafName leaf ++ "', which has no reference")
        []       -> case mapM normalizeLeaf leaves of
          Left (leaf, culprit) -> throwError $ SemanticErr (_inPos leaf) ("Function '" ++ op' ++ "' cannot be performed on a set expression over '" ++ leafName leaf ++ "', whose reference chain reaches '" ++ culprit ++ "', which has no reference")
          Right leaves'        -> hops $ rebuild operand leaves'
  -- a single operand takes the same hops: for a clafer, a navigation, or a
  -- local over one clafer they coincide with 'addDref' (the nearest
  -- reference along the hierarchy at each hop); for a local bound to a set
  -- expression over clafers with different references (`all n : (x ++ y) |
  -- sum n`, --skip-resolver) they name every reference where 'addDref'
  -- named the first (HOARDE Junie, PR #52 Cycle 2)
  | otherwise = hops operand
  where
  leaves = setOperatorLeaves operand
  newPExp = PExp Nothing "" $ _inPos operand
  -- Each leaf follows its own reference chain first (HOARDE Codex, PR #52
  -- Cycle 2): a leaf whose nearest references point to clafers is
  -- dereferenced, typed by the target, until its nearest references point
  -- to values, so leaves of different depths (`r1 ++ n1` with `r1 -> N`)
  -- meet as sets of clafers with values and take the final hop together;
  -- a chain that reaches a clafer without a reference (`r1 -> A`) is an
  -- error at the leaf instead of a member that silently contributes
  -- nothing.  References to clafers and to values at one level of a leaf
  -- are left as they are and refused by 'aggregableOperand' after the hop.
  normalizeLeaf leaf = go leaf
    where
    go p = case mapsOf (targetOf $ typeOf p) of
      []                             -> Left (leaf, typeName $ targetOf $ typeOf p)
      ms | all (isTClafer . _ta) ms -> go $ PExp (Just $ _ta refMap) "" (_inPos leaf) (IFunExp "." [p, PExp (Just refMap) "" (_inPos leaf) (IClaferId "" "dref" False NoBind)])
         | otherwise                -> Right p
        where refMap = unionMap ms
  typeName (TClafer (u : _)) | Just IClafer{_ident} <- findIClafer uidIClaferMap' u = _ident
  typeName t = show t
  -- the set operator with its leaves replaced in order, each operator
  -- node re-typed by the union of its operands (a superset for `--` and
  -- `**`, which only widens the relations the final hop names)
  rebuild p ls = fst $ go p ls
    where
    go q@PExp{_exp = e@IFunExp{_exps = [l, r]}} ls0
      | isSetOperator q = let (l', ls1) = go l ls0
                              (r', ls2) = go r ls1
                          in (q{_exp = e{_exps = [l', r']}, _iType = Just $ typeOf l' +++ typeOf r'}, ls2)
    go _ (x : xs) = (x, xs)
    go q []       = (q, [])
  -- one dereference hop by the union of the nearest references of the
  -- clafers the type names, then further hops while the target is a set
  -- of clafers with references
  hops pexp' = case mapsOf (targetOf $ typeOf pexp') of
    [] -> lift mzero
    ms -> let refMap = unionMap ms
              next = newPExp (IFunExp "." [pexp', newPExp (IClaferId "" "dref" False NoBind) `withType` refMap]) `withType` refMap
          in return next <++> (case _ta refMap of
                                 TClafer{} -> hops next
                                 _         -> lift mzero)
  targetOf (TMap _ ta) = ta
  targetOf t           = t
  unionMap [m] = m
  unionMap ms  = TMap (TUnion $ map _so ms) (foldr1 (+++) $ map _ta ms)
  -- the nearest reference map of each clafer a type names: for one clafer
  -- (a type that is its own hierarchy) the first along the hierarchy, as
  -- 'addDref' finds it; for several (a set operator's union type, a union
  -- of reference targets, a local bound to a set expression) the first
  -- along each member's hierarchy
  mapsOf t@(TClafer hi@(u : _))
    | getTClaferByUID uidIClaferMap' u == Just t = take 1 $ getTMaps uidIClaferMap' t
    | otherwise = nub $ concat [ take 1 $ getTMaps uidIClaferMap' member | u' <- hi, Just member <- [getTClaferByUID uidIClaferMap' u'] ]
  mapsOf t = take 1 $ concatMap (getTMaps uidIClaferMap') $ getTClafers uidIClaferMap' t
  referenceLess t@(TClafer hi@(u : _))
    | getTClaferByUID uidIClaferMap' u == Just t = null $ getTMaps uidIClaferMap' t
    | otherwise = or [ null $ getTMaps uidIClaferMap' member | u' <- hi, Just member <- [getTClaferByUID uidIClaferMap' u'] ]
  referenceLess t = null $ concatMap (getTMaps uidIClaferMap') $ getTClafers uidIClaferMap' t
  leafName leaf = case _exp leaf of
    IClaferId{_sident} -> maybe _sident _ident $ findIClafer uidIClaferMap' _sident
    _ -> case typeOf leaf of
      TClafer (u : _) | Just IClafer{_ident} <- findIClafer uidIClaferMap' u -> _ident
      _ -> showType leaf

-- | Whether a typed operand of @sum@ / @product@ denotes a set of integer
-- clafers (Sigil-Logic/clafer#47): a dereference to integers -- the
-- operand's own @.dref@, or the one 'derefAggregateOperand' adds -- and not a
-- set operator whose operands were dereferenced one by one (@x ++ y.dref@,
-- of a union type; @N.dref -- m.dref@ over unrelated @N@ and @m@, of type
-- integer), nor a mixed target.
aggregableOperand :: PExp -> Bool
aggregableOperand operand
  | isSetOperator operand = False
  | otherwise = case typeOf operand of
      TInteger        -> True
      TMap _ TInteger -> True
      _               -> False

isSetOperator :: PExp -> Bool
isSetOperator PExp{_exp = IFunExp{_op = op', _exps = [_, _]}} = op' `elem` [iUnion, iDifference, iIntersection]
isSetOperator _ = False

-- | The operands of a nest of set operators that are not set operators themselves.
setOperatorLeaves :: PExp -> [PExp]
setOperatorLeaves p@PExp{_exp = IFunExp{_exps = [l, r]}}
  | isSetOperator p = setOperatorLeaves l ++ setOperatorLeaves r
setOperatorLeaves p = [p]

isTClafer :: IType -> Bool
isTClafer TClafer{} = True
isTClafer _         = False

-- Adds "dref"s at the end, effectively dereferencing Clafers when needed.
addDref :: PExp -> ExceptT ClaferSErr (ListT TypeAnalysis) PExp
addDref pexp =
  do
    localCurPath (typeOf pexp) $ do
      deref <- ExceptT (ListT $ resolveTPExp' $ newPExp $ IClaferId "" "dref" False NoBind) `catchError` const (lift mzero)
      let result = newPExp (IFunExp "." [pexp, deref]) `withType` typeOf deref
      return result <++> addDref result
  where
  newPExp = PExp Nothing "" $ _inPos pexp

-- Adds a quantifier "some" at the beginning, effectively turning an identifier into a TBoolean expression
addSome :: PExp -> ExceptT ClaferSErr (ListT TypeAnalysis) PExp
addSome pexp =
  do
    localCurPath (typeOf pexp) $ return $ (newPExp $ IDeclPExp ISome [] pexp) `withType` TBoolean
  where
  newPExp = PExp Nothing "" $ _inPos pexp

typeOf :: PExp -> IType
typeOf pexp = fromMaybe (error "No type") $ _iType pexp

withType :: PExp -> IType -> PExp
withType p t = p{_iType = Just t}

(<++>) :: MonadPlus m => ExceptT e m a -> ExceptT e m a -> ExceptT e m a
(ExceptT a) <++> (ExceptT b) = ExceptT $ a `mplus` b

liftError :: MonadError e m => ExceptT e m a -> ExceptT e m a
liftError e =
  liftCatch catchError e throwError
  where
  liftCatch catchError' m h = ExceptT $ runExceptT m `catchError'` (runExceptT . h)

{-
 -
 - Utility functions
 -
 -}

liftList :: Monad m => [a] -> ListT m a
liftList = ListT . return

syntaxOf :: PExp -> String
syntaxOf = printTree . sugarExp

-- Returns true iff the left and right expressions are syntactically identical
sameAs :: PExp -> PExp -> Bool
sameAs e1 e2 = syntaxOf e1 == syntaxOf e2 -- Not very efficient but hopefully correct
