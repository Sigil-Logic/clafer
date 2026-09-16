{-# LANGUAGE FlexibleContexts #-}
{-
 Copyright (C) 2012 Kacper Bak, Jimmy Liang <http://gsd.uwaterloo.ca>

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
module Language.Clafer.Optimizer.Optimizer where

import Data.Data (Data)
import Data.Maybe
import Data.List
import Control.Applicative
import Control.Lens hiding (elements, children, un)
import Control.Monad.State
import Data.Data.Lens (biplate)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Prelude

import Language.Clafer.Common
import Language.Clafer.ClaferArgs
import Language.Clafer.Front.AbsClafer (Span(..))
import Language.Clafer.Intermediate.Intclafer
import Language.ClaferT (ClaferErr, CErr(..))

-- | Apply optimizations for unused abstract clafers and inheritance flattening
optimizeModule :: ClaferArgs -> (IModule, GEnv) -> IModule
optimizeModule args (imodule, genv) =
  imodule{_mDecls = em $ rm $ map (optimizeElement (1, 1)) $
                   markTopModule $ _mDecls imodule}
  where
  rm = if keep_unused args then makeZeroUnusedAbs else remUnusedAbs
  em = if flatten_inheritance args then flip (curry expModule) genv else id

optimizeElement :: Interval -> IElement -> IElement
optimizeElement interval' x = case x of
  IEClafer c  -> IEClafer $ optimizeClafer interval' c
  IEConstraint _ _  -> x
  IEGoal _ _ -> x

optimizeClafer :: Interval -> IClafer -> IClafer
optimizeClafer interval' c = c {_glCard = glCard',
  _elements = map (optimizeElement glCard') $ _elements c}
  where
  glCard' = multInt (fromJust $ _card c) interval'


multInt :: Interval -> Interval -> Interval
multInt (m, n) (m', n') = (m * m', multExInt n n')

multExInt :: Integer -> Integer -> Integer
multExInt 0 _ = 0
multExInt _  0 = 0
multExInt m n = if m == -1 || n == -1 then -1 else m * n

-- -----------------------------------------------------------------------------
-- unused abstract clafers
--
-- A top-level abstract clafer is /unused/ when no top-level concrete
-- clafer extends it, directly or through the supers of the nested clafers
-- of everything reached that way ('findUnusedAbs'); no instance of it can
-- exist.  Not every unused abstract can be dropped, though: the generators
-- still emit a reference to it wherever the retained part of the module
-- /mentions/ it -- as a reference target (`pick -> Target`) or in a
-- constraint (`[ no Extra ]`) -- and dropping the declaration then
-- leaves a dangling name that Alloy ('The name "c0_Target" cannot be
-- found') and chocosolver ('ReferenceError: "c0_Target" is not defined')
-- both reject (Sigil-Logic/clafer#15).  (A nested clafer's super is a
-- mention too, but the refinement checker rejects a top-level clafer
-- extending a nested abstract of a clafer it does not itself extend, so
-- a super alone never reaches an unused abstract.)
--
-- 'partitionUnusedAbs' therefore splits the unused abstracts into the
-- /mentioned/ ones, which every mode keeps with the (0, 0) cardinality
-- that encodes "no instances" (`fact { #c0_Target = 0 }`, scope 0 --
-- the treatment --keep-unused has always applied to every unused
-- abstract), and the /unmentioned/ ones, which are the only ones
-- 'remUnusedAbs' drops.  --keep-unused ('makeZeroUnusedAbs') still
-- zeroes both.  Invariant: the default output differs from the
-- --keep-unused output only by omitting the unmentioned abstracts, so it
-- cannot dangle where the --keep-unused output does not.

makeZeroUnusedAbs :: [IElement] -> [IElement]
makeZeroUnusedAbs decls' = map (zeroUnusedAbs $ uidSet $ mentioned ++ unmentioned) decls'
  where
  (mentioned, unmentioned) = partitionUnusedAbs decls'

remUnusedAbs :: [IElement] -> [IElement]
remUnusedAbs decls' = map (zeroUnusedAbs $ uidSet mentioned) $ filter (not . isUnmentioned) decls'
  where
  (mentioned, unmentioned) = partitionUnusedAbs decls'
  unmentionedUids = uidSet unmentioned
  isUnmentioned (IEClafer c) = _uid c `Set.member` unmentionedUids
  isUnmentioned _            = False

-- | Give a top-level abstract clafer from the set the (0, 0) cardinality
-- that encodes "no instances"; leave every other element untouched.
zeroUnusedAbs :: Set.Set UID -> IElement -> IElement
zeroUnusedAbs unusedUids (IEClafer c)
  | _uid c `Set.member` unusedUids = IEClafer c{_card = Just (0, 0)}
zeroUnusedAbs _ x = x

uidSet :: [IClafer] -> Set.Set UID
uidSet = Set.fromList . map _uid

-- | The unused top-level abstract clafers, split into those the retained
-- part of the module mentions (to keep, with zero cardinality) and those
-- it does not (droppable).  The retained part is the closure, under
-- "mentions", of the top-level concrete clafers and the top-level
-- constraints and goals -- everything the generators emit -- so a mention
-- inside a dropped abstract retains nothing, while a mention inside a kept
-- one retains, transitively.  A mention of a nested clafer counts as a
-- mention of the top-level clafer containing it, since the top-level
-- declaration is what carries the nested one into the output.
partitionUnusedAbs :: [IElement] -> ([IClafer], [IClafer])
partitionUnusedAbs decls' = partition ((`Set.member` retained) . _uid) unused
  where
  clafers = toClafers decls'
  unused  = findUnusedAbs clafers $ map _uid $ filter (not . _isAbstract) clafers
  byUid   = Map.fromList [ (_uid c, c) | c <- clafers ]
  -- every clafer in a top-level clafer's subtree, itself included, maps
  -- to that top-level clafer
  owner   = Map.fromList $ [ (_uid top, _uid top) | top <- clafers ]
                        ++ [ (_uid c, _uid top) | top <- clafers, c <- universeOn biplate top ]
  -- the top-level clafers an element mentions anywhere in its subtree:
  -- supers, reference targets, and the identifiers in its constraints
  -- and goals (a resolved identifier carries the UID as its sident).
  -- Only an identifier whose sident names a clafer of this module can
  -- be a mention, and of those a locally bound one (a quantifier
  -- variable) mentions nothing, whatever it is called -- its name may
  -- coincide with a UID (`all c0_Target : Thing | ...`) without
  -- referring to that clafer (HOARDE Codex, PR #28 Cycle 1); a
  -- globally bound or unbound one (the --skip-resolver path) mentions
  -- the clafer named.  The sident test comes first on purpose: it is
  -- what lets special names (`parent`, `this`, `dref`, ...) drop out
  -- WITHOUT forcing their binding, which the resolver leaves as a
  -- lazily failing thunk for `parent` under a top-level clafer.
  mentions :: Data a => a -> [UID]
  mentions x = mapMaybe (`Map.lookup` owner) $ concatMap mentionedUid (universeOn biplate x)
  mentionedUid IClaferId{_sident = s, _binding = b}
    | Map.member s owner = case b of
        LocalBind _ -> []
        _           -> [s]
  mentionedUid _ = []
  seeds = [ _uid c | c <- clafers, not $ _isAbstract c ]
       ++ concat [ mentions e | e <- decls', not $ isClaferElement e ]
  isClaferElement (IEClafer _) = True
  isClaferElement _            = False
  retained = close Set.empty seeds
  close seen []     = seen
  close seen (u:us)
    | u `Set.member` seen = close seen us
    | otherwise           = close (Set.insert u seen) $ maybe [] mentions (Map.lookup u byUid) ++ us

-- | The top-level abstract clafers that none of the given (uids of)
-- top-level concrete clafers extends, transitively through the supers of
-- nested clafers.  This is the "no instances can exist" criterion; see
-- 'partitionUnusedAbs' for which of these may actually be dropped.
findUnusedAbs :: [IClafer] -> [String] -> [IClafer]
findUnusedAbs maybeUsed [] = maybeUsed
findUnusedAbs [] _   = []
findUnusedAbs maybeUsed used = findUnusedAbs maybeUsed' $ getUniqExtended used'
  where
  (used', maybeUsed') = partition (\c -> _uid c `elem` used) maybeUsed

getUniqExtended :: [IClafer] -> [String]
getUniqExtended used = nub $ used >>= getExtended


getExtended :: IClafer -> [String]
getExtended c =
  sName ++ ((getSubclafers $ _elements c) >>= getExtended)
  where
  sName = getSuper c

-- -----------------------------------------------------------------------------
-- inheritance  expansions

expModule :: ([IElement], GEnv) -> [IElement]
expModule (decls', genv) = evalState (mapM expElement decls') genv

expClafer :: MonadState GEnv m => IClafer -> m IClafer
expClafer claf = do
  super' <- case _super claf of
    Nothing      -> return Nothing
    (Just pexp') -> Just `liftM` expPExp pexp'
  elements' <- mapM expElement $ _elements claf
  return $ claf {_super = super', _elements = elements'}

expElement :: MonadState GEnv m => IElement -> m IElement
expElement x = case x of
  IEClafer claf  -> IEClafer `liftM` expClafer claf
  IEConstraint isHard' constraint  -> IEConstraint isHard' `liftM` expPExp constraint
  IEGoal isMaximize' goal -> IEGoal isMaximize' `liftM` expPExp goal

expPExp :: MonadState GEnv m => PExp -> m PExp
expPExp (PExp t pid' pos' exp') = PExp t pid' pos' `liftM` expIExp pos' exp'

expIExp :: MonadState GEnv m => Span -> IExp -> m IExp
expIExp pos' x = case x of
  IDeclPExp quant' decls' pexp -> do
    decls'' <- mapM expDecl decls'
    pexp' <- expPExp pexp
    return $ IDeclPExp quant' decls'' pexp'
  IFunExp op' exps' -> if op' == iJoin
                     then expNav pos' x else IFunExp op' `liftM` mapM expPExp exps'
  IClaferId _ _ _ _ -> expNav pos' x
  _ -> return x

expDecl :: MonadState GEnv m => IDecl -> m IDecl
expDecl x = case x of
  IDecl disj locids pexp -> IDecl disj locids `liftM` expPExp pexp

expNav :: MonadState GEnv m => Span -> IExp -> m IExp
expNav pos' x = do
  xs <- split' x return
  xs' <- mapM (expNav' pos' "") xs
  return $ mkIFunExp pos' iUnion $ map fst xs'

expNav' :: MonadState GEnv m => Span -> String -> IExp -> m (IExp, String)
expNav' pos' context (IFunExp _ (p0:p:_)) = do
  (exp0', context') <- expNav' pos' context  $ _exp p0
  (exp', context'') <- expNav' pos' context' $ _exp p
  return (IFunExp iJoin [ p0 {_exp = exp0'}
                        , p  {_exp = exp'}], context'')
expNav' pos' context x@(IClaferId modName' id' isTop' bind' ) = do
  st <- gets stable
  if Map.member id' st
    then do
      let impls  = (Map.!) st id'
      let (impls', context') = maybe (impls, "")
           (\y -> ([[head y]], head y)) $
           find (\z -> context == (head.tail) z) impls
      return (mkIFunExp pos' iUnion $ map (\u -> IClaferId modName' u isTop' bind') $
              map head impls', context')
    else do
      return (x, id')
expNav' pos' _ _ = error $ "Function expNav' from Optimizer expects an argument of type ClaferId or IFunExp but was given another IExp, " ++ show pos'

split' :: MonadState GEnv m => IExp -> (IExp -> m IExp) -> m [IExp]
split'(IFunExp _ (p:pexp:_)) f =
    split' (_exp p) (\s -> f $ IFunExp iJoin
      [p {_exp = s}, pexp])
split' (IClaferId modName' id' isTop' bind') f = do
    st <- gets stable
    mapM f $ map (\y -> IClaferId modName' y isTop' bind') $ maybe [id'] (map head) $ Map.lookup id' st
split' _ _ = error "Function split' from Optimizer expects an argument of type ClaferId or IFunExp but was given another IExp"

-- -----------------------------------------------------------------------------
-- checking if all clafers have unique names and don't extend other clafers

allUnique :: IModule -> Bool
allUnique iModule = dontExtend && identsUnique
  where
    allClafers :: [ IClafer ]
    allClafers = universeOn biplate iModule

    -- True when getSuper always returns Nothing and therefore concatMap returned []
    dontExtend = null $ concatMap getSuper allClafers
    allIdents = map _ident allClafers
    -- all idents are unique when nub cannot remove any duplicates
    identsUnique = (length allIdents) == (length $ nub allIdents)

checkConstraintElement :: [String] -> IElement -> Bool
checkConstraintElement idents x = case x of
  IEClafer claf -> and $ map (checkConstraintElement idents) $ _elements claf
  IEConstraint _ pexp -> checkConstraintPExp idents pexp
  IEGoal _ _ ->  True

checkConstraintPExp :: [String] -> PExp -> Bool
checkConstraintPExp idents pexp = checkConstraintIExp idents $ _exp pexp

checkConstraintIExp :: [String] -> IExp -> Bool
checkConstraintIExp idents x = case x of
   IDeclPExp _ oDecls' pexp ->
     checkConstraintPExp ((oDecls' >>= (checkConstraintIDecl idents)) ++ idents) pexp
   IClaferId _ ident' _ _ -> if ident' `elem` (specialNames ++ (rootIdent : idents)) then True
                          else error $ "optimizer: " ++ ident' ++ " not found"
   _ -> True

checkConstraintIDecl :: [String] -> IDecl -> [String]
checkConstraintIDecl idents (IDecl _ decls' pexp)
  | checkConstraintPExp idents pexp = decls'
  | otherwise                       = []

-- -----------------------------------------------------------------------------
findDupModule :: ClaferArgs -> IModule -> Either ClaferErr IModule
findDupModule args iModule = if check_duplicates args && (not $ null dups)
  then Left $ ClaferErr $ "--check-duplicates: Duplicate clafer names: " ++ (intercalate ", " dups)
  else Right iModule
  where
    allClafers :: [ IClafer ]
    allClafers = universeOn biplate iModule
    dups = findDuplicates allClafers

    findDuplicates :: [IClafer] -> [String]
    findDuplicates clafers =
      map head $ filter (\xs -> 1 < length xs) $ group $ sort $ map _ident clafers

-- -----------------------------------------------------------------------------
-- marks top clafers

markTopModule :: [IElement] -> [IElement]
markTopModule decls' = map (markTopElement (
      specialNames ++ primitiveTypes ++
      (map _uid $ toClafers decls'))) decls'


markTopClafer :: [String] -> IClafer -> IClafer
markTopClafer clafers c =
  c {_super = markTopPExp clafers <$> _super c,
     _elements = map (markTopElement clafers) $ _elements c}


markTopElement :: [String] -> IElement -> IElement
markTopElement clafers x = case x of
  IEClafer c  -> IEClafer $ markTopClafer clafers c
  IEConstraint isHard' pexp  -> IEConstraint isHard' $ markTopPExp clafers pexp
  IEGoal isMaximize' pexp -> IEGoal isMaximize' $ markTopPExp clafers pexp

markTopPExp :: [String] -> PExp -> PExp
markTopPExp clafers pexp =
  pexp {_exp = markTopIExp clafers $ _exp pexp}


markTopIExp :: [String] -> IExp -> IExp
markTopIExp clafers x = case x of
  IDeclPExp quant' decl pexp -> IDeclPExp quant' (map (markTopDecl clafers) decl)
                                (markTopPExp ((decl >>= _decls) ++ clafers) pexp)
  IFunExp op' exps' -> IFunExp op' $ map (markTopPExp clafers) exps'
  IClaferId modName' sident' _ bind'->
    IClaferId modName' sident' (sident' `elem` clafers) bind'
  _ -> x


markTopDecl :: [String] -> IDecl -> IDecl
markTopDecl clafers x = case x of
  IDecl disj locids pexp -> IDecl disj locids $ markTopPExp clafers pexp
