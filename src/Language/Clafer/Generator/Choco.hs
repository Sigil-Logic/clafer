{-# LANGUAGE NamedFieldPuns #-}
{-
 Copyright (C) 2012-2017 Jimmy Liang, Michal Antkiewicz, Rafael Olaechea <http://gsd.uwaterloo.ca>

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
-- | Generates JS representation of IR for the <https://github.com/gsdlab/chocosolver Chocosolver>.
module Language.Clafer.Generator.Choco (genCModule, chocoUnsupportedRefTargets) where

import Control.Applicative
import Control.Lens.Plated hiding (rewrite)
import Control.Monad
import Data.Data.Lens
import Data.List
import Data.Maybe
import Prelude hiding (exp)
import Language.Clafer.Common
import Language.Clafer.Intermediate.Intclafer
import Language.Clafer.Front.LexClafer


-- | A reference target classified for the Choco backend
-- (Sigil-Logic/clafer#18).  chocosolver's @AstRef@ takes exactly one
-- target type (@refTo(T)@ / @refToUnique(T)@), so a target that is not
-- a plain clafer is emitted as a carrier type plus a membership
-- constraint on @joinRef($this())@.  This is the intermediate form both
-- the emission (@genRefTarget@ in 'genCModule') and the support check
-- ('chocoUnsupportedRefTargets') derive from, so the two cannot drift.
data RefTargetSet
  = ClaferSet [UID] String   -- ^ candidate carrier UIDs, and the target as a JS set expression
  | IntSet IntRefSet         -- ^ a set of integers
  | StrSet StrRefSet         -- ^ a set of strings

-- | Sets of integers.  chocosolver has no expression for the integer
-- domain (@global(Int)@ does not compile), so @integer@ and its
-- complements are tracked symbolically: a co-finite set is emitted
-- through @notIn@, and the three set operators are folded over
-- finite (F), co-finite (C), and universe (U) operands by the usual
-- identities (@C -- F = C@ of the union, @C ** F = F@ of the
-- difference, and so on).
data IntRefSet
  = IntUniverse              -- ^ @integer@
  | IntFinite String         -- ^ a finite set: a JS set expression over @constant(k)@
  | IntCoFinite String       -- ^ @integer -- S@: the finite JS set expression S it excludes

-- | Sets of strings.  chocosolver has no string-valued sets (a union
-- of string constants is rejected), so a string restriction is a
-- boolean formula over the referred value: a finite set is a
-- disjunction of equalities, a co-finite one (@string -- "a"@) a
-- conjunction of inequalities, and the universe needs none.  The
-- literals are concrete at generation time, so the three set operators
-- are folded over the literal lists themselves by the same
-- finite / co-finite / universe identities as the integer case.
data StrRefSet
  = StrUniverse              -- ^ @string@
  | StrFinite [String]       -- ^ the literals (non-empty)
  | StrCoFinite [String]     -- ^ every string except the literals (non-empty)

-- | A plain reference target: a clafer, or a join path (only the path's
-- last clafer types the reference, as in the Alloy backend's refType).
-- These keep the pre-#18 emission byte-for-byte.
isPlainRefTarget :: PExp -> Bool
isPlainRefTarget PExp{_exp = IClaferId{}} = True
isPlainRefTarget PExp{_exp = IFunExp "." [_, r]} = isPlainRefTarget r
isPlainRefTarget _ = False

-- | Classifies a reference target that is not plain, given a renderer
-- for its clafer-typed sub-expressions (the generator's constraint
-- printer; the support check passes a dummy).  Left carries the reason
-- the Choco backend cannot express the target.  Negative literals are
-- folded first (`x -> (-1)` is unary minus over the literal in the IR,
-- Sigil-Logic/clafer#31), so they take the literal case below and emit
-- `constant(-1)` -- the same fold the constraint printer applies.
classifyRefTarget :: (PExp -> String) -> PExp -> Either String RefTargetSet
classifyRefTarget render = go . foldNegativeLiterals
  where
    go p@PExp{_exp = IClaferId{_sident}}
      | _sident `elem` [integerType, intType] = Right $ IntSet IntUniverse
      | _sident == stringType = Right $ StrSet StrUniverse
      | isPrimitive _sident = Left $ "the " ++ _sident ++ " type inside a set expression"
      | otherwise           = Right $ ClaferSet [_sident] (render p)
    go p@PExp{_exp = IFunExp "." [_, r]} = case go r of
      Right (ClaferSet uids _) -> Right $ ClaferSet uids (render p)
      Right _                  -> Left "a join whose target is not a clafer"
      Left why                 -> Left why
    go PExp{_exp = IInt k} = Right $ IntSet $ IntFinite $ "constant(" ++ show k ++ ")"
    go PExp{_exp = IStr t} = Right $ StrSet $ StrFinite [t]
    go PExp{_exp = IFunExp op' [a, b]}
      | op' `elem` ["++", "**", "--"] = do
          a' <- go a
          b' <- go b
          combine op' a' b'
    go _ = Left "an expression that is not a set expression over clafers, integers, or strings"

    -- the carriers of both operands are kept for every operator: the
    -- values of `a ** b` and `a -- b` lie in `a`, so a's carriers alone
    -- would be sound, but the least common super clafer of all leaves
    -- is the type chocosolver needs for the constraints that later
    -- mention the reference (a carrier narrowed to `Alice` makes an
    -- `Ella not in onlyAlice` assertion ill-typed: disjoint types)
    combine op' (ClaferSet ua ja) (ClaferSet ub jb) = Right $ ClaferSet (ua ++ ub) (setOp op' ja jb)
    combine op' (IntSet a) (IntSet b) = IntSet <$> intOp op' a b
    combine op' (StrSet a) (StrSet b) = StrSet <$> strOp op' a b
    combine _ _ _ = Left "a set expression mixing clafers, integers, and strings"

    finiteStr [] = Left "an empty set of strings"
    finiteStr ts = Right $ StrFinite ts
    -- excluding nothing is the universe again
    coFiniteStr [] = StrUniverse
    coFiniteStr ts = StrCoFinite ts

    strOp "++" StrUniverse _ = Right StrUniverse
    strOp "++" _ StrUniverse = Right StrUniverse
    strOp "++" (StrFinite a)   (StrFinite b)   = Right $ StrFinite $ nub $ a ++ b
    strOp "++" (StrCoFinite a) (StrFinite b)   = Right $ coFiniteStr $ a \\ b            -- ¬a ∪ b = ¬(a − b)
    strOp "++" (StrFinite a)   (StrCoFinite b) = Right $ coFiniteStr $ b \\ a            -- a ∪ ¬b = ¬(b − a)
    strOp "++" (StrCoFinite a) (StrCoFinite b) = Right $ coFiniteStr $ a `intersect` b  -- ¬a ∪ ¬b = ¬(a ∩ b)
    strOp "**" StrUniverse x = Right x
    strOp "**" x StrUniverse = Right x
    strOp "**" (StrFinite a)   (StrFinite b)   = finiteStr $ a `intersect` b
    strOp "**" (StrCoFinite a) (StrFinite b)   = finiteStr $ b \\ a                    -- ¬a ∩ b = b − a
    strOp "**" (StrFinite a)   (StrCoFinite b) = finiteStr $ a \\ b                    -- a ∩ ¬b = a − b
    strOp "**" (StrCoFinite a) (StrCoFinite b) = Right $ StrCoFinite $ nub $ a ++ b     -- ¬a ∩ ¬b = ¬(a ∪ b)
    strOp "--" _ StrUniverse = Left "an empty set of strings (`-- string`)"
    strOp "--" StrUniverse (StrFinite a)   = Right $ StrCoFinite a
    strOp "--" StrUniverse (StrCoFinite a) = Right $ StrFinite a                        -- U − ¬a = a
    strOp "--" (StrFinite a)   (StrFinite b)   = finiteStr $ a \\ b
    strOp "--" (StrCoFinite a) (StrFinite b)   = Right $ StrCoFinite $ nub $ a ++ b     -- ¬a − b = ¬(a ∪ b)
    strOp "--" (StrFinite a)   (StrCoFinite b) = finiteStr $ a `intersect` b            -- a − ¬b = a ∩ b
    strOp "--" (StrCoFinite a) (StrCoFinite b) = finiteStr $ b \\ a                    -- ¬a − ¬b = b − a
    strOp op' _ _ = Left $ "the operator " ++ op' ++ " over string sets"

    setOp "++" a b = "union(" ++ a ++ ", " ++ b ++ ")"
    setOp "**" a b = "inter(" ++ a ++ ", " ++ b ++ ")"
    setOp _    a b = "diff(" ++ a ++ ", " ++ b ++ ")"

    intOp "++" IntUniverse _ = Right IntUniverse
    intOp "++" _ IntUniverse = Right IntUniverse
    intOp "++" (IntFinite a)   (IntFinite b)   = Right $ IntFinite   $ setOp "++" a b
    intOp "++" (IntCoFinite a) (IntFinite b)   = Right $ IntCoFinite $ setOp "--" a b  -- ¬a ∪ b = ¬(a − b)
    intOp "++" (IntFinite a)   (IntCoFinite b) = Right $ IntCoFinite $ setOp "--" b a  -- a ∪ ¬b = ¬(b − a)
    intOp "++" (IntCoFinite a) (IntCoFinite b) = Right $ IntCoFinite $ setOp "**" a b  -- ¬a ∪ ¬b = ¬(a ∩ b)
    intOp "**" IntUniverse x = Right x
    intOp "**" x IntUniverse = Right x
    intOp "**" (IntFinite a)   (IntFinite b)   = Right $ IntFinite   $ setOp "**" a b
    intOp "**" (IntCoFinite a) (IntFinite b)   = Right $ IntFinite   $ setOp "--" b a  -- ¬a ∩ b = b − a
    intOp "**" (IntFinite a)   (IntCoFinite b) = Right $ IntFinite   $ setOp "--" a b  -- a ∩ ¬b = a − b
    intOp "**" (IntCoFinite a) (IntCoFinite b) = Right $ IntCoFinite $ setOp "++" a b  -- ¬a ∩ ¬b = ¬(a ∪ b)
    intOp "--" _ IntUniverse = Left "an empty set of integers (`-- integer`)"
    intOp "--" IntUniverse (IntFinite a)   = Right $ IntCoFinite a
    intOp "--" IntUniverse (IntCoFinite a) = Right $ IntFinite a                        -- U − ¬a = a
    intOp "--" (IntFinite a)   (IntFinite b)   = Right $ IntFinite   $ setOp "--" a b
    intOp "--" (IntCoFinite a) (IntFinite b)   = Right $ IntCoFinite $ setOp "++" a b  -- ¬a − b = ¬(a ∪ b)
    intOp "--" (IntFinite a)   (IntCoFinite b) = Right $ IntFinite   $ setOp "**" a b  -- a − ¬b = a ∩ b
    intOp "--" (IntCoFinite a) (IntCoFinite b) = Right $ IntFinite   $ setOp "--" b a  -- ¬a − ¬b = b − a
    intOp op' _ _ = Left $ "the operator " ++ op' ++ " over integer sets"

-- | The reference-declaring clafers whose target the Choco backend
-- cannot express, each with the reason (Sigil-Logic/clafer#18).
-- Language.Clafer.generate declines Choco output for a model with any,
-- through the same unsupported-feature path it uses for reals, instead
-- of emitting a silently under-constrained model.
chocoUnsupportedRefTargets :: IModule -> [(UID, String)]
chocoUnsupportedRefTargets iModule =
  [ (_uid, why)
  | IClafer{_uid, _reference = Just IReference{_ref = refExp}} <- (universeOn biplate iModule :: [IClafer])
  , not $ isPlainRefTarget refExp
  , Left why <- [classifyRefTarget (const "") refExp] ]

-- | Choco 3 code generation
genCModule :: (IModule, GEnv) -> [(UID, Integer)] -> [Token]     -> Result
genCModule (imodule@IModule{_mDecls}, genv') scopes  otherTokens' =
    genScopes
    ++ "\n"
    ++ (genClafers =<< _mDecls)
    ++ (genSuperRefConstraintAssertGoal "root" =<< _mDecls)
    ++ genChocoEscapes
    where
    uidIClaferMap' = uidClaferMap genv'

    genClafers :: IElement -> String
    genClafers    (IEClafer (c@IClafer{_uid, _gcard, _elements}))
        = _uid
        ++ genClaferNesting c
        ++ prop "withGroupCard" (genCard $ _interval <$> _gcard)
        ++ ";\n"
        ++ (genClafers =<< _elements)
    genClafers    _ = ""

    genClaferNesting (IClafer{_modifiers=IClaferModifiers{_abstract=True}, _uid, _parentUID="clafer"})
        = " = Abstract(\"" ++ _uid ++ "\")"
    genClaferNesting (IClafer{_modifiers=IClaferModifiers{_abstract=True}, _uid, _parentUID})
        = " = " ++ _parentUID ++  ".addAbstractChild(\"" ++ _uid ++ "\")"
    genClaferNesting (IClafer{_modifiers=IClaferModifiers{_abstract=False}, _uid, _card, _parentUID="root"})
        = " = Clafer(\"" ++ _uid ++ "\")"
        ++ prop "withCard" (genCard _card)
    genClaferNesting (IClafer{_modifiers=IClaferModifiers{_abstract=False}, _uid, _card, _parentUID})
        = " = "
        ++ _parentUID
        ++  ".addChild(\"" ++ _uid ++ "\")"
        ++ prop "withCard" (genCard _card)

    prop name value =
        case value of
                Just value' -> "." ++ name ++ "(" ++ value' ++ ")"
                Nothing     -> ""

    claferWithUid u = fromMaybe (error $ "claferWithUid: \"" ++ u ++ "\" is not a clafer") $ findIClafer uidIClaferMap' u

    superOf u =
        case _super $ claferWithUid u of
            Just (PExp{_exp = IClaferId{_sident}})
                | _sident == baseClafer -> Nothing
                | isPrimitive _sident   -> Nothing
                | otherwise             -> Just _sident
            _ -> Nothing

    genCard :: Maybe Interval -> Maybe String
    genCard (Just (0, -1)) = Nothing
    genCard (Just (low, -1)) = return $ show low
    genCard (Just (low, high)) = return $ show low ++ ", " ++ show high
    genCard _              = Nothing


    genScopes :: Result
    genScopes =
        (if null scopeMap then "" else "scope({" ++ intercalate ", " scopeMap ++ "});\n")
        ++ "defaultScope(1);\n"
        ++ "intRange(-" ++ show largestPositiveInt ++ ", " ++ show (largestPositiveInt - 1) ++ ");\n"
        ++ "stringLength(" ++ show longestString ++ ");\n"
        where
            largestPositiveInt :: Integer
            largestPositiveInt = 2 ^ (bitwidth - 1)
            scopeMap = [uid' ++ ":" ++ show scope | (uid', scope) <- scopes, uid' /= "int"]

    genChocoEscapes :: String
    genChocoEscapes = concatMap printChocoEscape otherTokens'
        where
            printChocoEscape (PT _ (T_PosChoco code)) =  let
                code' = fromJust $ stripPrefix "[choco|" code
              in
                take (length code' - 2) code'
            printChocoEscape _                        = ""

    exprs :: [IExp]
    exprs = universeOn biplate imodule

    stringLength :: IExp -> Maybe Int
    stringLength (IStr string) = Just $ length string
    stringLength _ = Nothing

    longestString :: Int
    longestString = maximum $ 16 : mapMaybe stringLength exprs

    genSuperRefConstraintAssertGoal :: String -> IElement -> Result
    genSuperRefConstraintAssertGoal _ IEClafer{_iClafer=IClafer{_uid, _super=Nothing, _reference=Nothing, _elements}}
        = genSuperRefConstraintAssertGoal _uid =<< _elements
    genSuperRefConstraintAssertGoal _ (IEClafer IClafer{_uid, _super, _reference, _elements})
        = _uid
        ++ prop "extending" (superOf _uid)
        ++ refClause
        ++ ";\n"
        ++ refRestriction
        ++ (genSuperRefConstraintAssertGoal _uid =<< _elements)
        where
            (refClause, refRestriction) = maybe ("", "") (genRefTarget _uid) _reference
    genSuperRefConstraintAssertGoal "root" (IEConstraint True pexp) = "Constraint(" ++ genConstraintPExp pexp ++ ");\n"
    genSuperRefConstraintAssertGoal pUID (IEConstraint True pexp) = pUID ++ ".addConstraint(" ++ genConstraintPExp pexp ++ ");\n"
    genSuperRefConstraintAssertGoal _ (IEConstraint False pexp) = "assert(" ++ genConstraintPExp pexp ++ ");\n"
    genSuperRefConstraintAssertGoal _ (IEGoal True PExp{_exp=IFunExp _ [pexp]})  = "max(" ++ genConstraintPExp pexp ++ ");\n"
    genSuperRefConstraintAssertGoal _ (IEGoal False PExp{_exp=IFunExp _ [pexp]})  = "min(" ++ genConstraintPExp pexp ++ ");\n"
    genSuperRefConstraintAssertGoal _ _ = ""

    -- | Reference-target emission (Sigil-Logic/clafer#18): the
    -- .refTo/.refToUnique clause, and -- for a target that is not a
    -- plain clafer -- the constraint restricting the referred value to
    -- the target set, as its own statement after the clause.  Before
    -- #18 every non-plain target was dropped (a bare `cN_uid;`
    -- statement, or the primitive type without its literal).
    genRefTarget :: UID -> IReference -> (String, String)
    genRefTarget uid' IReference{_isSet, _ref = refExp} =
        case encodeRefTarget refExp of
            Right (carrier, restriction) ->
                ( (if _isSet then ".refToUnique(" else ".refTo(") ++ carrier ++ ")"
                , maybe "" (\r -> uid' ++ ".addConstraint(" ++ r ++ ");\n") restriction )
            Left why -> error $ "[bug] Choco.genRefTarget: " ++ uid' ++ " refers to " ++ why
                                ++ "; Language.Clafer.generate must decline Choco output for this model (chocoUnsupportedRefTargets)"

    -- | The carrier type and the optional restriction of a reference target.
    encodeRefTarget :: PExp -> Either String (String, Maybe String)
    encodeRefTarget refExp
        | isPlainRefTarget refExp = Right (genTarget $ plainRefTargetId refExp, Nothing)
        | otherwise = encode <$> classifyRefTarget genConstraintPExp refExp
        where
            encode (ClaferSet uids js)       = (carrierOf uids, Just $ "$in(" ++ thisRef ++ ", " ++ js ++ ")")
            encode (IntSet IntUniverse)      = ("Int", Nothing)
            encode (IntSet (IntFinite js))   = ("Int", Just $ "$in(" ++ thisRef ++ ", " ++ js ++ ")")
            encode (IntSet (IntCoFinite js)) = ("Int", Just $ "notIn(" ++ thisRef ++ ", " ++ js ++ ")")
            -- chocosolver rejects a union of string constants, so a
            -- string enumeration is a disjunction of equalities and a
            -- co-finite string set a conjunction of inequalities
            encode (StrSet StrUniverse)      = ("string", Nothing)
            encode (StrSet (StrFinite ts))   = ("string", Just $ strFormula "or" "equal" ts)
            encode (StrSet (StrCoFinite ts)) = ("string", Just $ strFormula "and" "notEqual" ts)
            strFormula conn test ts = foldl1 (\acc e -> conn ++ "(" ++ acc ++ ", " ++ e ++ ")")
                                        [ test ++ "(" ++ thisRef ++ ", constant(" ++ show t ++ "))" | t <- ts ]
            thisRef = "joinRef($this())"

    plainRefTargetId PExp{_exp = IClaferId{_sident}} = _sident
    plainRefTargetId PExp{_exp = IFunExp "." [_, r]} = plainRefTargetId r
    plainRefTargetId p = error $ "[bug] Choco.plainRefTargetId: not a plain reference target: " ++ show p

    genTarget "integer" = "Int"
    genTarget "int" = "Int"
    genTarget target = target

    -- | The least common super clafer of the candidate carriers, or
    -- chocosolver's universal type root when they share none (a union
    -- of unrelated clafers).
    carrierOf :: [UID] -> String
    carrierOf uids = case nub uids of
        []     -> typeRoot
        (u:us) -> case [ a | a <- superChain u, all (elem a . superChain) us ] of
            (a:_) -> a
            []    -> typeRoot
        where typeRoot = "rc.getModel().getTypeRoot()"

    superChain :: UID -> [UID]
    superChain u = u : maybe [] superChain (superOf u)


    rewrite :: PExp -> PExp
    -- Rearrange right joins to left joins.
    rewrite p1@PExp{_iType = Just _, _exp = IFunExp "." [p2, p3@PExp{_exp = IFunExp "." _}]} =
        p1{_exp = IFunExp "." [p3{_iType = _iType p4, _exp = IFunExp "." [p2, p4]}, p5]}
        where
            PExp{_exp = IFunExp "." [p4, p5]} = rewrite p3
    -- Fold unary minus over a literal into the literal (Common.negateLiteral,
    -- shared with the reference-target classifier, Sigil-Logic/clafer#31).
    -- This is so that the output looks cleaner, no other purpose since the
    -- Choco optimizer in the backend will treat the pre-rewritten expression
    -- the same.
    rewrite p = negateLiteral p

    genConstraintPExp :: PExp -> String
    genConstraintPExp = genConstraintExp . _exp . rewrite

    genConstraintExp :: IExp -> String
    genConstraintExp (IDeclPExp quant' [] body') =
        mapQuant quant' ++ "(" ++ genConstraintPExp body' ++ ")"
    genConstraintExp (IDeclPExp quant' decls' body') =
        mapQuant quant' ++ "([" ++ intercalate ", " (map genDecl decls') ++ "], " ++ genConstraintPExp body' ++ ")"
        where
            genDecl (IDecl isDisj' locals body'') =
                (if isDisj' then "disjDecl" else "decl") ++ "([" ++ intercalate ", " (map genLocal locals) ++ "], " ++ genConstraintPExp body'' ++ ")"
            genLocal local =
                local ++ " = local(\"" ++ local ++ "\")"

    genConstraintExp (IFunExp "." [PExp{_exp = IClaferId{_sident = "root"}}, e2]) =
        genConstraintPExp e2
    genConstraintExp (IFunExp "." [e1, PExp{_exp = IClaferId{_sident = "dref"}}]) =
        "joinRef(" ++ genConstraintPExp e1 ++ ")"
    genConstraintExp (IFunExp "." [e1, PExp{_exp = IClaferId{_sident = "parent"}}]) =
        "joinParent(" ++ genConstraintPExp e1 ++ ")"
    genConstraintExp (IFunExp "." [e1, PExp{_exp = IClaferId{_sident}}]) =
        "join(" ++ genConstraintPExp e1 ++ ", " ++ _sident ++ ")"
    genConstraintExp (IFunExp "." [_, _]) =
        error "Did not rewrite all joins to left joins."
    genConstraintExp (IFunExp "-" [arg]) =
        "minus(" ++ genConstraintPExp arg ++ ")"
    genConstraintExp (IFunExp "-" [arg1, arg2]) =
        "sub(" ++ genConstraintPExp arg1 ++ ", " ++ genConstraintPExp arg2 ++ ")"
    genConstraintExp (IFunExp "sum" args')
        | [arg] <- args', PExp{_exp = IFunExp{_exps = [a, PExp{_exp = IClaferId{_sident = "dref"}}]}} <- rewrite arg =
            "sum(" ++ genConstraintPExp a ++ ")"
        | [arg] <- args' =
            "sum(" ++ genConstraintPExp arg ++ ")"
        | otherwise = error $ "[bug] Choco.genConstraintExp: Unexpected sum argument: " ++ show args'
    genConstraintExp (IFunExp "product" args')
        | [arg] <- args', PExp{_exp = IFunExp{_exps = [a, PExp{_exp = IClaferId{_sident = "dref"}}]}} <- rewrite arg =
            "product(" ++ genConstraintPExp a ++ ")"
        | otherwise = error "Choco: Unexpected product argument."
    genConstraintExp (IFunExp "+" args') =
        (if _iType (head args') == Just TString then "concat" else "add") ++
            "(" ++ intercalate ", " (map genConstraintPExp args') ++ ")"
    genConstraintExp (IFunExp op' args') =
        mapFunc op' ++ "(" ++ intercalate ", " (map genConstraintPExp args') ++ ")"
    -- this is a keyword in Javascript so use "$this" instead
    genConstraintExp IClaferId{_sident = "this"} = "$this()"
    -- a locally bound identifier (a quantifier variable) is a local
    -- whatever it is called: its name may coincide with a clafer UID
    -- (`all c0_Target : Thing | ...`) without referring to that clafer,
    -- and the name lookup below would then emit it as global
    -- (Sigil-Logic/clafer PR #28, HOARDE Codex Cycle 1)
    genConstraintExp IClaferId{_sident, _binding = LocalBind _} = _sident
    genConstraintExp IClaferId{_sident}
        | isJust $ findIClafer uidIClaferMap' _sident = "global(" ++ _sident ++ ")"
        | otherwise                = _sident
    genConstraintExp (IInt val) = "constant(" ++ show val ++ ")"
    genConstraintExp (IStr val) = "constant(" ++ show val ++ ")"
    genConstraintExp (IDouble val) = "constant(" ++ show val ++ ")"
    genConstraintExp (IReal val) = "constant(" ++ show val ++ ")"

    mapQuant INo = "none"
    mapQuant ISome = "some"
    mapQuant IAll = "all"
    mapQuant IOne = "one"
    mapQuant ILone = "lone"

    mapFunc "!" = "not"
    mapFunc "#" = "card"
    mapFunc "min" = "minimum"
    mapFunc "max" = "maximum"
    mapFunc "<=>" = "ifOnlyIf"
    mapFunc "=>" = "implies"
    mapFunc "||" = "or"
    mapFunc "xor" = "xor"
    mapFunc "&&" = "and"
    mapFunc "<" = "lessThan"
    mapFunc ">" = "greaterThan"
    mapFunc "=" = "equal"
    mapFunc "<=" = "lessThanEqual"
    mapFunc ">=" = "greaterThanEqual"
    mapFunc "!=" = "notEqual"
    mapFunc "in" = "$in"
    mapFunc "not in" = "notIn"
    mapFunc "+" = "add"
    mapFunc "*" = "mul"
    mapFunc "/" = "div"
    mapFunc "%" = "mod"
    mapFunc "++" = "union"
    mapFunc "--" = "diff"
    mapFunc "**" = "inter"
    mapFunc "ifthenelse" = "ifThenElse"
    mapFunc op' = error $ "Choco: Unknown op: " ++ op'

    bitwidth = fromMaybe 4 $ lookup "int" scopes :: Integer
