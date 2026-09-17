{-
 Copyright (C) 2012 Christopher Walker, Michal Antkiewicz <http://gsd.uwaterloo.ca>

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
-- | Generates HTML and plain text rendering of a Clafer model.
module Language.Clafer.Generator.Html
  ( genHtml
  , genText
  , genTooltip
  , printModule
  , printDeclaration
  , printDecl
  , traceAstModule
  , traceIrModule
  , cleanOutput
  , revertLayout
  , printComment
  , printPreComment
  , printStandaloneComment
  , printInlineComment
  , highlightErrors
  ) where

import Language.ClaferT
import Language.Clafer.Front.AbsClafer as AbsClafer
import Language.Clafer.Front.LayoutResolver(revertLayout)
import Language.Clafer.Intermediate.Tracing
import Language.Clafer.Intermediate.Intclafer

import Control.Applicative
import Data.List (intersperse,genericSplitAt)
import qualified Data.Map as Map
import Data.Maybe
import Data.Char (isSpace)
import Prelude hiding (exp)

printPreComment :: Span -> [(Span, String)] -> ([(Span, String)], String)
printPreComment _ [] = ([], [])
printPreComment (Span (Pos r _) _) (c@((Span (Pos r' _) _), _):cs)
  | r > r' = findAll r (c:cs, [])
  | otherwise  = (c:cs, "")
    where findAll _ ([],comments) = ([],comments)
          findAll row ((c'@((Span (Pos row' col') _), comment):cs'), comments)
            | row > row' = case take 3 comment of
                ['/', '/', '#'] -> findAll row (cs', concat [comments, "<!-- " ++ trim (drop 2 comment) ++ " /-->\n"])
                ['/', '/', _]   -> if col' == 1
                                   then findAll row (cs', concat [comments, printStandaloneComment comment ++ "\n"])
                                   else findAll row (cs', concat [comments, printInlineComment comment ++ "\n"])
                ['/', '*', _]   -> findAll row (cs', concat [comments, printStandaloneComment comment ++ "\n"])
                _      -> (cs', "")
            | otherwise  = (c':cs', comments)
printComment :: Span -> [(Span, String)] -> ([(Span, String)], String)
printComment _ [] = ([],[])
printComment (Span (Pos row _) _) (c@(Span (Pos row' col') _, comment):cs)
  | row == row' = case take 3 comment of
        ['/', '/', '#'] -> (cs,"<!-- " ++ trim' (drop 2 comment) ++ " /-->\n")
        ['/', '/', _]   -> if col' == 1
                           then (cs, printStandaloneComment comment ++ "\n")
                           else (cs, printInlineComment comment ++ "\n")
        ['/', '*', _]   -> (cs, printStandaloneComment comment ++ "\n")
        _      -> (cs, "")
  | otherwise = (c:cs, "")
  where trim' = let f = reverse. dropWhile isSpace in f . f
printStandaloneComment :: String -> String
printStandaloneComment comment = "<div class=\"standalonecomment\">" ++ replaceNLwithBR comment ++ "</div>"
  where
    replaceNLwithBR :: String   -> String
    replaceNLwithBR    ""        = ""
    replaceNLwithBR    ('\n':cs) = "<br>\n" ++ replaceNLwithBR cs
    replaceNLwithBR    (c:cs)    = c : replaceNLwithBR cs


printInlineComment :: String -> String
printInlineComment comment = "<span class=\"inlinecomment\">" ++ comment ++ "</span>"

printDeprecated :: String -> String -> Bool -> String
printDeprecated    s         m         html = while html ("<span class=\"deprecated\" title=\"" ++ "Deprecated. " ++ m ++ "\">")
                                              ++ s
                                              ++ while html "</span>"

-- | Generate the model as HTML document
genHtml :: Module -> IModule -> String
genHtml x ir = cleanOutput $ revertLayout $ printModule x (traceIrModule ir) True
-- | Generate the model as plain text
-- | This is used by the graph generator for tooltips
genText :: Module -> IModule -> String
genText x ir = cleanOutput $ revertLayout $ printModule x (traceIrModule ir) False
genTooltip :: Module -> Map.Map Span [Ir] -> String
genTooltip m ir = unlines $ filter (\x -> trim x /= []) $ lines $ cleanOutput $ revertLayout $ printModule m ir False

printModule :: Module -> Map.Map Span [Ir] -> Bool -> String
printModule (Module _ [])     _ _ = ""
printModule (Module s (x:xs)) irMap html = printDeclaration x 0 irMap html [] ++ printModule (Module s xs) irMap html

printDeclaration :: Declaration -> Int -> Map.Map Span [Ir] -> Bool -> [(Span, String)] -> String
printDeclaration (EnumDecl s posIdent enumIds)  indent irMap html comments =
    preComments ++
    printIndentId 0 html ++
    while html "<span class=\"keyword\">" ++ "enum" ++ while html "</span>" ++
    " " ++
    printPosIdent posIdent mUid' html ++
    " = " ++
    concat (intersperse " | " (map (\x -> printEnumId x indent irMap html comments) enumIds)) ++
    comment ++
    printIndentEnd html
  where
    mUid' = getUid posIdent irMap;
    (comments', preComments) = printPreComment s comments;
    (_, comment) = printComment s comments'
printDeclaration (ElementDecl _ element) indent irMap html comments = printElement element indent irMap html comments

printElement :: Element -> Int -> Map.Map Span [Ir] -> Bool -> [(Span, String)] -> String
printElement (Subclafer _ clafer) indent irMap html comments = printClafer clafer indent irMap html comments

printElement (ClaferUse s name crd es) indent irMap html comments =
  preComments ++
  printIndentId indent html ++
  "`" ++ while html ("<a href=\"#" ++ superId ++ "\"><span class=\"reference\">") ++
  printName name indent irMap False [] --trick the printer into only printing the name
  ++ while html "</span></a>" ++
  printCard crd ++
  comment ++
  printIndentEnd html ++
  printElements es indent irMap html comments''
  where
    (_, superId) = getUseId s irMap;
    (comments', preComments) = printPreComment s comments;
    (comments'', comment) = printComment s comments'

printElement (Subgoal s goal) indent irMap html comments =
  preComments ++
  printIndent 0 html ++
  printGoal goal indent irMap html comments'' ++
  comment ++
  printIndentEnd html
  where
   (comments', preComments) = printPreComment s comments;
   (comments'', comment) = printComment s comments'

printElement (Subconstraint s constraint) indent irMap html comments =
    preComments ++
    printIndent indent html ++
    printConstraint constraint indent irMap html comments'' ++
    comment ++
    printIndentEnd html
  where
    (comments', preComments) = printPreComment s comments;
    (comments'', comment) = printComment s comments'

printElement (SubAssertion s constraint) indent irMap html comments =
    preComments ++
    printIndent indent html ++
    printAssertion constraint indent irMap html comments'' ++
    comment ++
    printIndentEnd html
  where
    (comments', preComments) = printPreComment s comments;
    (comments'', comment) = printComment s comments'

printElements :: Elements -> Int -> Map.Map Span [Ir] -> Bool -> [(Span, String)] -> String
printElements (ElementsEmpty _) _ _ _ _ = ""
printElements (ElementsList _ es) indent irMap html comments = "\n{" ++ mapElements es indent irMap html comments ++ "\n}"
    where mapElements []     _ _ _ _ = []
          mapElements (e':es') indent' irMap' html' comments'
            = if span' e' == noSpan
              then printElement e' (indent' + 1) irMap' html' comments' {-++ "\n"-} ++ mapElements es' indent' irMap' html' comments'
              else printElement e' (indent' + 1) irMap' html' comments' {-++ "\n"-} ++ mapElements es' indent' irMap' html' (afterSpan (span' e') comments')
          afterSpan s comments' = let (Span _ (Pos line _)) = s in dropWhile (\(x, _) -> let (Span _ (Pos line' _)) = x in line' <= line) comments'
          span' (Subclafer s _) = s
          span' (Subconstraint s _) = s
          span' (ClaferUse s _ _ _) = s
          span' (Subgoal s _) = s
          span' (SubAssertion s _) = s

printClafer :: Clafer -> Int -> Map.Map Span [Ir] -> Bool -> [(Span, String)] -> String
printClafer (Clafer s abstract' tmod' gCard id' super' reference' crd init' trans' es) indent irMap html comments =
  preComments ++
  printIndentId indent html ++
  claferDeclaration ++
  comment ++
  printElements es indent irMap html comments'' ++
  printIndentEnd html
  where
    uid' = getDivId s irMap;
    (comments', preComments) = printPreComment s comments;
    (comments'', comment) = printComment s comments'
    claferDeclaration = concat [
      printAbstract abstract' html,
      printModifiers tmod' html,
      printGCard gCard html,
      printPosIdent id' (Just uid') html,
      printSuper super' indent irMap html comments,
      printReference reference' indent irMap html comments,
      printCard crd,
      printInit init' indent irMap html comments,
      printTransition trans' indent irMap html comments]

printGoal :: Goal -> Int -> Map.Map Span [Ir] -> Bool -> [(Span, String)] -> String
printGoal goal indent irMap html comments =
  (if html then "&lt;&lt;" else "<<") ++
  (case goal of
    (GoalMinimize _ exps') -> while html "<span class=\"keyword\">" ++ "minimize " ++ while html "</span>" ++ concatMap (\x -> printExp x indent irMap html comments) exps'
    (GoalMaximize _ exps') -> while html "<span class=\"keyword\">" ++ "maximize " ++ while html "</span>" ++ concatMap (\x -> printExp x indent irMap html comments) exps'
    (GoalMinDeprecated _ exps') -> printDeprecated "min " "Use `minimize` instead." html ++ concatMap (\x -> printExp x indent irMap html comments) exps'
    (GoalMaxDeprecated _ exps') -> printDeprecated "max " "Use `maximize` instead." html ++ concatMap (\x -> printExp x indent irMap html comments) exps'
  ) ++
  if html then "&gt;&gt;" else ">>"

printAbstract :: Abstract -> Bool -> String
printAbstract (Abstract _) html   = while html "<span class=\"keyword\">" ++ "abstract" ++ while html "</span>" ++ " "
printAbstract (AbstractEmpty _) _ = ""

printModifiers :: [TempModifier] -> Bool -> String
printModifiers tmods' html = concatMap printTempMod tmods'
  where
    printTempMod (AbsClafer.Final _)       = while html "<span class=\"tKeyword\">" ++ "final" ++ while html "</span>" ++ " "
    printTempMod (AbsClafer.FinalRef _)    = while html "<span class=\"tKeyword\">" ++ "finalref" ++ while html "</span>" ++ " "
    printTempMod (AbsClafer.FinalTarget _) = while html "<span class=\"tKeyword\">" ++ "finaltarget" ++ while html "</span>" ++ " "
    printTempMod (Initial _)               = while html "<span class=\"tKeyword\">" ++ "initial" ++ while html "</span>" ++ " "

printGCard :: GCard -> Bool -> String
printGCard gCard html = case gCard of
  (GCardInterval _ ncard) -> printNCard ncard
  (GCardEmpty _)          -> ""
  (GCardXor _)            -> while html "<span class=\"keyword\">" ++ "xor" ++ while html "</span>" ++ " "
  (GCardOr _)             -> while html "<span class=\"keyword\">" ++ "or"  ++ while html "</span>" ++ " "
  (GCardMux _)            -> while html "<span class=\"keyword\">" ++ "mux" ++ while html "</span>" ++ " "
  (GCardOpt _)            -> while html "<span class=\"keyword\">" ++ "opt" ++ while html "</span>" ++ " "

printNCard :: NCard -> String
printNCard (NCard _ (PosInteger (_, num)) exInteger) = num ++ ".." ++ printExInteger exInteger ++ " "

printExInteger :: ExInteger -> String
printExInteger (ExIntegerAst _) = "*"
printExInteger (ExIntegerNum _ (PosInteger(_, num))) = num

printName :: Name -> Int -> Map.Map Span [Ir] -> Bool -> [(Span, String)] -> String
printName (Path _ modids) indent irMap html comments = unwords $ map (\x -> printModId x indent irMap html comments) modids

printModId :: ModId -> Int -> Map.Map Span [Ir] -> Bool -> [(Span, String)] -> String
printModId (ModIdIdent _ posident) _ irMap html _ = printPosIdentRef posident irMap html

printPosIdent :: PosIdent -> Maybe String -> Bool -> String
printPosIdent (PosIdent (_, id')) Nothing _ = id'
printPosIdent (PosIdent (_, id')) (Just uid') html = while html ("<span class=\"claferDecl\" id=\"" ++ uid' ++ "\">") ++ id' ++ while html "</span>"

printPosIdentRef :: PosIdent -> Map.Map Span [Ir] -> Bool -> String
printPosIdentRef (PosIdent (_, "dref")) _ html
  = while html "<span class=\"keyword\">" ++ "dref" ++ while html "</span>"
printPosIdentRef (PosIdent (_, "this")) _ html
  = while html "<span class=\"keyword\">" ++ "this" ++ while html "</span>"
printPosIdentRef (PosIdent (_, "parent")) _ html
  = while html "<span class=\"keyword\">" ++ "parent" ++ while html "</span>"
printPosIdentRef (PosIdent (_, "root")) _ html
  = while html "<span class=\"keyword\">" ++ "root" ++ while html "</span>"
printPosIdentRef (PosIdent (_, "ref")) _ html
  = printDeprecated "ref" "Use `dref` instead." html
printPosIdentRef (PosIdent (_, id')) _     False = id'
printPosIdentRef (PosIdent (p, id')) irMap True
  = case mUid' of
      Just uid' -> "<a href=\"#" ++ uid' ++ "\"><span class=\"reference\">" ++ id' ++ "</span></a>"
      Nothing   -> id'
  where
    mUid' = getUid (PosIdent (p, id')) irMap

printSuper :: Super -> Int -> Map.Map Span [Ir] -> Bool -> [(Span, String)] -> String
printSuper (SuperEmpty _) _ _ _ _ = ""
printSuper (SuperSome _ setExp) indent irMap html comments =
  while html "<span class=\"keyword\">" ++ " : " ++ while html "</span>" ++
  fromMaybe (printExpIn 26 setExp indent irMap html comments) linkedPath
  where
    -- Sigil-Logic/clafer#29: a dotted path names its target through the
    -- resolver's single normalized reference, not per-segment trace entries
    linkedPath = case setExp of
      EJoin s _ _ | html -> printSuperPath s setExp irMap
      _                  -> Nothing

-- | Render a dotted super-type path (@Person.Head@) with every segment linked
-- to the clafer it names.  The resolver resolves such a path by direct-child
-- navigation and traces only the target, so segment @i@ is recovered as the
-- @i@-th innermost ancestor of the target (the target itself last).  Nothing
-- when the trace holds no resolved target for the span or the ancestry is
-- shorter than the path, in which case the caller prints the plain text.
printSuperPath :: Span -> Exp -> Map.Map Span [Ir] -> Maybe String
printSuperPath s setExp irMap = do
  segments <- pathSegments setExp
  target   <- traceSuperUid s irMap
  let chain = reverse $ take (length segments) $ ancestry target
  if length chain == length segments
    then Just $ foldr1 (\a b -> a ++ "." ++ b)
           [ "<a href=\"#" ++ uid' ++ "\"><span class=\"reference\">" ++ ident' ++ "</span></a>" | (uid', ident') <- zip chain segments ]
    else Nothing
  where
    clafers = Map.fromList [ (_uid c, c) | irs <- Map.elems irMap, IRClafer c <- irs ]
    -- the clafer and its ancestors, innermost first, up to the top level
    ancestry uid' = uid' : maybe [] (ancestry . _parentUID) (Map.lookup uid' clafers)
    pathSegments (ClaferId _ (Path _ [ModIdIdent _ (PosIdent (_, ident'))])) = Just [ident']
    pathSegments (EJoin _ l r) = (++) <$> pathSegments l <*> pathSegments r
    pathSegments _ = Nothing

printReference :: Reference -> Int -> Map.Map Span [Ir] -> Bool -> [(Span, String)] -> String
printReference (ReferenceEmpty _) _ _ _ _ = ""
printReference (ReferenceSet _ setExp) indent irMap html comments = while html "<span class=\"keyword\">" ++ " -> " ++ while html "</span>" ++ printExpIn 23 setExp indent irMap html comments
printReference (ReferenceBag _ setExp) indent irMap html comments = while html "<span class=\"keyword\">" ++ " ->> " ++ while html "</span>" ++ printExpIn 23 setExp indent irMap html comments


printCard :: Card -> String
printCard (CardEmpty _) = ""
printCard (CardLone _)  = " ?"
printCard (CardSome _)  = " +"
printCard (CardAny _)   = " *"
printCard (CardNum _ (PosInteger (_,num))) = " " ++ num
printCard (CardInterval _ nCard) = " " ++ printNCard nCard

printConstraint ::  Constraint -> Int -> Map.Map Span [Ir] -> Bool -> [(Span, String)] -> String
printConstraint (Constraint _ exps') indent irMap html comments = concatMap (\x -> printConstraint' x indent irMap html comments) exps'

printConstraint' :: Exp -> Int -> Map.Map Span [Ir] -> Bool -> [(Span, String)] -> String
printConstraint' exp' indent irMap html comments =
    while html "<span class=\"keyword\">" ++ "[" ++ while html "</span>" ++
    " " ++
    printExp exp' indent irMap html comments ++
    " " ++
    while html "<span class=\"keyword\">" ++ "]" ++ while html "</span>"

printAssertion :: Assertion -> Int -> Map.Map Span [Ir] -> Bool -> [(Span, String)] -> String
printAssertion (Assertion _ exps') indent irMap html comments = concatMap (\x -> printAssertion' x indent irMap html comments) exps'
printAssertion' :: Exp -> Int -> Map.Map Span [Ir] -> Bool -> [(Span, String)] -> String
printAssertion' exp' indent' irMap html comments =
    while html "<span class=\"keyword\">" ++ "assert [" ++ while html "</span>" ++
    " " ++
    printExp exp' indent' irMap html comments ++
    " " ++
    while html "<span class=\"keyword\">" ++ "]" ++ while html "</span>"

printDecl :: Decl-> Int -> Map.Map Span [Ir] -> Bool -> [(Span, String)] -> String
printDecl (Decl _ locids setExp) indent irMap html comments =
  concat (intersperse "; " $ map printLocId locids) ++
  while html "<span class=\"keyword\">" ++ " : " ++ while html "</span>" ++ printExpIn 21 setExp indent irMap html comments
  where
    printLocId :: LocId -> String
    printLocId (LocIdIdent _ (PosIdent (_, ident'))) = ident'

printVarBinding :: VarBinding-> Int -> Map.Map Span [Ir] -> Bool -> [(Span, String)] -> String
printVarBinding (VarBinding _ locid name) indent irMap html comments =
  printLocId locid ++
  while html "<span class=\"keyword\">" ++ " = " ++ while html "</span>" ++
  printName name indent irMap html comments
  where
    printLocId :: LocId -> String
    printLocId (LocIdIdent _ (PosIdent (_, ident'))) = ident'

printInit :: Init -> Int -> Map.Map Span [Ir] -> Bool -> [(Span, String)] -> String
printInit (InitEmpty _) _ _ _ _ = ""
printInit (InitSome _ initHow exp') indent irMap html comments = printInitHow initHow  ++ printExp exp' indent irMap html comments

printInitHow :: InitHow -> String
printInitHow (InitConstant _) = " = "
printInitHow (InitDefault _) = " := "

printTransition :: Transition -> Int -> Map.Map Span [Ir] -> Bool -> [(Span, String)] -> String
printTransition (TransitionEmpty _) _ _ _ _ = ""
printTransition (Transition _ (SyncTransArrow _) exp2) indent irMap html comments = (if html then "<span class=\"tKeyword\"> --&gt;&gt; </span>" else " -->> ") ++ printExp exp2 indent irMap html comments
printTransition (Transition _ (NextTransArrow _) exp2) indent irMap html comments = (if html then "<span class=\"tKeyword\"> --&gt; </span>" else " --> ") ++ printExp exp2 indent irMap html comments
printTransition (Transition _ (GuardedSyncTransArrow _ (TransGuard _ guardExp)) exp2) indent irMap html comments = while html "<span class=\"tKeyword\">" ++ " -[" ++ while html "</span>" ++ printExpIn 1 guardExp indent irMap html comments ++ (if html then "<span class=\"tKeyword\">]--&gt;&gt; </span>" else "]->> ")  ++ printExp exp2 indent irMap html comments
printTransition (Transition _ (GuardedNextTransArrow _ (TransGuard _ guardExp)) exp2) indent irMap html comments = while html "<span class=\"tKeyword\">" ++ " -[" ++ while html "</span>" ++ printExpIn 1 guardExp indent irMap html comments ++ (if html then "<span class=\"tKeyword\">]--&gt; </span>" else "]-> ") ++ printExp exp2 indent irMap html comments

-- | The grammar level of the production that builds an expression node: the
-- @N@ of the @ExpN@ nonterminal in @ParClafer.y@ whose production the
-- constructor carries (@Exp@ itself is level 0; the atoms are the @Exp27@
-- level, which also holds the parenthesized production @'(' Exp ')'@ that
-- builds no node).  A node of level @m@ may stand unparenthesized wherever the
-- grammar admits level @n <= m@, because each @ExpN@ passes through to
-- @ExpN+1@; anywhere else it needs the parentheses the parser consumed.
-- Levels 12 to 14 are pass-through only and build nothing.
-- (Sigil-Logic/clafer#36)
expLevel :: Exp -> Int
expLevel e = case e of
  TransitionExp{}           -> 0   -- Exp   : Exp1 TransArrow Exp
  EDeclAllDisj{}            -> 1   -- Exp1  : 'all' 'disj' Decl '|' Exp1
  EDeclAll{}                -> 1   --       | 'all' Decl '|' Exp1
  EDeclQuantDisj{}          -> 1   --       | Quant 'disj' Decl '|' Exp1
  EDeclQuant{}              -> 1   --       | Quant Decl '|' Exp1
  EImpliesElse{}            -> 1   --       | 'if' Exp1 'then' Exp1 'else' Exp1
  LetExp{}                  -> 1   --       | 'let' VarBinding 'in' Exp1
  TmpPatNever{}             -> 2   -- Exp2  : 'never' Exp3 PatternScope
  TmpPatSometime{}          -> 2   --       | 'sometime' Exp3 PatternScope
  TmpPatLessOrOnce{}        -> 2   --       | 'lonce' Exp3 PatternScope
  TmpPatAlways{}            -> 2   --       | 'always' Exp3 PatternScope
  TmpPatPrecede{}           -> 2   --       | Exp3 'must' 'precede' Exp3 PatternScope
  TmpPatFollow{}            -> 2   --       | Exp3 'must' 'follow' Exp3 PatternScope
  TmpInitially{}            -> 2   --       | 'initially' Exp3
  TmpFinally{}              -> 2   --       | 'finally' Exp3
  EIff{}                    -> 3   -- Exp3  : Exp3 '<=>' Exp4
  EImplies{}                -> 4   -- Exp4  : Exp4 '=>' Exp5
  EOr{}                     -> 5   -- Exp5  : Exp5 '||' Exp6
  EXor{}                    -> 6   -- Exp6  : Exp6 'xor' Exp7
  EAnd{}                    -> 7   -- Exp7  : Exp7 '&&' Exp8
  LtlU{}                    -> 8   -- Exp8  : Exp8 'U' Exp9
  TmpUntil{}                -> 8   --       | Exp8 'until' Exp9
  LtlW{}                    -> 9   -- Exp9  : Exp9 'W' Exp10
  TmpWUntil{}               -> 9   --       | Exp9 'weakuntil' Exp10
  LtlF{}                    -> 10  -- Exp10 : 'F' Exp10
  TmpEventually{}           -> 10  --       | 'eventually' Exp10
  LtlG{}                    -> 10  --       | 'G' Exp10
  TmpGlobally{}             -> 10  --       | 'globally' Exp10
  LtlX{}                    -> 10  --       | 'X' Exp10
  TmpNext{}                 -> 10  --       | 'next' Exp10
  ENeg{}                    -> 11  -- Exp11 : '!' Exp11
  ELt{}                     -> 15  -- Exp15 : Exp15 '<' Exp16
  EGt{}                     -> 15  --       | Exp15 '>' Exp16
  EEq{}                     -> 15  --       | Exp15 '=' Exp16
  ELte{}                    -> 15  --       | Exp15 '<=' Exp16
  EGte{}                    -> 15  --       | Exp15 '>=' Exp16
  ENeq{}                    -> 15  --       | Exp15 '!=' Exp16
  EIn{}                     -> 15  --       | Exp15 'in' Exp16
  ENin{}                    -> 15  --       | Exp15 'not' 'in' Exp16
  EQuantExp{}               -> 16  -- Exp16 : Quant Exp20
  EAdd{}                    -> 17  -- Exp17 : Exp17 '+' Exp18
  ESub{}                    -> 17  --       | Exp17 '-' Exp18
  EMul{}                    -> 18  -- Exp18 : Exp18 '*' Exp19
  EDiv{}                    -> 18  --       | Exp18 '/' Exp19
  ERem{}                    -> 18  --       | Exp18 '%' Exp19
  EGMax{}                   -> 19  -- Exp19 : 'max' Exp20
  EGMin{}                   -> 19  --       | 'min' Exp20
  ESum{}                    -> 20  -- Exp20 : 'sum' Exp21
  EProd{}                   -> 20  --       | 'product' Exp21
  ECard{}                   -> 20  --       | '#' Exp21
  EMinExp{}                 -> 20  --       | '-' Exp21
  EDomain{}                 -> 21  -- Exp21 : Exp21 '<:' Exp22
  ERange{}                  -> 22  -- Exp22 : Exp22 ':>' Exp23
  EUnion{}                  -> 23  -- Exp23 : Exp23 '++' Exp24
  EUnionCom{}               -> 23  --       | Exp23 ',' Exp24
  EDifference{}             -> 24  -- Exp24 : Exp24 '--' Exp25
  EIntersection{}           -> 25  -- Exp25 : Exp25 '**' Exp26
  EIntersectionDeprecated{} -> 26  -- Exp26 : Exp26 '&' Exp27
  EJoin{}                   -> 26  --       | Exp26 '.' Exp27
  ClaferId{}                -> 27  -- Exp27 : Name | PosInteger | PosDouble | PosReal | PosString | '(' Exp ')'
  EInt{}                    -> 27
  EDouble{}                 -> 27
  EReal{}                   -> 27
  EStr{}                    -> 27

-- | Print an expression at a position where the grammar admits level
-- @required@ and above, restoring the parentheses the parser consumed when
-- the expression's own level is lower ('expLevel').  Every sub-expression of
-- 'printExp' is printed this way with the level its production admits, and
-- so is every expression a restricted context holds: a reference target is an
-- @Exp23@, a super type an @Exp26@, a quantifier declaration's set an
-- @Exp21@, a transition guard an @Exp1@, and a pattern scope's bounds are
-- @Exp11@s.  Constraints, assertions, goals, initializers, and transition
-- targets admit any @Exp@ and call 'printExp' directly.
-- (Sigil-Logic/clafer#36)
printExpIn :: Int -> Exp -> Int -> Map.Map Span [Ir] -> Bool -> [(Span, String)] -> String
printExpIn required exp' indent irMap html comments
  | expLevel exp' < required = "(" ++ printed ++ ")"
  | otherwise                = printed
  where
    printed = printExp exp' indent irMap html comments

-- | Print an expression as the source text it was parsed from.  The parser
-- keeps no node for the parentheses it consumes, so each sub-expression is
-- printed through 'printExpIn' with the level its position in the production
-- admits, which parenthesizes it exactly when its own level is lower: for a
-- left-associative operator at level @N@ (@ExpN : ExpN op ExpN+1@) a
-- same-level left operand prints bare and a same-level right operand prints
-- in parentheses.  The operator spellings and spacing are unchanged from the
-- pre-#36 printer, so an expression that needed no parentheses prints as it
-- did before.  (Sigil-Logic/clafer#36)
printExp :: Exp -> Int -> Map.Map Span [Ir] -> Bool -> [(Span, String)] -> String
printExp e indent irMap html comments = case e of
  TransitionExp _ exp1 (SyncTransArrow _) exp2 -> sub 1 exp1 ++ (if html then "<span class=\"tKeyword\"> --&gt;&gt; </span>" else " -->> ") ++ sub 0 exp2
  TransitionExp _ exp1 (NextTransArrow _) exp2 -> sub 1 exp1 ++ (if html then "<span class=\"tKeyword\"> --&gt; </span>" else " --> ") ++ sub 0 exp2
  TransitionExp _ exp1 (GuardedSyncTransArrow _ (TransGuard _ guardExp)) exp2 -> sub 1 exp1 ++ while html "<span class=\"tKeyword\">" ++ " -[" ++ while html "</span>" ++ sub 1 guardExp ++ (if html then "<span class=\"tKeyword\">]--&gt;&gt; </span>" else "]->> ")  ++ sub 0 exp2
  TransitionExp _ exp1 (GuardedNextTransArrow _ (TransGuard _ guardExp)) exp2 -> sub 1 exp1 ++ while html "<span class=\"tKeyword\">" ++ " -[" ++ while html "</span>" ++ sub 1 guardExp ++ (if html then "<span class=\"tKeyword\">]--&gt; </span>" else "]-> ") ++ sub 0 exp2
  EDeclAllDisj _ decl exp' -> "all disj " ++ printDecl decl indent irMap html comments ++ " | " ++ sub 1 exp'
  EDeclAll _     decl exp' -> "all " ++ printDecl decl indent irMap html comments ++ " | " ++ sub 1 exp'
  EDeclQuantDisj _ quant' decl exp' -> printQuant quant' html ++ "disj" ++ printDecl decl indent irMap html comments ++ " | " ++ sub 1 exp'
  EDeclQuant _     quant' decl exp' -> printQuant quant' html ++ printDecl decl indent irMap html comments ++ " | " ++ sub 1 exp'
  LetExp _ varBinding exp' -> while html "<span class=\"keyword\">" ++ "let " ++ while html "</span>" ++ printVarBinding varBinding indent irMap html comments ++ while html "<span class=\"keyword\">" ++ " in " ++ while html "</span>" ++ sub 1 exp'
  TmpPatNever _ exp' patternScope        -> while html "<span class=\"tKeyword\">" ++ "never " ++ while html "</span>" ++ sub 3 exp' ++ printPatternScope patternScope indent irMap html comments
  TmpPatSometime _ exp' patternScope     -> while html "<span class=\"tKeyword\">" ++ "sometime " ++ while html "</span>" ++ sub 3 exp' ++ printPatternScope patternScope indent irMap html comments
  TmpPatLessOrOnce _ exp' patternScope   -> while html "<span class=\"tKeyword\">" ++ "lonce " ++ while html "</span>" ++ sub 3 exp' ++ printPatternScope patternScope indent irMap html comments
  TmpPatAlways _ exp' patternScope       -> while html "<span class=\"tKeyword\">" ++ "always " ++ while html "</span>" ++ sub 3 exp' ++ printPatternScope patternScope indent irMap html comments
  TmpPatPrecede _ exp1 exp2 patternScope -> sub 3 exp1 ++ while html "<span class=\"tKeyword\">" ++ " must precede " ++ while html "</span>" ++ sub 3 exp2 ++ printPatternScope patternScope indent irMap html comments
  TmpPatFollow _ exp1 exp2 patternScope  -> sub 3 exp1 ++ while html "<span class=\"tKeyword\">" ++ " must follow " ++ while html "</span>" ++ sub 3 exp2 ++ printPatternScope patternScope indent irMap html comments
  TmpInitially _ exp'    -> while html "<span class=\"tKeyword\">" ++ "initially " ++ while html "</span>" ++ sub 3 exp'
  TmpFinally _ exp'      -> while html "<span class=\"tKeyword\">" ++ "finally " ++ while html "</span>" ++ sub 3 exp'
  EGMax _ exp'           -> "max " ++ sub 20 exp'
  EGMin _ exp'           -> "min " ++ sub 20 exp'
  ENeq _ exp1 exp2       -> sub 15 exp1 ++ " != " ++ sub 16 exp2
  EQuantExp _ quant' exp' -> printQuant quant' html ++ sub 20 exp'
  EIff _ exp1 exp2       -> sub 3 exp1 ++ (if html then " &lt;=&gt; " else " <=> ") ++ sub 4 exp2
  EImplies _ exp1 exp2   -> sub 4 exp1 ++ (if html then " =&gt; " else " => ") ++ sub 5 exp2
  EAnd _ exp1 exp2       -> sub 7 exp1 ++ (if html then " &amp;&amp; " else " && ")  ++ sub 8 exp2
  EOr _ exp1 exp2        -> sub 5 exp1 ++ (if html then " &#124;&#124; " else " || ") ++ sub 6 exp2
  EXor _ exp1 exp2       -> sub 6 exp1 ++ " xor " ++ sub 7 exp2
  LtlU _ exp1 exp2       -> sub 8 exp1 ++ " U " ++ sub 9 exp2
  TmpUntil _ exp1 exp2   -> sub 8 exp1 ++ while html "<span class=\"tKeyword\">" ++ " until " ++ while html "</span>" ++ sub 9 exp2
  LtlW _ exp1 exp2       -> sub 9 exp1 ++ " W " ++ sub 10 exp2
  TmpWUntil _ exp1 exp2  -> sub 9 exp1 ++ while html "<span class=\"tKeyword\">" ++ " weakuntil " ++ while html "</span>" ++ sub 10 exp2
  LtlF _ exp'            -> "F " ++ sub 10 exp'
  TmpEventually _ exp'   -> while html "<span class=\"tKeyword\">" ++ "eventually " ++ while html "</span>" ++ sub 10 exp'
  LtlG _ exp'            -> "G " ++ sub 10 exp'
  TmpGlobally _ exp'     -> while html "<span class=\"tKeyword\">" ++ "globally " ++ while html "</span>" ++ sub 10 exp'
  LtlX _ exp'            -> "F " ++ sub 10 exp'
  TmpNext _ exp'         -> while html "<span class=\"tKeyword\">" ++ "next " ++ while html "</span>" ++ sub 10 exp'
  ENeg _ exp'            -> " ! " ++ sub 11 exp'
  ELt _ exp1 exp2        -> sub 15 exp1 ++ (if html then " &lt; " else " < ") ++ sub 16 exp2
  EGt _ exp1 exp2        -> sub 15 exp1 ++ (if html then " &gt; " else " > ") ++ sub 16 exp2
  EEq _ exp1 exp2        -> sub 15 exp1 ++ " = " ++ sub 16 exp2
  ELte _ exp1 exp2       -> sub 15 exp1 ++ (if html then " &lt;= " else " <= ") ++ sub 16 exp2
  EGte _ exp1 exp2       -> sub 15 exp1 ++ (if html then " &gt;= " else " >= ") ++ sub 16 exp2
  EIn _ exp1 exp2        -> sub 15 exp1 ++ " in " ++ sub 16 exp2
  ENin _ exp1 exp2       -> sub 15 exp1 ++ " not in " ++ sub 16 exp2
  EAdd _ exp1 exp2       -> sub 17 exp1 ++ " + " ++ sub 18 exp2
  ESub _ exp1 exp2       -> sub 17 exp1 ++ " - " ++ sub 18 exp2
  EMul _ exp1 exp2       -> sub 18 exp1 ++ " * " ++ sub 19 exp2
  EDiv _ exp1 exp2       -> sub 18 exp1 ++ (if html then " &#47; " else " / ") ++ sub 19 exp2
  ERem _ exp1 exp2       -> sub 18 exp1 ++ (if html then " &#37; " else " % ") ++ sub 19 exp2
  ESum _ exp'            -> while html "<span class=\"keyword\">" ++ "sum " ++ while html "</span>" ++ sub 21 exp'
  EProd _ exp'           -> while html "<span class=\"keyword\">" ++ "product " ++ while html "</span>" ++ sub 21 exp'
  ECard _ exp'           -> "# " ++ sub 21 exp'
  EMinExp _ exp'         -> "-" ++ sub 21 exp'
  EImpliesElse _ exp1 exp2 exp'3
    -> while html "<span class=\"keyword\">" ++ "if " ++ while html "</span>"
    ++ sub 1 exp1
    ++ while html "<span class=\"keyword\">" ++ " then " ++ while html "</span>"
    ++ sub 1 exp2
    ++ while html "<span class=\"keyword\">" ++ " else " ++ while html "</span>"
    ++ sub 1 exp'3
  ClaferId _ name                    -> printName name indent irMap html comments
  EUnion _ set1 set2                 -> sub 23 set1 ++ "++" ++ sub 24 set2
  EUnionCom _ set1 set2              -> sub 23 set1 ++ ", " ++ sub 24 set2
  EDifference _ set1 set2            -> sub 24 set1 ++ "--" ++ sub 25 set2
  EIntersection _ set1 set2          -> sub 25 set1 ++ "**" ++ sub 26 set2
  EIntersectionDeprecated _ set1 set2 -> sub 26 set1 ++ printDeprecated "&amp;" "Use `**` instead." html ++ sub 27 set2
  EDomain _ set1 set2                -> sub 21 set1 ++ "<:" ++ sub 22 set2
  ERange _ set1 set2                 -> sub 22 set1 ++ ":>" ++ sub 23 set2
  EJoin _ set1 set2                  -> sub 26 set1 ++ "." ++ sub 27 set2
  EInt _ (PosInteger (_, num))       -> num
  EDouble _ (PosDouble (_, num))     -> num
  EReal _ (PosReal (_, num))         -> num
  EStr _ (PosString (_, str))        -> str
  where
    -- the sub-expression at a position admitting level @required@ and above
    sub required exp' = printExpIn required exp' indent irMap html comments

printPatternScope :: PatternScope -> Int -> Map.Map Span [Ir] -> Bool -> [(Span, String)] -> String
printPatternScope (PatScopeBefore _ exp')          indent irMap html comments = while html "<span class=\"tKeyword\">" ++ " before " ++ while html "</span>" ++ printExpIn 11 exp' indent irMap html comments
printPatternScope (PatScopeAfter _ exp')           indent irMap html comments = while html "<span class=\"tKeyword\">" ++ " after " ++ while html "</span>" ++ printExpIn 11 exp' indent irMap html comments
printPatternScope (PatScopeBetweenAnd _ exp1 exp2) indent irMap html comments = while html "<span class=\"tKeyword\">" ++ " between " ++ while html "</span>" ++ printExpIn 11 exp1 indent irMap html comments ++ while html "<span class=\"tKeyword\">" ++ " and " ++ while html "</span>" ++ printExpIn 11 exp2 indent irMap html comments
printPatternScope (PatScopeAfterUntil _ exp1 exp2) indent irMap html comments = while html "<span class=\"tKeyword\">" ++ " after " ++ while html "</span>" ++ printExpIn 11 exp1 indent irMap html comments ++ while html "<span class=\"tKeyword\">" ++ " until " ++ while html "</span>" ++ printExpIn 11 exp2 indent irMap html comments
printPatternScope _                           _      _     _    _        = ""

printQuant :: Quant -> Bool -> String
printQuant quant' html = case quant' of
  (QuantNo _)   -> while html "<span class=\"keyword\">" ++ "no" ++ while html "</span>" ++ " "
  (QuantNot _)  -> while html "<span class=\"keyword\">" ++ "not" ++ while html "</span>" ++ " "
  (QuantLone _) -> while html "<span class=\"keyword\">" ++ "lone" ++ while html "</span>" ++ " "
  (QuantOne _)  -> while html "<span class=\"keyword\">" ++ "one" ++ while html "</span>" ++ " "
  (QuantSome _) -> while html "<span class=\"keyword\">" ++ "some" ++ while html "</span>" ++ " "

printEnumId :: EnumId -> Int -> Map.Map Span [Ir] -> Bool -> [(Span, String)] -> String
printEnumId (EnumIdIdent _ posident) _ irMap html _ = printPosIdent posident mUid' html
  where
    mUid' = getUid posident irMap

printIndent :: Int -> Bool -> String
printIndent 0 html = while html "<div>" ++ "\n"
printIndent _ html = while html "<div class=\"indent\">" ++ "\n"

printIndentId :: Int -> Bool -> String
printIndentId 0 html = while html "<div>" ++ "\n"
printIndentId _ html = while html "<div class=\"indent\">" ++ "\n"

printIndentEnd :: Bool -> String
printIndentEnd html = while html "</div>" ++ "\n"

dropUid :: String -> String
dropUid uid' = let id' = rest $ dropWhile (/= '_') uid'
              in if id' == ""
                then uid'
                else id'

--so it fails more gracefully on empty lists
{-first :: String -> String
first [] = []
first (x:_) = x-}
rest :: String -> String
rest [] = []
rest (_:xs) = xs

getUid :: PosIdent -> Map.Map Span [Ir] -> Maybe String
getUid posIdent@(PosIdent (_, id')) irMap =
  case Map.lookup (getSpan posIdent) irMap of
    Nothing -> Nothing
    Just wrappedResultList -> listToMaybe $ mapMaybe (findUid id' . unwrap) wrappedResultList
  where
    unwrap (IRPExp pexp')       = getIdentPExp pexp'
    unwrap (IRClafer iClafer') = [ _uid iClafer' ]
    unwrap x = error $ "Html:getUid:unwrap called on: " ++ show x
    getIdentPExp (PExp _ _ _ exp') = getIdentIExp exp'
    getIdentIExp (IFunExp _ exps') = concatMap getIdentPExp exps'
    getIdentIExp (IClaferId _ id'' _ _) = [id'']
    getIdentIExp (IDeclPExp _ _ pexp) = getIdentPExp pexp
    getIdentIExp _ = []
    findUid name (x:xs) = if name == dropUid x then Just x else findUid name xs
    findUid _    []     = Nothing

getDivId :: Span -> Map.Map Span [Ir] -> String
getDivId s irMap = if isNothing $ Map.lookup s irMap
                      then "Uid not Found"
                      else let IRClafer iClaf = head $ fromJust $ Map.lookup s irMap in
                        _uid iClaf

getUseId :: Span -> Map.Map Span [Ir] -> (String, String)
getUseId s irMap = if isNothing $ Map.lookup s irMap
                      then ("Uid not Found", "Uid not Found")
                      else let IRClafer iClaf = head $ fromJust $ Map.lookup s irMap in
                        (_uid iClaf, fromMaybe "" $ _sident . _exp <$> _super iClaf)

while :: Bool -> String -> String
while bool exp' = if bool then exp' else ""

cleanOutput :: String -> String
cleanOutput "" = ""
cleanOutput (' ':'\n':xs) = cleanOutput $ '\n':xs
cleanOutput ('\n':'\n':xs) = cleanOutput $ '\n':xs
cleanOutput (' ':'<':'b':'r':'>':xs) = "<br>"++cleanOutput xs
cleanOutput (x:xs) = x : cleanOutput xs

trim :: String -> String
trim = let f = reverse . dropWhile isSpace in f . f

highlightErrors :: String -> [ClaferErr] -> String
highlightErrors model errors = "<pre>\n" ++ unlines (replace "<!-- # FRAGMENT /-->" "</pre>\n<!-- # FRAGMENT /-->\n<pre>" --assumes the fragments have been concatenated
                            (highlightErrors' (replace "//# FRAGMENT" "<!-- # FRAGMENT /-->" (lines model)) errors)) ++ "</pre>"
  where
    replace _ _ []     = []
    replace x y (z:zs) = (if x == z then y else z):replace x y zs

highlightErrors' :: [String] -> [ClaferErr] -> [String]
highlightErrors' model' [] = model'
highlightErrors' model' (ClaferErr _:es) = highlightErrors' model' es
highlightErrors' model' (ParseErr ErrPos{modelPos = Pos l c, fragId = n} msg':es) =
  let (ls, lss) = genericSplitAt (l + toInteger n) model'
      newLine = fst (genericSplitAt (c - 1) $ last ls) ++ "<span class=\"error\" title=\"Parsing failed at line " ++ show l ++ " column " ++ show c ++
           "...\n" ++ msg' ++ "\">" ++ (if snd (genericSplitAt (c - 1) $ last ls) == "" then "&nbsp;" else snd (genericSplitAt (c - 1) $ last ls)) ++ "</span>"
  in highlightErrors' (init ls ++ [newLine] ++ lss) es
highlightErrors' model' (SemanticErr ErrPos{modelPos = Pos l c, fragId = n} msg':es) =
  let (ls, lss) = genericSplitAt (l + toInteger n) model'
      newLine = fst (genericSplitAt (c - 1) $ last ls) ++ "<span class=\"error\" title=\"Compiling failed at line " ++ show l ++ " column " ++ show c ++
           "...\n" ++ msg' ++ "\">" ++ (if snd (genericSplitAt (c - 1) $ last ls) == "" then "&nbsp;" else snd (genericSplitAt (c - 1) $ last ls)) ++ "</span>"
  in highlightErrors' (init ls ++ [newLine] ++ lss) es
