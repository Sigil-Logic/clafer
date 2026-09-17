{-
 Copyright (C) 2014-2017 Michal Antkiewicz <http://gsd.uwaterloo.ca>

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
-- | Support for dealing with unique IDs (UIDs), fully- and least-partially qualified names.
module Language.Clafer.QNameUID (
        QName,
        FQName,
        PQName,
        QNameMaps,
        UID,
        deriveQNameMaps,
        getUIDs,
        getFQName,
        getLPQName,
        getQNameUIDTriples
)

where

import Data.List (isInfixOf, isPrefixOf)
import Data.Maybe
import Data.List.Split
import qualified Data.Map as Map

import Language.Clafer.Intermediate.Intclafer

-- | a fully- or partially-qualified name
type QName = String

-- | fully-qualified name, must begin with ::
-- | e.g., `::Person::name`, `::Company::Department::chair`
type FQName = String

-- a reversed FQName used as a key in the FQNameUIDMap
type FQKey = String

-- | partially-qualified name, must not begin with ::
-- | e.g., `Person::name`, `chair`
type PQName = String

-- a map from reversed FQName (FQKey) to UID
-- an ordered map: reversing the names on "::" makes every qualified-name
-- prefix query a contiguous key range, so prefix search needs no prefix tree
type FQNameUIDMap = Map.Map FQKey UID

type UIDFqNameMap = Map.Map UID FQName
type UIDLpqNameMap = Map.Map UID PQName

-- | maps between fully-, least-partially-qualified names and UIDs
data QNameMaps =  QNameMaps FQNameUIDMap UIDFqNameMap UIDLpqNameMap

-- | get the UID of a clafer given a fully qualifed name or potentially many UIDs given a partially qualified name
getUIDs :: QNameMaps                 -> QName -> [UID]
getUIDs    (QNameMaps fqNameUIDMap _ _) qName = findUIDsByFQName fqNameUIDMap qName

-- | get the fully-qualified name of a clafer given its UID
getFQName :: QNameMaps                 -> UID -> Maybe FQName
getFQName    (QNameMaps _ uidFqNameMap _) uid' = Map.lookup uid' uidFqNameMap

-- | get the least-partially-qualified name of a clafer given its UID
getLPQName :: QNameMaps                 -> UID -> Maybe PQName
getLPQName    (QNameMaps _ _ uidLpqNameMap) uid' = Map.lookup uid' uidLpqNameMap

-- | derive maps between fully-, partially-qualified names, and UIDs
deriveQNameMaps :: IModule -> QNameMaps
deriveQNameMaps    iModule =
    let
        (fqNameUIDMap, uidFqNameMap) = deriveFQNameUIDMaps iModule
        uidLpqNameMap = deriveUidLpqNameMap fqNameUIDMap
    in
        QNameMaps fqNameUIDMap uidFqNameMap uidLpqNameMap

deriveFQNameUIDMaps :: IModule -> (FQNameUIDMap, UIDFqNameMap)
deriveFQNameUIDMaps    iModule = addElements ["::"] (_mDecls iModule) (Map.empty, Map.empty)

addElements :: [String] -> [IElement] -> (FQNameUIDMap, UIDFqNameMap) -> (FQNameUIDMap, UIDFqNameMap)
addElements    path        elems         maps                         = foldl (addClafer path) maps elems

addClafer :: [String] -> (FQNameUIDMap, UIDFqNameMap) -> IElement          -> (FQNameUIDMap, UIDFqNameMap)
addClafer    path        (fqNameUIDMap, uidFqNameMap)    (IEClafer iClaf) =
    let
        newPath = _ident iClaf : path
        fqKey :: FQKey
        fqKey = concat newPath
        fqName :: FQName
        fqName = getQNameFromKey fqKey
        fqNameUIDMap' = Map.insert fqKey (_uid iClaf) fqNameUIDMap
        uidFqNameMap' = Map.insert (_uid iClaf) fqName uidFqNameMap
    in
        addElements ("::" : newPath) (_elements iClaf) (fqNameUIDMap', uidFqNameMap')
addClafer    _           maps                            _                  = maps

findUIDsByFQName :: FQNameUIDMap -> FQName            -> [ UID ]
findUIDsByFQName    fqNameUIDMap    fqName@(':':':':_) = maybeToList $ Map.lookup (getFQKey fqName) fqNameUIDMap
findUIDsByFQName    fqNameUIDMap    fqName             = prefixFind (getFQKey fqName) fqNameUIDMap

-- all values whose key begins with the given prefix, in ascending key order
-- (replaces Data.StringMap.prefixFind: keys sharing a prefix form a
--  contiguous range in an ordered map, carved out by two antitone splits).
-- The match is character-wise, not segment-wise: the prefix `A` also matches
-- the key `AB::`, so a plain name that prefixes another clafer's name is
-- judged ambiguous and over-qualified (`A` beside `AB` derives `::A`).
-- Sigil-Logic/clafer#38 tracks the segment-boundary fix; Sigil-Logic/clafer#34
-- left it unchanged so every multi-clafer .cfr-map stays byte-identical.
prefixFind :: FQKey -> FQNameUIDMap -> [UID]
prefixFind    prefix   fqNameUIDMap =
    Map.elems $ Map.takeWhileAntitone (prefix `isPrefixOf`) $ Map.dropWhileAntitone (< prefix) fqNameUIDMap

reverseOnQualifier :: FQName -> FQName
reverseOnQualifier fqName = concat $ reverse $ split (onSublist "::") fqName

getFQKey :: FQName -> FQKey
getFQKey = reverseOnQualifier

getQNameFromKey :: FQKey -> QName
getQNameFromKey = reverseOnQualifier

deriveUidLpqNameMap :: FQNameUIDMap ->  UIDLpqNameMap
deriveUidLpqNameMap    fqNameUIDMap =
    Map.foldrWithKey (generateUIDLpqMapEntry fqNameUIDMap) Map.empty fqNameUIDMap

generateUIDLpqMapEntry :: FQNameUIDMap ->  FQKey -> UID -> UIDLpqNameMap -> UIDLpqNameMap
generateUIDLpqMapEntry    fqNameUIDMap     fqKey       uid'   uidLpqNameMap =
    Map.insert uid' lpqName uidLpqNameMap
    where
      -- need to reverse the key to get a fully qualified name
      fqName :: FQName
      fqName = getQNameFromKey fqKey

      -- name qualified just sufficiently to uniquely identify the clafer
      -- can be both FQName or PQName
      lpqName :: QName
      lpqName = findLeastQualifiedName fqName fqNameUIDMap

      findLeastQualifiedName :: String -> FQNameUIDMap -> String
      -- handle fully qualified name case
      findLeastQualifiedName fqName'@(':':':':pqName) fqNameUIDMap' =
          if (length (findUIDsByFQName fqNameUIDMap' pqName) > 1)
              then fqName'
              else findLeastQualifiedName pqName fqNameUIDMap'
      -- handle partially qualified name case
      findLeastQualifiedName pqName fqNameUIDMap'
         -- a plain name has no qualification left to remove: it is the
         -- least-qualified form, and the caller has already established
         -- that it identifies the clafer uniquely.  Without this base case
         -- the step below strips the plain name to the empty name, whose
         -- prefix search returns every clafer in the module; a module with
         -- a single clafer never returns more than one, so the recursion
         -- looped on the empty name forever and `--meta-data` hung on any
         -- single-top-level-clafer model (Sigil-Logic/clafer#34).  Modules
         -- with two or more clafers stopped here by accident, because the
         -- empty prefix matched them all.
         | not ("::" `isInfixOf` pqName) = pqName
         | otherwise =
         let
            -- remove one segment of qualification
            lessQName =  concat $ drop 2 $ split (onSublist "::") pqName
         in
            if (length (findUIDsByFQName fqNameUIDMap' lessQName) > 1)
              then pqName
              else findLeastQualifiedName lessQName fqNameUIDMap'

getQNameUIDTriples :: QNameMaps -> [(FQName, PQName, UID)]
getQNameUIDTriples qNameMaps@(QNameMaps _ uidFqNameMap _) =
    let
      uidFqNameList :: [(UID, FQName)]
      uidFqNameList = Map.toList uidFqNameMap
    in
      map (\(uid', fqName) -> (fqName, fromMaybe fqName $ getLPQName qNameMaps uid', uid')) uidFqNameList
