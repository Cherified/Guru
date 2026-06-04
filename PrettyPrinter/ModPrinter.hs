module ModPrinter where

import Data.List
import Compile
import CodePrinter
import GHC.Num

ppArrayKind :: Kind -> Kind
ppArrayKind k@(Array _ k') = ppArrayKind k'
ppArrayKind (Bit n') = Bool
ppArrayKind k = k

ppArrayList :: Kind -> [Integer]
ppArrayList k@(Array n' k') = (n': ppArrayList k')
ppArrayList (Bit n') = n' : []
ppArrayList _ = []

ppKindImmStart :: Int -> Kind -> String
ppKindImmStart q Bool = "logic "
ppKindImmStart q (Bit n) = ppKindImmStart q (Array n Bool)
ppKindImmStart q (Struct ls) = "struct packed {\n" ++ concatMap (\(s, k) -> ppIndent (q+1) ++ ppKindImmStart (q+1) k ++ s ++ ";\n") ls ++ ppIndent q ++ "} "
ppKindImmStart q a@(Array n k) = ppKindImmStart q (ppArrayKind a) ++ concatMap (\i -> "[" ++ show (i-1) ++ " : 0]") (ppArrayList a) ++ " "

ppKindDecl :: Int -> Kind -> String
ppKindDecl q k = ppIndent q ++ ppKindImmStart q k

clog2 :: Integer -> Integer
clog2 = ceiling . (logBase 2) . fromIntegral

sizeElem :: ModElem -> Bool
sizeElem (EReg r) = size (regKind r) > 0
sizeElem (EMem m) = size (memKind m) > 0 && memSize m > 0 && memPort m > 0
sizeElem (ESend k) = size k > 0
sizeElem (ERecv k) = size k > 0

dfsModElems :: Tree ModElem -> [([String], ModElem)]
dfsModElems tree = helper [] tree
  where
    helper path (Leaf name elem) = [(name : path, elem)]
    helper path (Node name children) =
      concatMap (helper (name : path)) children

modElems :: Tree ModElem -> [(Integer, (String, ModElem))]
modElems tree = tag (Prelude.map (\(path, elem) -> (intercalate "_" (reverse path), elem)) (filter (sizeElem . Prelude.snd) $ dfsModElems tree))


