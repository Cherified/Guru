{-
 - Copyright (c) 2025-2026 Cherified Systems LLC
 -
 - SPDX-License-Identifier: MIT
 -}

module Rtl where

import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.IO (hPutStrLn, stderr)
import Data.Char (isAlphaNum)
import Data.List (nub)
import Compile
import ModPrinter

isValidNameChar :: Char -> Bool
isValidNameChar c = isAlphaNum c || c == '_'

isValidName :: String -> Bool
isValidName = all isValidNameChar

kindNames :: Kind -> [String]
kindNames Bool = []
kindNames (Bit _) = []
kindNames (Struct ls) = concatMap (\(s, k) -> s : kindNames k) ls
kindNames (TaggedUnion ls) = concatMap (\(s, k) -> s : kindNames k) ls
kindNames (Array _ k) = kindNames k

elemKindNames :: Elem -> [String]
elemKindNames (EReg r) = kindNames (regKind r)
elemKindNames (EMem m) = kindNames (memKind m)
elemKindNames (ESend k) = kindNames k
elemKindNames (ERecv k) = kindNames k
elemKindNames (EGallinaReg _) = []

treeNames :: Tree Elem -> [String]
treeNames (Leaf name e) = name : elemKindNames e
treeNames (Node name children) = name : concatMap treeNames children

findInvalidNames :: CompiledModule -> [String]
findInvalidNames (((_, tree), tmps), _) =
  let codeNames = concatMap (\(s, k) -> s : kindNames k) tmps
      allNames = treeNames tree ++ codeNames
  in nub (Prelude.filter (not . isValidName) allNames)

breakLine :: String -> String
breakLine line =
  let indent    = takeWhile (== ' ') line ++ "  "
      indentLen = Prelude.length indent
      go _   [] = []
      go col (' ':cs)
        | col >= 200 = '\n' : indent ++ go indentLen cs
      go col (c:cs)  = c    : go (col + 1) cs
  in go 0 line

main :: IO ()
main = do
  args <- getArgs
  let isSim = case args of
                ("s":_) -> True
                _       -> False
      cm@(((valid, tree), _), _) = compiledMod
      dups = findDuplicateElems tree
      invalids = findInvalidNames cm
  if not (Prelude.null dups && Prelude.null invalids)
    then do
      mapM_ (\d -> hPutStrLn stderr ("ERROR! Duplicate element name: " ++ d)) dups
      mapM_ (\s -> hPutStrLn stderr ("ERROR! Invalid name: " ++ s)) invalids
      exitFailure
    else if not isSim && not valid
      then do
        hPutStrLn stderr "ERROR! RTL being generated but violates write-after-read for memory, or multiple Sends or multiple memory requests in a single cycle, or uses CallGallina"
        exitFailure
      else putStr $ unlines $ Prelude.map breakLine $ lines $
           "`include \"GuruLibrary.sv\"\n" ++ ppTop isSim cm
