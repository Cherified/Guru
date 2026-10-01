{-
 - Copyright (c) 2025-2026 Cherified Systems LLC
 -
 - SPDX-License-Identifier: MIT
 -}

module Rtl where

import Compile
import ModPrinter

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
  case compiledMod of
    Just cm -> putStr $ unlines $ Prelude.map breakLine $ lines $
               "`include \"GuruLibrary.sv\"\n" ++ ppTop cm
    Nothing -> putStrLn "ERROR!"
