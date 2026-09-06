{-
 - Copyright (c) 2025-2026 Cherified Systems LLC
 -
 - SPDX-License-Identifier: MIT
 -}

module Rtl where

import Compile
import ModPrinter

main :: IO ()
main = do
  case compiledMod of
    Just cm -> putStrLn $ "`include \"GuruLibrary.sv\"\n"
               ++ ppTop cm
    Nothing -> putStrLn "ERROR!"
