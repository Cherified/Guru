{-
 - Copyright 2026 Google LLC
 -
 - SPDX-License-Identifier: MIT
 -}

-- Prints the CIRCT MLIR of the extracted compiledMod; the counterpart of
-- PrettyPrinter/Rtl.hs. With the argument "s", prints the simulation version (the
-- counterpart of "Rtl s"); otherwise prints the RTL version, which needs a valid module.

module Circt where

import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.IO (hPutStrLn, stderr)
import Compile (compiledMod)
import ModPrinter (findDuplicateElems)
import Rtl (findInvalidNames)
import CirctPrinter (Mode(..), ppCirctTop)

main :: IO ()
main = do
  args <- getArgs
  let isSim = case args of
                ("s" : _) -> True
                _ -> False
      cm@(((valid, tree), _), _) = compiledMod
      dups = findDuplicateElems tree
      invalids = findInvalidNames cm
  if not (null dups && null invalids)
    then do
      mapM_ (\d -> hPutStrLn stderr ("ERROR! Duplicate element name: " ++ d)) dups
      mapM_ (\s -> hPutStrLn stderr ("ERROR! Invalid name: " ++ s)) invalids
      exitFailure
    else if not isSim && not valid
      then do
        hPutStrLn stderr "ERROR! RTL being generated but violates write-after-read for memory, or multiple Sends or multiple memory requests in a single cycle, or uses CallGallina"
        exitFailure
      else putStr (ppCirctTop (if isSim then Sim else Rtl) cm)
