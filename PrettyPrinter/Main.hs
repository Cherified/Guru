module Main where

import Compile
import ModPrinter
import TopPrinter

main :: IO ()
main = do
  case compiledMod of
    Just cm -> putStrLn $ "`include \"GuruLibrary.sv\"\n"
               ++ ppMod cm
               ++ ppTop cm
               ++ ppTb cm
    Nothing -> putStrLn "ERROR!"
