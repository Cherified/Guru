module Main where

import Compile
import ModPrinter
import TopPrinter

main :: IO ()
main = do
  case compiledMod of
    Just cm -> putStrLn $ "`include \"GuruLibrary\"\n"
               ++ ppMod cm
               ++ ppTop cm
               ++ ppTb cm
    Nothing -> putStrLn "ERROR!"
