module Main where

import Compile
import ModPrinter

main :: IO ()
main = do
  case compiledMod of
    Just cm -> putStrLn $ "`include \"GuruLibrary.sv\"\n"
               ++ ppTop cm
    Nothing -> putStrLn "ERROR!"
