{-# LANGUAGE OverloadedStrings #-}

import qualified Data.Text as T
import qualified Data.Text.IO as T

import Data.Char (isSpace)
import System.Environment (getArgs)

data Tok =
      White T.Text
    | Txt T.Text
    | LParen
    | RParen
    | Zero
    | Succ
    | NatLit Int
    deriving (Show)

toks :: T.Text -> [Tok]
toks txt
    | T.null txt = []
    | otherwise = case T.stripPrefix "(" txt of
        Just rest -> LParen : toks rest
        Nothing -> case T.stripPrefix ")" txt of
            Just rest -> RParen : toks rest
            Nothing -> case T.stripPrefix "0" txt of
                Just rest -> Zero : toks rest
                Nothing -> case T.stripPrefix "Prelude.succ" txt of
                    Just rest -> Succ : toks rest
                    Nothing -> case isSpace $ T.head txt of
                        True -> let (white,rest) = T.span isSpace txt in (White white) : toks rest
                        False -> let (txt',rest) = T.span (\c -> not $ isSpace c && c /= '(' && c /= ')') txt in (Txt txt') : toks rest

drop_rps :: Int -> [Tok] -> [Tok]
drop_rps n ts 
    | n <= 0 = ts
    | otherwise = case ts of
        (White _:us) -> drop_rps n us
        (RParen:us) -> drop_rps (n-1) us
        _ -> ts

parse_nat :: [Tok] -> Maybe (Int, [Tok])
parse_nat ts = go 0 ts where
    go n (Succ:rest) = go (n+1) rest
    go n (Zero:rest) = Just (n, drop_rps (n-1) rest)
    go n ((White _):rest) = go n rest
    go n (LParen:rest) = go n rest
    go _ _ = Nothing

fix_lits :: [Tok] -> [Tok]
fix_lits ts = case ts of
    [] -> []
    (Succ:rest) -> case parse_nat ts of
        Just (n,rest') -> (NatLit n) : fix_lits rest'
        Nothing -> Succ : fix_lits rest
    (t:rest) -> t : fix_lits rest

print_tok :: Tok -> T.Text
print_tok (White w) = w
print_tok (Txt t) = t
print_tok LParen = "("
print_tok RParen = ")"
print_tok Zero = "0"
print_tok Succ = "Prelude.succ"
print_tok (NatLit n) = T.pack $ show n

main :: IO ()
main = do
    (fileIn:_) <- getArgs
    txt <- T.readFile fileIn
    T.writeFile fileIn $ T.concat $ map print_tok $ fix_lits $ toks txt
