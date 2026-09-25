{-
 - Copyright (c) 2025-2026 Cherified Systems LLC
 -
 - SPDX-License-Identifier: MIT
 -}

{-# LANGUAGE OverloadedStrings, BangPatterns #-}

import qualified Data.Text as T
import qualified Data.Text.IO as T

import Data.Char (isSpace)
import Data.List (foldl')
import System.Environment (getArgs)

data Tok =
      White T.Text
    | Txt T.Text
    | LParen
    | RParen
    | Zero
    | One
    | Succ
    | NatLit Int
    | ZPos
    | ZNeg
    | XI
    | XO
    | IntLit Integer
    | Cons
    | Nil
    | IntListLit [Integer]
    deriving (Show)

isDelim :: T.Text -> Bool
isDelim rest = case T.uncons rest of
    Nothing -> True
    Just (c, _) -> isSpace c || c == ')' || c == '('

toks :: T.Text -> [Tok]
toks txt
    | T.null txt = []
    | Just rest <- T.stripPrefix "(:)" txt = Cons : toks rest
    | Just rest <- T.stripPrefix "[]" txt = Nil : toks rest
    | Just rest <- T.stripPrefix "(\\x -> 2 Prelude.* x Prelude.+ 1)" txt = XI : toks rest
    | Just rest <- T.stripPrefix "(\\x -> 2 Prelude.* x)" txt = XO : toks rest
    | Just rest <- T.stripPrefix "(\\x -> Prelude.negate x)" txt = ZNeg : toks rest
    | Just rest <- T.stripPrefix "(\\x -> x)" txt = ZPos : toks rest
    | Just rest <- T.stripPrefix "Prelude.succ" txt, isDelim rest = Succ : toks rest
    | Just rest <- T.stripPrefix "(" txt = LParen : toks rest
    | Just rest <- T.stripPrefix ")" txt = RParen : toks rest
    | Just rest <- T.stripPrefix "0" txt, isDelim rest = Zero : toks rest
    | Just rest <- T.stripPrefix "1" txt, isDelim rest = One : toks rest
    | isSpace (T.head txt) =
        let (white, rest) = T.span isSpace txt
        in White white : toks rest
    | otherwise =
        let (txt', rest) = T.span (\c -> not (isSpace c) && c /= '(' && c /= ')') txt
        in Txt txt' : toks rest

drop_rps :: Int -> [Tok] -> [Tok]
drop_rps !n ts
    | n <= 0 = ts
    | otherwise = case ts of
        (White _:us) -> drop_rps n us
        (RParen:us) -> drop_rps (n-1) us
        _ -> ts

skip_white :: [Tok] -> [Tok]
skip_white (White _:rest) = skip_white rest
skip_white ts = ts

parse_nat :: [Tok] -> Maybe (Int, [Tok])
parse_nat ts = go 0 0 ts where
    go !n !lp (Succ:rest) = go (n+1) lp rest
    go !n !lp (Zero:rest) = Just (n, drop_rps lp rest)
    go !n !lp ((White _):rest) = go n lp rest
    go !n !lp (LParen:rest) = go n (lp+1) rest
    go _ _ _ = Nothing

parse_pos :: [Tok] -> Maybe (Integer, Int, [Tok])
parse_pos ts = go [] 0 ts where
    go ops !lp (XI:rest) = go ((\v -> 2 * v + 1) : ops) lp rest
    go ops !lp (XO:rest) = go ((\v -> 2 * v) : ops) lp rest
    go ops !lp (One:rest) = Just (foldl' (\v f -> f v) 1 ops, lp, rest)
    go ops !lp ((White _):rest) = go ops lp rest
    go ops !lp (LParen:rest) = go ops (lp+1) rest
    go _ _ _ = Nothing

parse_z :: [Tok] -> Maybe (Integer, [Tok])
parse_z (ZPos:rest) = do
    (v, lp, rest') <- parse_pos rest
    return (v, drop_rps lp rest')
parse_z (ZNeg:rest) = do
    (v, lp, rest') <- parse_pos rest
    return (-v, drop_rps lp rest')
parse_z ts@(XI:_) = do
    (v, lp, rest') <- parse_pos ts
    return (v, drop_rps lp rest')
parse_z ts@(XO:_) = do
    (v, lp, rest') <- parse_pos ts
    return (v, drop_rps lp rest')
parse_z _ = Nothing

fix_scalars :: [Tok] -> [Tok]
fix_scalars ts = case ts of
    [] -> []
    (Succ:rest) -> case parse_nat ts of
        Just (n, rest') -> NatLit n : fix_scalars rest'
        Nothing -> Succ : fix_scalars rest
    (ZPos:rest) -> case parse_z ts of
        Just (z, rest') -> IntLit z : fix_scalars rest'
        Nothing -> ZPos : fix_scalars rest
    (ZNeg:rest) -> case parse_z ts of
        Just (z, rest') -> IntLit z : fix_scalars rest'
        Nothing -> ZNeg : fix_scalars rest
    (XI:rest) -> case parse_z ts of
        Just (z, rest') -> IntLit z : fix_scalars rest'
        Nothing -> XI : fix_scalars rest
    (XO:rest) -> case parse_z ts of
        Just (z, rest') -> IntLit z : fix_scalars rest'
        Nothing -> XO : fix_scalars rest
    (t:rest) -> t : fix_scalars rest

parse_int_elem :: [Tok] -> Maybe (Integer, [Tok])
parse_int_elem ts = case skip_white ts of
    (Zero:rest) -> Just (0, rest)
    (One:rest) -> Just (1, rest)
    (NatLit n:rest) -> Just (fromIntegral n, rest)
    (IntLit z:rest) -> Just (z, rest)
    (LParen:rest) -> case skip_white rest of
        (Zero:rest1) -> case skip_white rest1 of
            (RParen:rest2) -> Just (0, rest2)
            _ -> Nothing
        (One:rest1) -> case skip_white rest1 of
            (RParen:rest2) -> Just (1, rest2)
            _ -> Nothing
        (NatLit n:rest1) -> case skip_white rest1 of
            (RParen:rest2) -> Just (fromIntegral n, rest2)
            _ -> Nothing
        (IntLit z:rest1) -> case skip_white rest1 of
            (RParen:rest2) -> Just (z, rest2)
            _ -> Nothing
        _ -> Nothing
    _ -> Nothing

parse_int_list :: [Tok] -> Maybe ([Integer], [Tok])
parse_int_list ts = go [] 0 ts where
    go acc !lp (Cons:rest) = do
        (!v, rest') <- parse_int_elem rest
        go (v:acc) lp rest'
    go acc !lp (Nil:rest)
        | not (null acc) = Just (reverse acc, drop_rps lp rest)
        | otherwise = Nothing
    go acc !lp (White _:rest) = go acc lp rest
    go acc !lp (LParen:rest) = go acc (lp+1) rest
    go _ _ _ = Nothing

fix_lists :: [Tok] -> [Tok]
fix_lists ts = case ts of
    [] -> []
    (Cons:rest) -> case parse_int_list ts of
        Just (zs, rest') -> IntListLit zs : fix_lists rest'
        Nothing -> Cons : fix_lists rest
    (t:rest) -> t : fix_lists rest

fix_lits :: [Tok] -> [Tok]
fix_lits = fix_lists . fix_scalars

print_tok :: Tok -> T.Text
print_tok (White w) = w
print_tok (Txt t) = t
print_tok LParen = "("
print_tok RParen = ")"
print_tok Zero = "0"
print_tok One = "1"
print_tok Succ = "Prelude.succ"
print_tok (NatLit n) = T.pack $ show n
print_tok ZPos = "(\\x -> x)"
print_tok ZNeg = "(\\x -> Prelude.negate x)"
print_tok XI = "(\\x -> 2 Prelude.* x Prelude.+ 1)"
print_tok XO = "(\\x -> 2 Prelude.* x)"
print_tok (IntLit z) = if z < 0 then "(" <> T.pack (show z) <> ")" else T.pack (show z)
print_tok Cons = "(:)"
print_tok Nil = "[]"
print_tok (IntListLit zs) = "[" <> T.intercalate ", " (map (T.pack . show) zs) <> "]"

main :: IO ()
main = do
    (fileIn:_) <- getArgs
    txt <- T.readFile fileIn
    T.writeFile fileIn $ T.concat $ map print_tok $ fix_lits $ toks txt
