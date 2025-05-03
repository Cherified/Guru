Require Import String List Psatz.
Require Import Guru.Lib.Library Guru.Lib.Word.
Require Import Guru.Syntax.

Set Implicit Arguments.
Set Asymmetric Patterns.

Import ListNotations.

Fixpoint evalExpr k (e: Expr type k): type k :=
  match e in Expr _ k return type k with
  | Var _ v => v
  | Const _ v => v
  | Or _ ls => fold_left (evalOrBinary _) (map (@evalExpr _) ls) (getDefault _)
  | And ls => fold_left andb (map (@evalExpr Bool) ls) true
  | Xor ls => fold_left xorb (map (@evalExpr Bool) ls) false
  | Not v => negb (evalExpr v)
  | Inv _ v => wneg (evalExpr v)
  | TruncLsb _ _ v => truncLsb (evalExpr v)
  | TruncMsb _ _ v => truncMsb (evalExpr v)
  | UOr n v => wuor (evalExpr v)
  | UAnd n v => wuand (evalExpr v)
  | UXor n v => wuxor (evalExpr v)
  | Add n ls => fold_left wadd (map (@evalExpr (Bit n)) ls) (ZToWord n 0)
  | Mul n ls => fold_left wmul (map (@evalExpr (Bit n)) ls) (ZToWord n 0)
  | Band n ls => fold_left wand (map (@evalExpr (Bit n)) ls) (ZToWord n 0)
  | Bxor n ls => fold_left wxor (map (@evalExpr (Bit n)) ls) (ZToWord n 0)
  | Div n a b => wdiv (evalExpr a) (evalExpr b)
  | Rem n a b => wmod (evalExpr a) (evalExpr b)
  | Sll _ _ a b => wslu (evalExpr a) (ZToWord _ (wordVal _ (evalExpr b)))
  | Srl _ _ a b => wsru (evalExpr a) (ZToWord _ (wordVal _ (evalExpr b)))
  | Sra _ _ a b => wsra (evalExpr a) (evalExpr b)
  | Concat _ _ a b => wcombine (evalExpr a) (evalExpr b)
  | ITE _ p t f => if evalExpr p then evalExpr t else evalExpr f
  | Eq _ a b => if isEq _ (evalExpr a) (evalExpr b) then true else false
  | ReadStruct _ v i => (getStructTupleToFunc _ _ (evalExpr v)) i
  | ReadArray n _ k v i =>
      match lt_dec (Z.to_nat (wordVal _ (evalExpr i))) n return type k with
      | left pf => getArrayTupleToFunc type _ _ (evalExpr v) (FinArray_of_nat_lt pf)
      | right _ => getDefault k
      end
  | ReadArrayConst _ _ v i => (getArrayTupleToFunc _ _ _ (evalExpr v)) i
  | BuildStruct _ vs => getStructFuncToTuple _ _ (fun i => evalExpr (vs i))
  | BuildArray _ _ vs => getArrayFuncToTuple _ _ _ (fun i => evalExpr (vs i))
  | ToBit _ v => evalToBit _ (evalExpr v)
  | FromBit _ v => evalFromBit _ (evalExpr v)
  end.
