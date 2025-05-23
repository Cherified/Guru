From Stdlib Require Import String List.
Require Import Guru.Lib.Library Guru.Lib.Word Guru.Lib.IdentParsing.
Require Import Guru.Syntax.

Set Implicit Arguments.
Unset Strict Implicit.
Set Asymmetric Patterns.

Import ListNotations.

Unset Printing Implicit Defensive.

Declare Scope guru_scope.
Delimit Scope guru_scope with guru.

Local Declare Scope gurustruct_scope.
Local Delimit Scope gurustruct_scope with gurustruct.

Notation "name :: k" := (name%string: string, k: Kind) : gurustruct_scope.

Notation "name ::= v" := (name%string: string, v) (at level 95) : gurustruct_scope.

Notation "'STRUCT_TYPE' { x1 ; .. ; xn }" :=
  (Struct (cons x1%gurustruct .. (cons xn%gurustruct nil) ..)): guru_scope.

Notation "'STRUCT_CONST' { sv1 ; .. ; svn }" :=
  (pair (snd sv1%gurustruct) .. (pair (snd svn%gurustruct) tt) ..): guru_scope.

Notation "'STRUCT' { sv1 ; .. ; svn }" :=
  (BuildStruct
     (structToFunc
        (ls := (cons (fst sv1%gurustruct, _) .. (cons (fst svn%gurustruct, _) nil) ..))
        (pair (snd sv1%gurustruct) .. (pair (snd svn%gurustruct) tt) ..))): guru_scope.

Definition structList [ty ls] (v: Expr ty (Struct ls)) := ls.

Notation "s ` name" := (ReadStruct s (getFinStruct name%string (structList s)))
                         (at level 83, left associativity): guru_scope.
Notation "s `{ name <- v }" := (UpdateStruct s (getFinStruct name%string (structList s)) v) : guru_scope.

Notation "'ARRAY_CONST' [ v1 ; .. ; vn ]" :=
  (pair v1 .. (pair vn tt) ..): guru_scope.

Notation "'ARRAY' [ v1 ; .. ; vn ]" :=
  (BuildArray
     (arrayToFunc
        ((pair v1 .. (pair vn tt) ..):
          SameTuple (Expr _ _) (length (cons v1 .. (cons vn nil) ..))))): guru_scope.

Notation "v @[ i ]" := (ReadArray v i): guru_scope.
Definition arraySize [ty k n] (e: Expr ty (Array n k)) := n.
Notation "v $[ i ]" := (ReadArrayConst v (@FinArray_of_nat_ltDec i (arraySize v) eq_refl)): guru_scope.

Notation "v @[ i <- e ]" := (UpdateArray v i e): guru_scope.
Notation "v $[ i <- e ]" := (UpdateArrayConst v (@FinArray_of_nat_ltDec i (arraySize v) eq_refl) e): guru_scope.

Notation "# x" := (Var _ _ x) (no associativity, at level 0, x name, format "# x"): guru_scope.
Notation "## x" := ltac:(match type of x with
                         | ?ty ?k => exact (Var ty k x)
                         end) (no associativity, at level 0, x name, only parsing): guru_scope.

Notation "sz ''h' a" := (ZToWord sz (hex a%string)) (at level 0).
Notation "'Ox' a" := (ZToWord _ (hex a%string)) (at level 0).
Notation "sz ''b' a" := (ZToWord sz (bin a%string)) (at level 0).
Notation "'Ob' a" := (ZToWord _ (bin a%string)) (at level 0).

Goal 8'h"a" = ZToWord 8 10.
Proof.
  reflexivity.
Qed.

Goal Ox"41" = ZToWord 7 65.
Proof.
  reflexivity.
Qed.

Goal Ob"1010" = ZToWord 8 10.
Proof.
  reflexivity.
Qed.

Goal Ob"1000001" = ZToWord 7 65.
Proof.
  reflexivity.
Qed.

Notation ConstBit := (Const _ (Bit _)).
Notation ConstBool := (Const _ Bool).
Notation ConstDefK k := (Const _ k (Default k)).
Notation ConstDef := (Const _ _ (Default _)).

Notation ConstT := (Const ltac:(match goal with
                                | ty: Kind -> Type |- _ => exact ty
                                end)) (only parsing).
Notation ConstTBit := (ConstT (Bit _)) (only parsing).
Notation ConstTBool := (ConstT Bool) (only parsing).
Notation ConstTDefK k := (ConstT k (Default k)) (only parsing).
Notation ConstTDef := (ConstT _ (Default _)) (only parsing).

Notation "$ x" := (ConstBit (natToWord _ x)) (no associativity, at level 0): guru_scope.

Notation "{< a , .. , b >}" := (Concat a .. (Concat b (ConstBit WO)) ..) (at level 0, a at level 200): guru_scope.

Definition bitSize [ty n] (e: Expr ty (Bit n)) := n.
Notation "x `[ msb : lsb ]" := (ConstExtract ltac:(let y := eval simpl in (bitSize x - msb - 1)
                                                     in exact y)
                                                    ltac:(let y := eval simpl in (msb - lsb + 1)
                                                            in exact y) lsb x)
                                 (msb at level 0, only parsing): guru_scope.

Notation "'RegRead' letv <- name 'in' m ; cont" :=
  (ReadReg (Stringify letv) (getFinStruct name%string (mregs m)) (fun letv => cont))
    (at level 20, only parsing): guru_scope.

Notation "'RegWrite' name 'in' m <- v ; cont" :=
  (WriteReg (getFinStruct name%string (mregs m)) v cont) (at level 20): guru_scope.

Notation "'MemReadRq' name 'in' m ! p <- i ; cont" :=
  (ReadRqMem (getFinStruct name%string (mmems m)) i
     (@FinArray_of_nat_ltDec p (memUPort (fieldK (getFinStruct name%string (mmems m)))) eq_refl) cont)
    (at level 20): guru_scope.

Notation "'MemReadRp' letv <-  name 'in' m ! p ; cont" :=
  (ReadRpMem (Stringify letv) (getFinStruct name%string (mmems m))
     (@FinArray_of_nat_ltDec p (memUPort (fieldK (getFinStruct name%string (mmems m)))) eq_refl) (fun letv => cont))
    (at level 20, only parsing): guru_scope.

Notation "'MemWrite' name 'in' m ! i <- v ; cont" :=
  (WriteMem (getFinStruct name%string (mmems m)) i v cont) (at level 20): guru_scope.

Notation "'RegReadU' letv <- name 'in' m ; cont" :=
  (ReadRegU (Stringify letv) (getFinStruct name%string (mregUs m)) (fun letv => cont))
    (at level 20, only parsing): guru_scope.

Notation "'RegWriteU' name 'in' m <- v ; cont" :=
  (WriteRegU (getFinStruct name%string (mregUs m)) v cont) (at level 20): guru_scope.

Notation "'MemReadRqU' name 'in' m ! p <- i ; cont" :=
  (ReadRqMemU (getFinStruct name%string (mmemUs m)) i
     (@FinArray_of_nat_ltDec p (memUPort (fieldK (getFinStruct name%string (mmemUs m)))) eq_refl) cont)
    (at level 20): guru_scope.

Notation "'MemReadRpU' letv <-  name 'in' m ! p ; cont" :=
  (ReadRpMemU (Stringify letv) (getFinStruct name%string (mmemUs m))
     (@FinArray_of_nat_ltDec p (memUPort (fieldK (getFinStruct name%string (mmemUs m)))) eq_refl) (fun letv => cont))
    (at level 20, only parsing): guru_scope.

Notation "'MemWriteU' name 'in' m ! i <- v ; cont" :=
  (WriteMemU (getFinStruct name%string (mmemUs m)) i v cont) (at level 20): guru_scope.

Notation "'Put' name 'in' m <- v ; cont" :=
  (Send (getFinStruct name%string (msends m)) v cont) (at level 20): guru_scope.

Notation "'Get' letv <- name 'in' m ; cont" :=
  (Recv (Stringify letv) (getFinStruct name%string (mrecvs m)) (fun letv => cont))
    (at level 20, only parsing): guru_scope.

Notation "'Let' letv : k' <- e ; cont" :=
  (LetExp (Stringify letv) (k' := k') e (fun letv => cont)) (at level 20, letv name, only parsing): guru_scope.

Notation "'Let' letv <- e ; cont" :=
  (LetExp (Stringify letv) e (fun letv => cont)) (at level 20, letv name, only parsing): guru_scope.

Notation "'LetA' letv : k' <- a ; cont" :=
  (LetAction (Stringify letv) (k' := k') a (fun letv => cont))
    (at level 20, a at level 0, letv name, only parsing): guru_scope.

Notation "'LetA' letv <- a ; cont" :=
  (LetAction (Stringify letv) a (fun letv => cont))
    (at level 20, a at level 0, letv name, only parsing): guru_scope.

Notation "'Act' a ; cont" :=
  (LetAction ""%string a (fun _ => cont)) (at level 20, a at level 0): guru_scope.

Notation "'Random' letv : k' ; cont" :=
  (NonDet (Stringify letv) k' (fun letv => cont)) (at level 20, letv name, only parsing): guru_scope.

Notation "'LetIf' letv : k' <- 'If' p 'Then' t 'Else' f ; cont" :=
  (IfElse (Stringify letv) p (k' := k') t f (fun letv => cont))
    (at level 20, t at level 0, f at level 0, letv name, only parsing): guru_scope.

Notation "'LetIf' letv <- 'If' p 'Then' t 'Else' f ; cont" :=
  (IfElse (Stringify letv) p t f (fun letv => cont))
    (at level 20, t at level 0, f at level 0, letv name, only parsing): guru_scope.

Notation "'LetIf' letv : k' <- 'If' p 'Then' t ; cont" :=
  (IfElse (Stringify letv) p (k' := k') t (Return (ConstDefK k')) (fun letv => cont))
    (at level 20, t at level 0, letv name, only parsing): guru_scope.

Notation "'LetIf' letv <- 'If' p 'Then' t ; cont" :=
  (IfElse (Stringify letv) p t (Return ConstDef) (fun letv => cont))
    (at level 20, t at level 0, letv name, only parsing): guru_scope.

Notation "'If' p 'Then' t 'Else' f ; cont" :=
  (IfElse ""%string p t f (fun _ => cont)) (at level 20, t at level 0, f at level 0): guru_scope.

Notation "'If' p 'Then' t ; cont" :=
  (IfElse ""%string p t (Return ConstDef) (fun _ => cont)) (at level 20, t at level 0): guru_scope.

Notation "'Sys' ls ; cont" :=
  (System ls cont) (at level 20): guru_scope.

Notation "'SysE' ls ; cont" :=
  (SystemE ls cont) (at level 20): guru_scope.

Notation "'LetE' letv : k' <- e ; cont" :=
  (LetEx (Stringify letv) (k' := k') (RetE e) (fun letv => cont)) (at level 20, letv name, only parsing): guru_scope.

Notation "'LetE' letv <- e ; cont" :=
  (LetEx (Stringify letv) (RetE e) (fun letv => cont)) (at level 20, letv name, only parsing): guru_scope.

Notation "'LETE' letv : k' <- le ; cont" :=
  (LetEx (Stringify letv) (k' := k') le (fun letv => cont)) (at level 20, letv name, only parsing): guru_scope.

Notation "'LETE' letv <- le ; cont" :=
  (LetEx (Stringify letv) le (fun letv => cont)) (at level 20, letv name, only parsing): guru_scope.

Notation "'LetIfE' letv : k' <- 'IfE' p 'ThenE' t 'ElseE' f ; cont" :=
  (IfElseE (Stringify letv) p (k' := k') t f (fun letv => cont))
    (at level 20, t at level 0, f at level 0, letv name, only parsing): guru_scope.

Notation "'LetIfE' letv <- 'IfE' p 'ThenE' t 'ElseE' f ; cont" :=
  (IfElseE (Stringify letv) p t f (fun letv => cont))
    (at level 20, t at level 0, f at level 0, letv name, only parsing): guru_scope.

Notation "'LetL' letv : k' <- le ; cont" :=
  (LetAction (Stringify letv) (k' := k') (toAction le) (fun letv => cont))
    (at level 20, le at level 0, letv name, only parsing): guru_scope.
 
Notation "'LetL' letv <- le ; cont" :=
  (LetAction (Stringify letv) (toAction le) (fun letv => cont))
    (at level 20, le at level 0, letv name, only parsing): guru_scope.

Notation ITE0 p v := (ITE p v ConstTDef) (only parsing).
