From Stdlib Require Import String List Zmod Bool.
Require Import Guru.Library Guru.Syntax Guru.Semantics Guru.IdentParsing.

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
  (Build_Prod (snd sv1%gurustruct) .. (Build_Prod (snd svn%gurustruct) tt) ..): guru_scope.

Notation "'STRUCT' { sv1 ; .. ; svn }" :=
  (BuildStruct _
     (ls := (cons (fst sv1%gurustruct, _) .. (cons (fst svn%gurustruct, _) nil) ..))
     (Build_Prod (snd sv1%gurustruct) .. (Build_Prod (snd svn%gurustruct) tt) ..)): guru_scope.

Definition structList [ty ls] (v: Expr ty (Struct ls)) := ls.
Notation "s ` name" :=
  (ReadStruct s (getFinStruct name%string (structList s))) (at level 0, only parsing): guru_scope.
Notation "s `{ name <- v }" :=
  (UpdateStruct s (getFinStruct name%string (structList s)) v) (only parsing): guru_scope.

Notation "'ARRAY_CONST' [ v1 ; .. ; vn ]" :=
  (Build_SameTuple (n := length (cons v1 .. (cons vn nil) ..))
     (tupleElems := (cons v1 .. (cons vn nil) ..)) I): guru_scope.

Notation "'ARRAY' [ v1 ; .. ; vn ]" :=
  (BuildArray (Build_SameTuple (n := length (cons v1 .. (cons vn nil) ..))
                 (tupleElems := (cons v1 .. (cons vn nil) ..)) I)): guru_scope.

Notation "v @[ i ]" := (ReadArray v i): guru_scope.

Definition arraySize [ty k n] (e: Expr ty (Array n k)) := n.
Notation "v $[ i ]" := (ReadArrayConst v (@Build_FinType (arraySize v) i I)): guru_scope.

Notation "v @[ i <- e ]" := (UpdateArray v i e): guru_scope.
Notation "v $[ i <- e ]" := (UpdateArrayConst v (@Build_FinType (arraySize v) i I) e): guru_scope.

Notation "# x" := (Var _ _ x) (no associativity, at level 0, x name, format "# x"): guru_scope.
Notation "## x" := ltac:(match type of x with
                         | ?ty ?k => exact (Var ty k x)
                         end) (no associativity, at level 0, x name, only parsing): guru_scope.

Notation ConstBit := (Const _ (Bit _)).
Notation ConstBool := (Const _ Bool).
Notation ConstDefK k := (Const _ k (Default k)).
Notation ConstDef := (Const _ _ (Default _)).

Ltac getTy := match goal with
              | ty: Kind -> Type |- _ => exact ty
              end.
Notation ConstT := (Const ltac:(getTy)) (only parsing).
Notation ConstTBit := (ConstT (Bit _)) (only parsing).
Notation ConstTBool := (ConstT Bool) (only parsing).
Notation ConstTDefK k := (ConstT k (Default k)) (only parsing).
Notation ConstTDef := (ConstT _ (Default _)) (only parsing).

Notation "$ x" := (ConstBit (Zmod.of_Z _ x)) (no associativity, at level 0): guru_scope.

Notation "{< a , .. , b >}" := (Concat a .. (Concat b (Const _ (Bit 0) Zmod.zero)) ..) (at level 0, a at level 200):
    guru_scope.

Definition bitSize [ty n] (e: Expr ty (Bit n)) := n.
Notation "x `[ msb : lsb ]" := (ConstExtract ltac:(let y := eval simpl in (Z.sub (Z.sub (bitSize x) msb%Z) 1%Z)
                                                     in exact y)
                                                    ltac:(let y := eval simpl in (msb - lsb + 1)%Z
                                                            in exact y) lsb x)
                                 (msb at level 0, only parsing): guru_scope.

Ltac simplKind x := match type of x with
                    | ?T => let Y := eval simpl in T in exact (x : Y)
                    end.

Ltac structSimplCbn x :=
  (let y := eval cbv [getFinStruct structList arraySize fieldK] in x in
     let y := eval cbn in y in
       simplKind y).

Notation structSimplCbn x := ltac:(structSimplCbn x) (only parsing).

Ltac structSimplCbv x :=
  (let y := eval cbv [getFinStruct structList arraySize fieldK forceOption getFinStructOption length
                        fst snd String.eqb Ascii.eqb Bool.eqb fieldNameK nth_pf finNum] in x in
     simplKind y).

Notation structSimplCbv x := ltac:(structSimplCbv x) (only parsing).

Ltac evalSimpl x :=
  let x := eval cbn delta -[evalFromBitStruct] beta iota in x in
    let x := eval cbv delta [mapSameTuple updSameTuple updSameTupleNat transparent_Is_true'] beta iota in x in
      let x := eval cbn delta -[evalFromBitStruct] beta iota in x in
        exact x.

Notation evalSimpl x := ltac:(evalSimpl x) (only parsing).

Ltac evalSimplGoal :=
  cbn delta -[evalFromBitStruct] beta iota;
  cbv delta [mapSameTuple updSameTuple updSameTupleNat transparent_Is_true'] beta iota;
  cbn delta -[evalFromBitStruct] beta iota.

Notation "'RegRead' letv <- name 'in' m ; cont" :=
  (ReadReg (Stringify letv) (getFinStruct name%string m.(mregs)) (fun letv => cont))
    (at level 20): guru_scope.

Notation "'RegWrite' name 'in' m <- v ; cont" :=
  (WriteReg (getFinStruct name%string m.(mregs)) v cont) (at level 20): guru_scope.

Notation "'MemReadRq' name 'in' m ! p <- i ; cont" :=
  (ReadRqMem (getFinStruct name%string m.(mmems)) i
     (@Build_FinType (fieldK (getFinStruct name%string m.(mmems))).(memUPort) p I) cont)
    (at level 20): guru_scope.

Notation "'MemReadRp' letv <-  name 'in' m ! p ; cont" :=
  (ReadRpMem (Stringify letv) (getFinStruct name%string m.(mmems))
     (@Build_FinType (fieldK (getFinStruct name%string m.(mmems))).(memUPort) p I) (fun letv => cont))
    (at level 20): guru_scope.

Notation "'MemWrite' name 'in' m ! i <- v ; cont" :=
  (WriteMem (getFinStruct name%string m.(mmems)) i v cont) (at level 20): guru_scope.

Notation "'RegReadU' letv <- name 'in' m ; cont" :=
  (ReadRegU (Stringify letv) (getFinStruct name%string m.(mregUs)) (fun letv => cont))
    (at level 20): guru_scope.

Notation "'RegWriteU' name 'in' m <- v ; cont" :=
  (WriteRegU (getFinStruct name%string m.(mregUs)) v cont) (at level 20): guru_scope.

Notation "'MemReadRqU' name 'in' m ! p <- i ; cont" :=
  (ReadRqMemU (getFinStruct name%string m.(mmemUs)) i
     (@Build_FinType (fieldK (getFinStruct name%string m.(mmemUs))).(memUPort) p I) cont)
    (at level 20): guru_scope.

Notation "'MemReadRpU' letv <-  name 'in' m ! p ; cont" :=
  (ReadRpMemU (Stringify letv) (getFinStruct name%string m.(mmemUs))
     (@Build_FinType (fieldK (getFinStruct name%string m.(mmemUs))).(memUPort) p I) (fun letv => cont))
    (at level 20): guru_scope.

Notation "'MemWriteU' name 'in' m ! i <- v ; cont" :=
  (WriteMemU (getFinStruct name%string m.(mmemUs)) i v cont) (at level 20): guru_scope.

Notation "'Put' name 'in' m <- v ; cont" :=
  (Send (getFinStruct name%string m.(msends)) v cont) (at level 20): guru_scope.

Notation "'Get' letv <- name 'in' m ; cont" :=
  (Recv (Stringify letv) (getFinStruct name%string m.(mrecvs)) (fun letv => cont))
    (at level 20): guru_scope.

Notation "'Let' letv : k' <- e ; cont" :=
  (LetExp (Stringify letv) (k' := k') e (fun letv => cont)) (at level 20, letv name): guru_scope.

Notation "'Let' letv <- e ; cont" :=
  (LetExp (Stringify letv) e (fun letv => cont)) (at level 20, letv name): guru_scope.

Notation "'LetA' letv : k' <- a ; cont" :=
  (LetAction (Stringify letv) (k' := k') a (fun letv => cont))
    (at level 20, a at level 0, letv name): guru_scope.

Notation "'LetA' letv <- a ; cont" :=
  (LetAction (Stringify letv) a (fun letv => cont))
    (at level 20, a at level 0, letv name): guru_scope.

Notation "'Act' a ; cont" :=
  (LetAction ""%string a (fun _ => cont)) (at level 20, a at level 0): guru_scope.

Notation "'Random' letv : k' ; cont" :=
  (NonDet (Stringify letv) k' (fun letv => cont)) (at level 20, letv name): guru_scope.

Notation "'LetIf' letv : k' <- 'If' p 'Then' t 'Else' f ; cont" :=
  (IfElse (Stringify letv) p (k' := k') t f (fun letv => cont))
    (at level 20, t at level 0, f at level 0, letv name): guru_scope.

Notation "'LetIf' letv <- 'If' p 'Then' t 'Else' f ; cont" :=
  (IfElse (Stringify letv) p t f (fun letv => cont))
    (at level 20, t at level 0, f at level 0, letv name): guru_scope.

Notation "'LetIf' letv : k' <- 'If' p 'Then' t ; cont" :=
  (IfElse (Stringify letv) p (k' := k') t (Return (ConstDefK k')) (fun letv => cont))
    (at level 20, t at level 0, letv name): guru_scope.

Notation "'LetIf' letv <- 'If' p 'Then' t ; cont" :=
  (IfElse (Stringify letv) p t (Return ConstDef) (fun letv => cont))
    (at level 20, t at level 0, letv name): guru_scope.

Notation "'If' p 'Then' t 'Else' f ; cont" :=
  (IfElse ""%string p t f (fun _ => cont)) (at level 20, t at level 0, f at level 0): guru_scope.

Notation "'If' p 'Then' t ; cont" :=
  (IfElse ""%string p t (Return ConstDef) (fun _ => cont)) (at level 20, t at level 0): guru_scope.

Notation "'Sys' ls ; cont" :=
  (System ls cont) (at level 20): guru_scope.

Notation "'SysE' ls ; cont" :=
  (SystemE ls cont) (at level 20): guru_scope.

Notation "'LetE' letv : k' <- e ; cont" :=
  (LetEx (Stringify letv) (k' := k') (RetE e) (fun letv => cont)) (at level 20, letv name): guru_scope.

Notation "'LetE' letv <- e ; cont" :=
  (LetEx (Stringify letv) (RetE e) (fun letv => cont)) (at level 20, letv name): guru_scope.

Notation "'LETE' letv : k' <- le ; cont" :=
  (LetEx (Stringify letv) (k' := k') le (fun letv => cont)) (at level 20, letv name): guru_scope.

Notation "'LETE' letv <- le ; cont" :=
  (LetEx (Stringify letv) le (fun letv => cont)) (at level 20, letv name): guru_scope.

Notation "'LetIfE' letv : k' <- 'IfE' p 'ThenE' t 'ElseE' f ; cont" :=
  (IfElseE (Stringify letv) p (k' := k') t f (fun letv => cont))
    (at level 20, t at level 0, f at level 0, letv name): guru_scope.

Notation "'LetIfE' letv <- 'IfE' p 'ThenE' t 'ElseE' f ; cont" :=
  (IfElseE (Stringify letv) p t f (fun letv => cont))
    (at level 20, t at level 0, f at level 0, letv name): guru_scope.

Notation "'LetL' letv : k' <- le ; cont" :=
  (LetAction (Stringify letv) (k' := k') (toAction _ le) (fun letv => cont))
    (at level 20, le at level 0, letv name): guru_scope.
 
Notation "'LetL' letv <- le ; cont" :=
  (LetAction (Stringify letv) (toAction _ le) (fun letv => cont))
    (at level 20, le at level 0, letv name): guru_scope.

Notation ITE0 p v := (ITE p v ConstTDef) (only parsing).

Section Structs.
  Local Open Scope guru_scope.
  Definition Option k := STRUCT_TYPE {
                             "data"  :: k ;
                             "valid" :: Bool }.

  Definition Pair k1 k2 := STRUCT_TYPE {
                               "fst" :: k1 ;
                               "snd" :: k2 }.

  Section Ty.
    Variable ty: Kind -> Type.
    Definition mkSome k (e: Expr ty k): Expr ty (Option k) := STRUCT { "data"  ::= e ;
                                                                       "valid" ::= ConstT Bool true }.
    Definition mkNone k: Expr ty (Option k) := STRUCT { "data"  ::= ConstTDefK k ;
                                                        "valid" ::= ConstTBool false }.
    Definition mkPair ty k1 (e1: Expr ty k1) k2 (e2: Expr ty k2) := STRUCT { "fst" ::= e1 ;
                                                                             "snd" ::= e2 }.
  End Ty.

  Definition RegsStruct (decl: ModDecl) :=
    STRUCT_TYPE {
        "regs"  :: Struct (map (fun x => (fst x, (snd x).(regKind))) decl.(modRegs));
        "regUs" :: Struct decl.(modRegUs) }.

  Definition MemRqsStruct (decl: ModDecl) :=
    STRUCT_TYPE {
        "rqs" :: Struct (map (fun x => (fst x, Array (snd x).(memPort)
                                                 (Option (Bit (Z.log2_up (Z.of_nat (snd x).(memSize)))))))
                           decl.(modMems));
        "rqUs" :: Struct (map (fun x => (fst x, Array (snd x).(memUPort)
                                                  (Option (Bit (Z.log2_up (Z.of_nat (snd x).(memUSize)))))))
                            decl.(modMemUs))
      }.

  Definition MemRpsStruct (decl: ModDecl) :=
    STRUCT_TYPE {
        "rps" :: Struct (map (fun x => (fst x, Array (snd x).(memPort) (snd x).(memKind))) decl.(modMems));
        "rpUs" :: Struct (map (fun x => (fst x, Array (snd x).(memUPort) (snd x).(memUKind))) decl.(modMemUs)) }.

  Definition MWrite sz k := Option (STRUCT_TYPE {
                                        "idx" :: Bit (Z.log2_up (Z.of_nat sz));
                                        "val" :: k }).

  Definition MemWrsStruct (decl: ModDecl) :=
    STRUCT_TYPE {
        "wrs" :: Struct (map (fun x => (fst x, MWrite (snd x).(memSize) (snd x).(memKind))) decl.(modMems));
        "wrUs" :: Struct (map (fun x => (fst x, MWrite (snd x).(memUSize) (snd x).(memUKind))) decl.(modMemUs)) }.

  Definition SendsStruct (decl: ModDecl) := Struct (map (fun x => (fst x, Option (snd x))) decl.(modSends)).
  Definition RecvsStruct (decl: ModDecl) := Struct decl.(modRecvs).

  Definition InputsStruct (decl: ModDecl) := STRUCT_TYPE {
                                                 "memRps" :: MemRpsStruct decl;
                                                 "recvs" :: RecvsStruct decl }.

  Definition OutputsStruct (decl: ModDecl) := STRUCT_TYPE {
                                                  "memRqs" :: MemRqsStruct decl;
                                                  "memWrs" :: MemWrsStruct decl;
                                                  "sends"  :: SendsStruct decl }.

  Definition ArgStruct (decl: ModDecl) := STRUCT_TYPE {
                                              "state" :: RegsStruct decl;
                                              "inputs" :: InputsStruct decl }.

  Definition ReturnStruct (decl: ModDecl) := STRUCT_TYPE {
                                                 "state" :: RegsStruct decl;
                                                 "outputs" :: OutputsStruct decl }.
End Structs.
