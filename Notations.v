From Stdlib Require Import String List Zmod Bool ZArith Ascii.
Require Import Guru.Library Guru.Syntax Guru.Semantics Guru.IdentParsing.

Delimit Scope char_scope with ascii.

Set Implicit Arguments.
Unset Strict Implicit.
Set Asymmetric Patterns.

Import ListNotations.

Unset Printing Implicit Defensive.

Section PurePathLookup.
  Variable A : Type.

  Fixpoint getLeafPath (t : Tree A) (path : list string) : option (LeafPath t) :=
    match t with
    | Leaf name a =>
        match path with
        | x :: nil => if String.eqb x name then Some tt else None
        | _ => None
        end
    | Node name children =>
        match path with
        | x :: xs => if String.eqb x name
                     then
                       (fix loop (ls : list (Tree A)) :
                          option ((fix loop' (ls: list (Tree A)) : Type :=
                                    match ls with
                                    | nil => Empty_set
                                    | x :: xs => (LeafPath x + loop' xs)%type
                                    end) ls) :=
                          match ls return
                            option ((fix loop' (ls: list (Tree A)) : Type :=
                                       match ls with
                                       | nil => Empty_set
                                       | x :: xs => (LeafPath x + loop' xs)%type
                                       end) ls)
                          with
                          | nil => None
                          | y :: ys =>
                              match getLeafPath y xs with
                              | Some p => Some (inl p)
                              | None =>
                                  match loop ys with
                                  | Some p => Some (inr p)
                                  | None => None
                                  end
                              end
                          end) children
                     else None
        | _ => None
        end
    end.
End PurePathLookup.

Arguments getLeafPath [A] t path.

Definition getRegPath (t : Tree ModElem) (path : string) : option (RegPath t) :=
  match getLeafPath t (splitDot path) as o return option (RegPath t) with
  | Some p =>
      match isRegElem (getLeaf p) as b return (isRegElem (getLeaf p) = b) -> option (RegPath t) with
      | true => fun pf => Some {| regPath := p ; regPathPf := transparent_Is_true _ (Is_true_eq_left _ pf) |}
      | false => fun _ => None
      end eq_refl
  | None => None
  end.

Definition getMemPath (t : Tree ModElem) (path : string) : option (MemPath t) :=
  match getLeafPath t (splitDot path) as o return option (MemPath t) with
  | Some p =>
      match isMemElem (getLeaf p) as b return (isMemElem (getLeaf p) = b) -> option (MemPath t) with
      | true => fun pf => Some {| memPath := p ; memPathPf := transparent_Is_true _ (Is_true_eq_left _ pf) |}
      | false => fun _ => None
      end eq_refl
  | None => None
  end.

Definition getSendPath (t : Tree ModElem) (path : string) : option (SendPath t) :=
  match getLeafPath t (splitDot path) as o return option (SendPath t) with
  | Some p =>
      match isSendElem (getLeaf p) as b return (isSendElem (getLeaf p) = b) -> option (SendPath t) with
      | true => fun pf => Some {| sendPath := p ; sendPathPf := transparent_Is_true _ (Is_true_eq_left _ pf) |}
      | false => fun _ => None
      end eq_refl
  | None => None
  end.

Definition getRecvPath (t : Tree ModElem) (path : string) : option (RecvPath t) :=
  match getLeafPath t (splitDot path) as o return option (RecvPath t) with
  | Some p =>
      match isRecvElem (getLeaf p) as b return (isRecvElem (getLeaf p) = b) -> option (RecvPath t) with
      | true => fun pf => Some {| recvPath := p ; recvPathPf := transparent_Is_true _ (Is_true_eq_left _ pf) |}
      | false => fun _ => None
      end eq_refl
  | None => None
  end.

Definition getRegPathTree (t : Tree ModElem) (path : string) :=
  forceOption (getRegPath t path).

Definition getMemPathTree (t : Tree ModElem) (path : string) :=
  forceOption (getMemPath t path).

Definition getSendPathTree (t : Tree ModElem) (path : string) :=
  forceOption (getSendPath t path).

Definition getRecvPathTree (t : Tree ModElem) (path : string) :=
  forceOption (getRecvPath t path).





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

Definition readTreeReg {t} (s: TreeState ModElemState t) (p: RegPath t) :
  type (registerKind (getRegFromPath p)) :=
  castStateReg p (readTreeState t s (regPath p)).
Arguments readTreeReg [t] s p / .

Definition readTreeMem {t} (s: TreeState ModElemState t) (p: MemPath t) :
  type (Array (getMemFromPath p).(memorySize) (getMemFromPath p).(memoryKind)) **
  type (Array (getMemFromPath p).(memoryPort) (getMemFromPath p).(memoryKind)) :=
  castStateMem p (readTreeState t s (memPath p)).
Arguments readTreeMem [t] s p / .

Definition readTreeSend {t} (s: TreeState ModElemState t) (p: SendPath t) :
  list (type (getSendKind p)) :=
  castStateSend p (readTreeState t s (sendPath p)).
Arguments readTreeSend [t] s p / .

Definition readTreeRecv {t} (s: TreeState ModElemState t) (p: RecvPath t) :
  list (type (getRecvKind p)) :=
  castStateRecv p (readTreeState t s (recvPath p)).
Arguments readTreeRecv [t] s p / .

Notation "a @% b" := (readDiffTupleStr a b) (at level 0).

Notation "'RdReg' ( s , p )" := (readTreeReg s (getRegPathTree ltac:(match type of s with
                                                                     | TreeState _ ?t => exact t
                                                                     end) p)) (at level 0).

Notation "'RdMem' ( s , p )" := (readTreeMem s (getMemPathTree ltac:(match type of s with
                                                                     | TreeState _ ?t => exact t
                                                                     end) p)) (at level 0).

Notation "'RdSend' ( s , p )" := (readTreeSend s (getSendPathTree ltac:(match type of s with
                                                                         | TreeState _ ?t => exact t
                                                                         end) p)) (at level 0).

Notation "'RdRecv' ( s , p )" := (readTreeRecv s (getRecvPathTree ltac:(match type of s with
                                                                         | TreeState _ ?t => exact t
                                                                         end) p)) (at level 0).

Notation "'RdRegExplicit' ( s , t , p )" := (readTreeReg s (getRegPathTree t p)) (at level 0).
Notation "'RdMemExplicit' ( s , t , p )" := (readTreeMem s (getMemPathTree t p)) (at level 0).
Notation "'RdSendExplicit' ( s , t , p )" := (readTreeSend s (getSendPathTree t p)) (at level 0).
Notation "'RdRecvExplicit' ( s , t , p )" := (readTreeRecv s (getRecvPathTree t p)) (at level 0).


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
Notation Retv := (Return (ConstTDefK (Bit 0))).

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

Notation "'RegRead' letv <- name 'in' t ; cont" :=
  (ReadReg (Stringify letv) (getRegPathTree t name) (fun letv => cont)) (at level 20, letv name): guru_scope.

Notation "'RegWrite' name 'in' t <- v ; cont" :=
  (WriteReg (getRegPathTree t name) v cont) (at level 20): guru_scope.

Notation "'MemReadRq' name 'in' t ! p <- i ; cont" :=
  (ReadRqMem (getMemPathTree t name) i (@Build_FinType (getMemFromPath (getMemPathTree t name)).(memoryPort) p I) cont) (at level 20): guru_scope.

Notation "'MemReadRp' letv <- name 'in' t ! p ; cont" :=
  (ReadRpMem (Stringify letv) (getMemPathTree t name) (@Build_FinType (getMemFromPath (getMemPathTree t name)).(memoryPort) p I) (fun letv => cont)) (at level 20, letv name): guru_scope.

Notation "'MemWrite' name 'in' t ! i <- v ; cont" :=
  (WriteMem (getMemPathTree t name) i v cont) (at level 20): guru_scope.

Notation "'Put' name 'in' t <- v ; cont" :=
  (Send (getSendPathTree t name) v cont) (at level 20): guru_scope.

Notation "'Get' letv <- name 'in' t ; cont" :=
  (Recv (Stringify letv) (getRecvPathTree t name) (fun letv => cont)) (at level 20, letv name): guru_scope.




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
  (IfElse (Stringify letv) p (k' := k') t (Return ConstTDef) (fun letv => cont))
    (at level 20, t at level 0, letv name): guru_scope.

Notation "'LetIf' letv <- 'If' p 'Then' t ; cont" :=
  (IfElse (Stringify letv) p t (Return ConstTDef) (fun letv => cont))
    (at level 20, t at level 0, letv name): guru_scope.

Notation "'If' p 'Then' t 'Else' f ; cont" :=
  (IfElse ""%string p t f (fun _ => cont)) (at level 20, t at level 0, f at level 0): guru_scope.

Notation "'If' p 'Then' t ; cont" :=
  (IfElse ""%string p t (Return ConstTDef) (fun _ => cont)) (at level 20, t at level 0): guru_scope.

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

Notation "'IfE' p 'ThenE' t 'ElseE' f ; cont" :=
  (IfElseE ""%string p (k' := Bit 0) t f (fun _ => cont)) (at level 20, t at level 0, f at level 0): guru_scope.

Notation "'IfE' p 'ThenE' t ; cont" :=
  (IfElseE ""%string p (k' := Bit 0) t (RetE ConstDef) (fun _ => cont)) (at level 20, t at level 0): guru_scope.

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
