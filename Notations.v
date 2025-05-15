Require Import String List.
Require Import Guru.Lib.Library Guru.Lib.Word.
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
  (Struct (cons x1%gurustruct .. (cons xn%gurustruct nil) ..)) (only parsing): guru_scope.

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
Notation "s `{ name <- v }" := (UpdateStruct s (getFinStruct name%string (structList s)) v).

Notation "'ARRAY_CONST' [ v1 ; .. ; vn ]" :=
  (pair v1 .. (pair vn tt) ..): guru_scope.

Notation "'ARRAY' [ v1 ; .. ; vn ]" :=
  (BuildArray
     (arrayToFunc
        ((pair v1 .. (pair vn tt) ..):
          SameTuple (Expr _ _) (length (cons v1 .. (cons vn nil) ..))))): guru_scope.

Notation "v #[ i ]" := (ReadArray v i): guru_scope.
Notation "v @[ i ]" := (ReadArrayConst v i): guru_scope.
Definition arraySize [ty k n] (e: Expr ty (Array n k)) := n.
Notation "v $[ i ]" := (ReadArrayConst v (@FinArray_of_nat_ltDec i (arraySize v) eq_refl)): guru_scope.

Notation "v #[ i <- e ]" := (UpdateArray v i e): guru_scope.
Notation "v @[ i <- e ]" := (UpdateArrayConst v i e): guru_scope.
Notation "v $[ i <- e ]" := (UpdateArrayConst v (@FinArray_of_nat_ltDec i (arraySize v) eq_refl) e): guru_scope.

Notation "# x" := (Var _ _ x) (no associativity, at level 0, x name): guru_scope.

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

Notation "'RegRead' ( letname , letv ) <- name 'in' m ; cont" :=
  (ReadReg letname%string (getFinStruct name%string (mregs m)) (fun letv => cont)) (at level 20): guru_scope.

Notation "'RegWrite' name 'in' m <- v ; cont" :=
  (WriteReg (getFinStruct name%string (mregs m)) v cont) (at level 20): guru_scope.

Notation "'MemReadRq' name 'in' m ! p <- i ; cont" :=
  (ReadRqMem (getFinStruct name%string (mmems m)) i
     (@FinArray_of_nat_ltDec p (memUPort (fieldK (getFinStruct name%string (mmems m)))) eq_refl) cont)
    (at level 20): guru_scope.

Notation "'MemReadRp' ( letname , letv ) <-  name 'in' m ! p ; cont" :=
  (ReadRpMem letname%string (getFinStruct name%string (mmems m))
     (@FinArray_of_nat_ltDec p (memUPort (fieldK (getFinStruct name%string (mmems m)))) eq_refl) (fun letv => cont))
    (at level 20): guru_scope.

Notation "'MemWrite' name 'in' m ! i <- v ; cont" :=
  (WriteMem (getFinStruct name%string (mmems m)) i v cont) (at level 20): guru_scope.

Notation "'RegReadU' ( letname , letv ) <- name 'in' m ; cont" :=
  (ReadRegU letname%string (getFinStruct name%string (mregUs m)) (fun letv => cont)) (at level 20): guru_scope.

Notation "'RegWriteU' name 'in' m <- v ; cont" :=
  (WriteRegU (getFinStruct name%string (mregUs m)) v cont) (at level 20): guru_scope.

Notation "'MemReadRqU' name 'in' m ! p <- i ; cont" :=
  (ReadRqMemU (getFinStruct name%string (mmemUs m)) i
     (@FinArray_of_nat_ltDec p (memUPort (fieldK (getFinStruct name%string (mmemUs m)))) eq_refl) cont)
    (at level 20): guru_scope.

Notation "'MemReadRpU' ( letname , letv ) <-  name 'in' m ! p ; cont" :=
  (ReadRpMemU letname%string (getFinStruct name%string (mmemUs m))
     (@FinArray_of_nat_ltDec p (memUPort (fieldK (getFinStruct name%string (mmemUs m)))) eq_refl) (fun letv => cont))
    (at level 20): guru_scope.

Notation "'MemWriteU' name 'in' m ! i <- v ; cont" :=
  (WriteMemU (getFinStruct name%string (mmemUs m)) i v cont) (at level 20): guru_scope.

Notation "'Put' name 'in' m <- v ; cont" :=
  (Send (getFinStruct name%string (msends m)) v cont) (at level 20): guru_scope.

Notation "'Get' ( letname , letv ) <- name 'in' m ; cont" :=
  (Recv letname%string (getFinStruct name%string (mrecvs m)) (fun letv => cont)) (at level 20): guru_scope.

Notation "'Let' ( letname , letv ) : k' <- e ; cont" :=
  (LetExpr letname%string (k' := k') e (fun letv => cont)) (at level 20): guru_scope.

Notation "'Let' ( letname , letv ) <- e ; cont" :=
  (LetExpr letname%string e (fun letv => cont)) (at level 20): guru_scope.

Notation "'LetA' ( letname , letv ) : k' <- a ; cont" :=
  (LetAction letname%string (k' := k') a (fun letv => cont)) (at level 20, a at level 0): guru_scope.

Notation "'LetA' ( letname , letv ) <- a ; cont" :=
  (LetAction letname%string a (fun letv => cont)) (at level 20, a at level 0): guru_scope.

Notation "'Act' a ; cont" :=
  (LetAction ""%string a (fun _ => cont)) (at level 20, a at level 0): guru_scope.

Notation "'Random' ( letname , letv ) : k' ; cont" :=
  (NonDet letname%string k' (fun letv => cont)) (at level 20): guru_scope.

Notation "'LetIf' ( letname , letv ) : k' <- 'If' p 'Then' t 'Else' f ; cont" :=
  (IfElse letname%string p (k' := k') t f (fun letv => cont)) (at level 20, t at level 0, f at level 0): guru_scope.

Notation "'LetIf' ( letname , letv ) <- 'If' p 'Then' t 'Else' f ; cont" :=
  (IfElse letname%string p t f (fun letv => cont)) (at level 20, t at level 0, f at level 0): guru_scope.

Notation "'LetIf' ( letname , letv ) : k' <- 'If' p 'Then' t ; cont" :=
  (IfElse letname%string p (k' := k') t (Return (ConstDefK k')) (fun letv => cont))
    (at level 20, t at level 0): guru_scope.

Notation "'LetIf' ( letname , letv ) <- 'If' p 'Then' t ; cont" :=
  (IfElse letname%string p t (Return ConstDef) (fun letv => cont)) (at level 20, t at level 0): guru_scope.

Notation "'If' p 'Then' t 'Else' f ; cont" :=
  (IfElse ""%string p t f (fun _ => cont)) (at level 20, t at level 0, f at level 0): guru_scope.

Notation "'If' p 'Then' t ; cont" :=
  (IfElse ""%string p t (Return ConstDef) (fun _ => cont)) (at level 20, t at level 0): guru_scope.

Notation "'Sys' ls ; cont" :=
  (System ls cont) (at level 20): guru_scope.

Notation "'SysE' ls ; cont" :=
  (SystemE ls cont) (at level 20): guru_scope.

Notation "'LetE' ( letname , letv ) : k' <- le ; cont" :=
  (LetEx letname%string (k' := k') le (fun letv => cont)) (at level 20): guru_scope.

Notation "'LetE' ( letname , letv ) <- le ; cont" :=
  (LetEx letname%string le (fun letv => cont)) (at level 20): guru_scope.

Notation "'LetIfE' ( letname , letv ) : k' <- 'IfE' p 'ThenE' t 'ElseE' f ; cont" :=
  (IfElseE letname%string p (k' := k') t f (fun letv => cont)) (at level 20, t at level 0, f at level 0): guru_scope.

Notation "'LetIfE' ( letname , letv ) <- 'IfE' p 'ThenE' t 'ElseE' f ; cont" :=
  (IfElseE letname%string p t f (fun letv => cont)) (at level 20, t at level 0, f at level 0): guru_scope.

Notation "'LetL' ( letname , letv  ) : k <- le ; cont" :=
  (LetAction letname%string (k := k) (toAction le) (fun letv => cont)) (at level 20, le at level 0): guru_scope.
 
Notation "'LetL' ( letname , letv  ) <- le ; cont" :=
  (LetAction letname%string (toAction le) (fun letv => cont)) (at level 20, le at level 0): guru_scope.

Section Structs.
  Local Open Scope guru_scope.
  Definition Option k := STRUCT_TYPE {
                             "valid" :: Bool ;
                             "data"  :: k }.

  Definition RegsStruct (decl: ModDecl) :=
    STRUCT_TYPE {
        "regs"  :: Struct (map (fun x => (fst x, regKind (snd x))) (modRegs decl));
        "regUs" :: Struct (modRegUs decl) }.

  Definition MemRqsStruct (decl: ModDecl) :=
    STRUCT_TYPE {
        "rqs" :: Struct (map (fun x => (fst x, Array (memPort (snd x))
                                                 (Option (Bit (Nat.log2_up (memSize (snd x))))))) (modMems decl));
        "rqUs" :: Struct (map (fun x => (fst x, Array (memUPort (snd x))
                                                  (Option (Bit (Nat.log2_up (memUSize (snd x))))))) (modMemUs decl))
      }.

  Definition MemRpsStruct (decl: ModDecl) :=
    STRUCT_TYPE {
        "rps" :: Struct (map (fun x => (fst x, Array (memPort (snd x)) (memKind (snd x)))) (modMems decl));
        "rpUs" :: Struct (map (fun x => (fst x, Array (memUPort (snd x)) (memUKind (snd x)))) (modMemUs decl)) }.

  Definition MWrite sz k := Option (STRUCT_TYPE {
                                        "idx" :: Bit (Nat.log2_up sz);
                                        "val" :: k }).

  Definition MemWrsStruct (decl: ModDecl) :=
    STRUCT_TYPE {
        "wrs" :: Struct (map (fun x => (fst x, MWrite (memSize (snd x)) (memKind (snd x)))) (modMems decl));
        "wrUs" :: Struct (map (fun x => (fst x, MWrite (memUSize (snd x)) (memUKind (snd x)))) (modMemUs decl)) }.

  Definition SendsStruct (decl: ModDecl) := Struct (map (fun x => (fst x, Option (snd x))) (modSends decl)).
  Definition RecvsStruct (decl: ModDecl) := Struct (modRecvs decl).

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

Section T.
  Local Open Scope guru_scope.
  Let S1 := STRUCT_TYPE { "test" :: Bool ;
                          "only" :: Bit 1 }.

  Let S2 := STRUCT_TYPE { "a" :: S1;
                          "b" :: Array 5 Bool }.

  Let c1: type S1 := STRUCT_CONST { "test" ::= true ;
                                    "only" ::= wzero 1 }.

  Let c2: type S2 := STRUCT_CONST { "a" ::= c1 ;
                                    "b" ::= Default (Array 5 Bool) }.

  Let A1 := Array 2 Bool.
  Let c3: type A1 := ARRAY_CONST [ true ; false ].

  Section Ty.
    Variable ty: Kind -> Type.
    Let s1: Expr ty S1 := STRUCT { "test" ::= And [Const ty Bool true; Const ty Bool false] ;
                                   "only" ::= Const ty (Bit 1) (wzero 1) }.
    
    Let s2: Expr ty S2 := STRUCT { "a" ::= s1 ;
                                   "b" ::= Const ty _ (Default (Array 5 Bool)) }.

    Let s3: Expr ty S2 := STRUCT { "a" ::= (STRUCT {
                                                "test" ::= And [Const ty Bool true; Const ty Bool false] ;
                                                "only" ::= Const ty (Bit 1) (wzero 1)
                                           }) ;
                                   "b" ::= Const ty _ (Default (Array 5 Bool)) }.

    Let field: Expr ty Bool := (s3`"a"`"test").

    Let s4: Expr ty S1 := s1`{ "test" <- Const ty Bool false }.

    Let a1: Expr ty A1 := ARRAY [ (Const ty Bool true) ; (Const ty Bool false) ].

    Let elem := a1 #[ Const ty (Bit 1) (WO~1)].

    Let elem1 := a1 @[ inl tt ].
    Let elem2 := a1 $[ 0 ].

    Let a2 := a1 #[ Const ty (Bit 1) (WO~1) <- Const ty Bool false ].
    Let a3 := a1 @[ inl tt <- Const ty Bool false ].
    Let a4 := a1 $[ 0 <- Const ty Bool false ].
  End Ty.

  Local Open Scope string.
  Let decl := {|modRegs := [("r", Build_Reg Bool true) ];
                modMems := [("m", Build_Mem 3 Bool 5 None)];
                modRegUs := [("ru", Bool) ];
                modMemUs := [("mu", Build_MemU 6 Bool 3)];
                modSends := [("p", Bool)];
                modRecvs := [("g", Bool)]|}.

  Let ml := getModLists decl.

  Let act ty : Action ty ml Bool :=
        ( RegRead ("tr", tr) <- "r" in ml;
          RegWrite "r" in ml <- ConstBool true;
          MemReadRq "m" in ml !1 <- ConstDef;
          MemReadRp ("tm", tm) <- "m" in ml !4;
          MemWrite "m" in ml ! ConstBit (wones _) <- #tm;
          RegReadU ("tru", tru) <- "ru" in ml;
          RegWriteU "ru" in ml <- Not #tru;
          MemReadRqU "mu" in ml !1 <- Add [ConstBit (ZToWord _ 4); ConstBit Ox"f"; ConstBit 3'h"e";
                                           ConstBit 3'b"10"; ConstBit Ob"01"];
          MemReadRpU ("tmu", tmu) <- "mu" in ml !0;
          MemWriteU "mu" in ml ! ConstBit (ZToWord _ 3) <- #tmu;
          Put "p" in ml <- ConstDefK Bool;
          Get ("tg", tg) <- "g" in ml;
          Let ("tv", tv): Bool <- #tg;
          Let ("tv2", tv2) <- And [#tv; #tg];
          LetA ("tv3", tv3) : Bit 4 <- ( Let ("tv4", tv4): Bit 4 <- ZeroExtend 2 (Concat (ToBit #tv) (ToBit #tg));
                                         Return #tv4);
          LetA ("tv6", tv6) <- ( Let ("tv5", tv5) <- (Concat (ToBit #tv) (ToBit #tg));
                                 Return #tv5);
          Random ("tv7", tv7) : Bit 6;

          LetL ("test", test): Bool <- ( SysE [];
                                         LetE ("l1", l1) <- RetE #tr;
                                         LetE ("l2", l2) : Bool <- RetE (Not #l1);
                                         LetIfE ("l3", l3): Bool <- IfE #l1 ThenE (RetE #l2) ElseE (RetE (Not #l2)) ;
                                         LetIfE ("l4", l4) <- IfE #l2 ThenE (RetE #l1) ElseE (RetE (Not #l1));
                                         RetE #l4);

          LetL ("tes1", tes1) <- ( SysE [];
                                   LetE ("l1", l1) <- RetE #tr;
                                   LetE ("l2", l2) : Bool <- RetE (Not #l1);
                                   LetIfE ("l3", l3): Bool <- IfE #l1 ThenE (RetE #l2) ElseE (RetE (Not #l2)) ;
                                   LetIfE ("l4", l4) <- IfE #l2 ThenE (RetE #l1) ElseE (RetE (Not #l1));
                                   RetE #l4);

          LetIf ("foo1", foo1): Bit 1 <-
                                  If #tg Then (
                                    LetIf ("bar1", bar1) : Bool <-
                                      If #tv Then (
                                        Return (Not #tg)
                                      ) Else (
                                        Return ConstDef
                                      );
                                    Return (ToBit #tr)
                                  ) Else (
                                    If (FromBit Bool (TruncLsb 5 1 #tv7)) Then (
                                        Sys [];
                                        Return (ConstDefK (Bit 4))
                                      );
                                    Return (ToBit #tm) ) ;
          LetIf ("foo2", foo2) <-
            If #tg Then (
              Return #tr
            ) Else (
              Return #tm ) ;
          LetIf ("foo3", foo3): Bool <-
                                  If #tg Then (
                                    Return #tr ) ;
          LetIf ("foo4", foo4) <-
            If #tg Then (
              Return #tr ) ;
          If #tg Then (
              Return #tr
            ) Else (
              Return (Not #tr)) ;
          If #tg Then (
              Return #tr );
          Sys [];
          Return (And [#tr;
                       #tm;
                       #tg]) ).

  Let listIntentationNotBroken := [ 5;
                                    6 ; 8 ;
                                    9].

  Let listIntentationNotBroken2 := [
      5;
      6 ; 8 ;
      9].

  Let m: Mod := {|modDecl := decl;
                  modActions := fun ty => [ Act (act ty); Return ConstDef ] |}.
End T.
