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

Section Structs.
  Local Open Scope guru_scope.
  Definition Option k := STRUCT_TYPE {
                             "valid" :: Bool ;
                             "data"  :: k }.

  Definition Pair k1 k2 := STRUCT_TYPE {
                               "fst" :: k1 ;
                               "snd" :: k2 }.

  Section Ty.
    Variable ty: Kind -> Type.
    Definition mkSome k (e: Expr ty k): Expr ty (Option k) := STRUCT { "valid" ::= ConstT Bool true ;
                                                                       "data"  ::= e }.
    Definition mkNone k: Expr ty (Option k) := STRUCT { "valid" ::= ConstT Bool false ;
                                                        "data"  ::= ConstTDefK k }.
    Definition mkPair ty k1 (e1: Expr ty k1) k2 (e2: Expr ty k2) := STRUCT { "fst" ::= e1 ;
                                                                             "snd" ::= e2 }.
  End Ty.

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

    Let elem := a1 @[ Const ty (Bit 1) (WO~1)].

    Let elem2 := a1 $[ 0 ].

    Let a2 := a1 @[ Const ty (Bit 1) (WO~1) <- Const ty Bool false ].
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
        ( RegRead tr <- "r" in ml;
          RegWrite "r" in ml <- ConstBool true;
          MemReadRq "m" in ml !1 <- ConstDef;
          MemReadRp tm <- "m" in ml !4;
          MemWrite "m" in ml ! ConstBit (wones _) <- #tm;
          RegReadU tru <- "ru" in ml;
          RegWriteU "ru" in ml <- Not #tru;
          MemReadRqU "mu" in ml !1 <- Add [ConstBit (ZToWord _ 4); ConstBit Ox"f"; ConstBit 3'h"e";
                                           ConstBit 3'b"10"; ConstBit Ob"01"];
          MemReadRpU tmu <- "mu" in ml !0;
          MemWriteU "mu" in ml ! ConstBit (ZToWord _ 3) <- #tmu;
          Put "p" in ml <- ConstDefK Bool;
          Get tg <- "g" in ml;
          Random tv7: Bit 6 ;
          Let tv: Bool <- ITE0 #tg #tr;
          Let tv2 <- And [#tv; #tg];
          Let var : Bit 4 <- $4;
          Let var2 : Bit 2 <- #var`[1:0];
          LetA tv3 : Bit 4 <- ( Let tv4: Bit 4 <- ZeroExtend 2 (Concat (ToBit #tv) (ToBit #tg));
                                Return #tv4);
          LetA tv6 <- ( Let tv5 <- (Concat (ToBit #tv) (ToBit #tg));
                        Return #tv5);

          LetL test: Bool <- ( SysE [];
                               LetE l1 <- #tr;
                               LetE l2 : Bool <- Not #l1;
                               LETE l22 : Bool <- (RetE #l2);
                               LetIfE l3: Bool <- IfE #l1 ThenE (RetE #l2) ElseE (RetE (Not #l2)) ;
                               LetIfE l4 <- IfE #l2 ThenE (RetE #l1) ElseE (RetE (Not #l1));
                               RetE #l4);
          
          LetL tes1 <- ( SysE [];
                         LetE l1 <- #tr;
                         LetE l2 : Bool <- Not #l1;
                         LetIfE l3: Bool <- IfE #l1 ThenE (RetE #l2) ElseE (RetE (Not #l2)) ;
                         LetIfE l4 <- IfE #l2 ThenE (RetE #l1) ElseE (RetE (Not #l1));
                         RetE #l4);

          LetIf foo1: Bit 1 <-
                        If #tg Then (
                          LetIf bar1 : Bool <-
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
          LetIf foo2 <-
            If #tg Then (
              Return #tr
            ) Else (
              Return #tm ) ;
          LetIf foo3: Bool <-
                        If #tg Then (
                          Return #tr ) ;
          LetIf foo4 <-
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
