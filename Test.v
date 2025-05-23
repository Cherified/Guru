From Stdlib Require Import String List PeanoNat.
Require Import Guru.Lib.Library Guru.Lib.Word.
Require Import Guru.Syntax Guru.Notations Guru.Compiler Guru.Extraction.

Set Implicit Arguments.
Unset Strict Implicit.
Set Asymmetric Patterns.

Import ListNotations.

Unset Printing Implicit Defensive.


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
    Local Definition s1: Expr ty S1 := STRUCT { "test" ::= And [Const ty Bool true; Const ty Bool false] ;
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
          
          Let structVal : S1 <- s1 ty;
          Let newTr <- #structVal`"test";
          
          LetL tes1 <- ( SysE [];
                         LetE l1 <- #newTr;
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

  Local Definition compiledMod := compile m.
  
End T.

Extraction "Compile"
  genFinStruct
  genFinArray
  compiledMod.
