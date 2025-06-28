From Stdlib Require Import String List ZArith Zmod Hexadecimal.
Require Import Guru.Library Guru.Syntax Guru.Notations Guru.Compiler Guru.Extraction.

Set Implicit Arguments.
Unset Strict Implicit.
Set Asymmetric Patterns.

Import ListNotations.

Unset Printing Implicit Defensive.

Section T.
  Local Open Scope guru_scope.
  Let S1 := STRUCT_TYPE { "test" :: Bool ;
                          "only" :: Bit 1 }.

  Let S2 := STRUCT_TYPE { "a" :: S1;
                          "b" :: Array 5 Bool }.

  Let c1: type S1 := STRUCT_CONST { "test" ::= true ;
                                    "only" ::= Zmod.zero }.

  Let c2: type S2 := STRUCT_CONST { "a" ::= c1 ;
                                    "b" ::= Default (Array 5 Bool) }.

  Let A1 := Array 2 Bool.
  Let c3: type A1 := ARRAY_CONST [ true ; false ].

  Section Ty.
    Variable ty: Kind -> Type.
    Variable test : nat.
    Local Definition s1: Expr ty S1 := STRUCT { "test" ::= And [Const ty Bool true; Const ty Bool false] ;
                                                "only" ::= Const ty (Bit 1) Zmod.zero }.
    
    Let s2: Expr ty S2 := STRUCT { "a" ::= s1 ;
                                   "b" ::= Const ty _ (Default (Array 5 Bool)) }.

    Let s3: Expr ty S2 := STRUCT { "a" ::= (STRUCT {
                                                "test" ::= And [Const ty Bool true; Const ty Bool false] ;
                                                "only" ::= Const ty (Bit 1) Zmod.zero
                                           }) ;
                                   "b" ::= Const ty _ (Default (Array 5 Bool)) }.

    Let field: Expr ty (Bit 1) := (s3`"a"`"only").

    Let s4: Expr ty S1 := s1`{ "only" <- Const ty (Bit 1) Zmod.zero }.

    Let a1: Expr ty A1 := ARRAY [ (Const ty Bool true) ; (Const ty Bool false) ].

    Let elem := a1 @[ Const ty (Bit 1) Zmod.one].

    Let elem2 := a1 $[ 0 ].

    Let a2 := a1 @[ Const ty (Bit 1) Zmod.one <- Const ty Bool false ].
    Let a4 := a1 $[ 0 <- Const ty Bool false ].
  End Ty.

  Local Open Scope string.
  Let decl := {|modRegs := [("r", Build_Reg Bool true) ];
                modMems := [("m", @Build_Mem 3 Bool 5 None)];
                modRegUs := [("ru", Bool) ];
                modMemUs := [("mu", Build_MemU 6 Bool 3)];
                modSends := [("p", Bool)];
                modRecvs := [("g", Bool)]|}.

  Let ml := getModLists decl.

  Local Set Printing Depth 1000.
  Let act ty: Action ty ml Bool := structSimplCbn
        ( RegRead tr <- "r" in ml;
          RegWrite "r" in ml <- ConstBool true;
          MemReadRq "m" in ml !1 <- ConstDef;
          MemReadRp tm <- "m" in ml !4;
          MemWrite "m" in ml ! ConstBit (Zmod.of_Z _ (-1)) <- #tm;
          RegReadU tru <- "ru" in ml;
          RegWriteU "ru" in ml <- Not #tru;
          MemReadRqU "mu" in ml !1 <- Add [ConstBit (Zmod.of_Z _ 4); ConstBit (Zmod.of_Z _ 0xf);
                                           ConstBit (Zmod.of_Z _ 0xe);
                                           ConstBit (Zmod.of_Z _ 2); ConstBit (Zmod.of_Z _ 1)];
          MemReadRpU tmu <- "mu" in ml !0;
          MemWriteU "mu" in ml ! ConstBit (Zmod.of_Z _ 3) <- #tmu;
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
  size compiledMod.
