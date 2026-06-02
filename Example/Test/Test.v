From Stdlib Require Import String List ZArith Zmod Hexadecimal.
From Guru Require Import Library Syntax Notations Compiler Extraction.

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

  Definition testTree : Tree ModStateElem :=
    Node ""
      [ Leaf "r" (ERegister (Build_Register Bool (Some true)));
        Leaf "m" (EMemory (Build_Memory 3 Bool 5 (Some (Some (@Build_SameTuple _ 3 [true; true; false] I)))));
        Leaf "ru" (ERegister (Build_Register Bool (Some (Default Bool))));
        Leaf "mu" (EMemory (Build_Memory 6 Bool 3 None));
        Leaf "p" (ESend Bool);
        Leaf "g" (ERecv Bool) ].

  Local Set Printing Depth 1000.
  Let act ty: ActionTree ty testTree Bool := structSimplCbn
        ( RegRead tr <- "r" in testTree;
          RegWrite "r" in testTree <- ConstBool true;
          MemReadRq "m" in testTree !1 <- ConstDef;
          MemReadRp tm <- "m" in testTree !4;
          MemWrite "m" in testTree ! ConstBit (Zmod.of_Z _ (-1)) <- #tm;
          RegRead tru <- "ru" in testTree;
          RegWrite "ru" in testTree <- Not #tru;
          MemReadRq "mu" in testTree !1 <- Add [ConstBit (Zmod.of_Z _ 4); ConstBit (Zmod.of_Z _ 0xf);
                                           ConstBit (Zmod.of_Z _ 0xe);
                                           ConstBit (Zmod.of_Z _ 2); ConstBit (Zmod.of_Z _ 1)];
          MemReadRp tmu <- "mu" in testTree !0;
          MemWrite "mu" in testTree ! ConstBit (Zmod.of_Z _ 3) <- #tmu;
          Put "p" in testTree <- ConstDefK Bool;
          Get tg <- "g" in testTree;
          Random tv7: Bit 6 ;
          Let structVal: STRUCT_TYPE {"a" :: Bool ; "b" :: Bit 2} <- STRUCT { "a" ::= Const ty Bool false;
                                                                              "b" ::= Const ty (Bit _)
                                                                                        (bits.of_Z 2 1) };
          Let updStruct1 <- #structVal`{ "b" <- Const ty (Bit _) (bits.of_Z 2 2) };
          Let updStruct2 <- ##updStruct1`{ "a" <- Const ty Bool true };
          Let tv: Bool <- ITE0 #tg #tr;
          Let tv2 <- And [#tv; #tg];
          Let var : Bit 4 <- $4;
          Let var2 : Bit 2 <- #var`[1:0];
          LetA tv3 : Bit 4 <- ( Let tv4: Bit 4 <- ZeroExtend 2 (Concat (ToBit #tv) (ToBit #tg));
                                ReturnTree #tv4);
          LetA tv6 <- ( Let tv5 <- (Concat (ToBit #tv) (ToBit #tg));
                        ReturnTree #tv5);
          
          Let structVal : S1 <- s1 ty;
          Let newTr <- #structVal`"test";
          
          LetIf foo1: Bit 1 <-
                        If #tg Then (
                          LetIf bar1 : Bool <-
                                         If #tv Then (
                                           ReturnTree (Not #tg)
                                         ) Else (
                                           ReturnTree ConstDef
                                         );
                          ReturnTree (ToBit #tr)
                        ) Else (
                          If (FromBit Bool (TruncLsb 5 1 #tv7)) Then (
                              Sys [];
                              ReturnTree (ConstDefK (Bit 4))
                            );
                          ReturnTree (ToBit #tm) ) ;
          LetIf foo2 <-
            If #tg Then (
              ReturnTree #tr
            ) Else (
              ReturnTree #tm ) ;
          LetIf foo3: Bool <-
                        If #tg Then (
                          ReturnTree #tr ) ;
          LetIf foo4 <-
            If #tg Then (
              ReturnTree #tr ) ;
          If #tg Then (
              ReturnTree #tr
            ) Else (
              ReturnTree (Not #tr)) ;
          If #tg Then (
              ReturnTree #tr );
          Sys [];
          ReturnTree (And [#tr;
                           #tm;
                           #tg]) ).

  Let m: ModTree testTree :=
    fun ty => [ Act (act ty); ReturnTree ConstDef ].

  Local Definition compiledMod := compileTree m.  
End T.

Set Extraction Output Directory "./Example/Test".
Extraction "Compile" size compiledMod.
