From Stdlib Require Import String List ZArith Zmod.
Require Import Guru.Library Guru.Syntax Guru.Semantics Guru.Notations Guru.Theorems Guru.Ltacs.

Set Implicit Arguments.
Unset Strict Implicit.
Set Asymmetric Patterns.

Import ListNotations.

Section Fifo.
  Local Open Scope string.

  Variable T: Kind.
  Variable LgCapacity: Z.

  Definition fifoRegs :=
    [ ("deqPtr", Build_Reg (Bit LgCapacity) (Default _));
      ("size", Build_Reg (Bit (LgCapacity + 1)) (Default _));
      ("elements", Build_Reg (Array (Z.to_nat (Z.shiftl 1 LgCapacity)) T) (Default _))].

  Definition fifoSends :=
    [ ("enqDone", Bool);
      ("deqVal", Option T) ].

  Definition fifoRecvs :=
    [ ("enqVal", Option T);
      ("deqEn", Bool) ].

  Definition fifoDecl := {|modRegs := fifoRegs;
                           modMems := [];
                           modRegUs := [];
                           modMemUs := [];
                           modSends := fifoSends;
                           modRecvs := fifoRecvs|}.

    Definition fifoMl := getModLists fifoDecl.

    Local Open Scope guru_scope.
    Definition fifoDeq ty: Action ty fifoMl (Bit 0) :=
      ( RegRead deqPtr <- "deqPtr" in fifoMl;
        RegRead size <- "size" in fifoMl;
        RegRead elements <- "elements" in fifoMl;
        Get deqEn <- "deqEn" in fifoMl;
        Let isDeq <- And [#deqEn; isNotZero #size];
        RegWrite "size" in fifoMl <- Sub #size (ITE #isDeq $1 $0);
        RegWrite "deqPtr" in fifoMl <- Add [TruncLsb 1 _ #size; ITE #isDeq $1 $0];
        Put "deqVal" in fifoMl <- STRUCT { "data" ::= #elements@[#deqPtr];
                                           "valid" ::= #isDeq };
        Retv ).

    Definition fifoEnq ty: Action ty fifoMl (Bit 0) :=
      ( RegRead deqPtr <- "deqPtr" in fifoMl;
        RegRead size <- "size" in fifoMl;
        RegRead elements <- "elements" in fifoMl;
        Get enqVal <- "enqVal" in fifoMl;
        Let isEnq <- And [#enqVal`"valid"; isZero (TruncMsb 1 _ #size)];
        RegWrite "elements" in fifoMl <- ITE #isEnq
                                           (#elements@[ Add [#deqPtr; TruncLsb 1 _ #size] <- #enqVal`"data"])
                                           #elements;
        RegWrite "size" in fifoMl <- Add [#size; ITE #isEnq $1 $0];
        Put "enqDone" in fifoMl <- #isEnq;
        Retv ).

    Definition fifo: Mod := {|modDecl := fifoDecl;
                              modActions ty := [ fifoDeq ty; fifoEnq ty; Retv ] |}.
End Fifo.
