From Stdlib Require Import String List ZArith Zmod.
From Guru Require Import Library Syntax Semantics Notations Theorems Ltacs Compiler Extraction.

Set Implicit Arguments.
Unset Strict Implicit.
Set Asymmetric Patterns.

Import ListNotations.

Section Fifo.
  Local Open Scope string.

  Variable T: Kind.
  Variable LgCapacity: Z.

  Definition fifoTree : Tree ModElem :=
    Node ""
      [ Leaf "deqPtr" (ERegister (Build_Register (Bit LgCapacity) (Some (Default _))));
        Leaf "size" (ERegister (Build_Register (Bit (LgCapacity + 1)) (Some (Default _))));
        Leaf "elements" (ERegister (Build_Register (Array (Z.to_nat (Z.shiftl 1 LgCapacity)) T) (Some (Default _))));
        Leaf "enqDone" (ESend Bool);
        Leaf "deqVal" (ESend (Option T));
        Leaf "enqVal" (ERecv (Option T));
        Leaf "deqEn" (ERecv Bool) ].

  Local Open Scope guru_scope.

  Definition fifoDeq ty: ActionTree ty fifoTree (Bit 0) :=
    ( RegRead deqPtr <- ".deqPtr" in fifoTree;
      RegRead sz <- ".size" in fifoTree;
      RegRead elements <- ".elements" in fifoTree;
      Get deqEn <- ".deqEn" in fifoTree;
      Let isDeq <- And [#deqEn; isNotZero #sz];
      RegWrite ".size" in fifoTree <- Sub #sz (ITE #isDeq $1 $0);
      RegWrite ".deqPtr" in fifoTree <- Add [TruncLsb 1 _ #sz; ITE #isDeq $1 $0];
      Put ".deqVal" in fifoTree <- STRUCT { "data" ::= #elements@[#deqPtr];
                                                 "valid" ::= #isDeq };
      Retv ).

  Definition fifoEnq ty: ActionTree ty fifoTree (Bit 0) :=
    ( RegRead deqPtr <- ".deqPtr" in fifoTree;
      RegRead sz <- ".size" in fifoTree;
      RegRead elements <- ".elements" in fifoTree;
      Get enqVal <- ".enqVal" in fifoTree;
      Let isEnq <- And [#enqVal`"valid"; isZero (TruncMsb 1 _ #sz)];
      RegWrite ".elements" in fifoTree <- ITE #isEnq
                                 (#elements@[ Add [#deqPtr; TruncLsb 1 _ #sz] <- #enqVal`"data"])
                                 #elements;
      RegWrite ".size" in fifoTree <- Add [#sz; ITE #isEnq $1 $0];
      Put ".enqDone" in fifoTree <- #isEnq;
      Retv ).

  Definition fifo: ModTree fifoTree :=
    fun ty => [ fifoDeq ty; fifoEnq ty; Retv ].
End Fifo.

Section FifoCompile.
  (* 4-entry Bool FIFO: LgCapacity=2, so capacity = 2^2 = 4 *)
  Local Definition compiledMod := compileTree (fifo Bool 2).
End FifoCompile.

Set Extraction Output Directory "./Example/Fifo".
Extraction "Compile" size compiledMod.
