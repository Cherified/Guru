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

  Definition fifoTree : Tree Elem :=
    Node ""
      [ Leaf "deqPtr" (EReg (Build_Reg (Bit LgCapacity) (Some (getDefault _))));
        Leaf "size" (EReg (Build_Reg (Bit (LgCapacity + 1)) (Some (getDefault _))));
        Leaf "elements" (EReg (Build_Reg (Array (Z.to_nat (Z.shiftl 1 LgCapacity)) T) (Some (getDefault _))));
        Leaf "enqDone" (ESend Bool);
        Leaf "deqVal" (ESend (Option T));
        Leaf "enqVal" (ERecv (Option T));
        Leaf "deqEn" (ERecv Bool) ].

  Local Open Scope guru_scope.

  Definition fifoDeq ty: Action ty fifoTree (Bit 0) :=
    ( RegRead deqPtr <- ".deqPtr" in fifoTree;
      RegRead sz <- ".size" in fifoTree;
      RegRead elements <- ".elements" in fifoTree;
      Get deqEn <- ".deqEn" in fifoTree;
      Let isDeq <- And [#deqEn; isNotZero #sz];
      RegWrite ".size" in fifoTree <- Sub #sz (ITE #isDeq $1 $0);
      RegWrite ".deqPtr" in fifoTree <- Add [TruncLsb 1 _ #sz; ITE #isDeq $1 $0];
      Put ".deqVal" in fifoTree <- ITE #isDeq (mkSome (#elements@[#deqPtr])) (mkNone ty);
      Retv ).

  Definition fifoEnq ty: Action ty fifoTree (Bit 0) :=
    ( RegRead deqPtr <- ".deqPtr" in fifoTree;
      RegRead sz <- ".size" in fifoTree;
      RegRead elements <- ".elements" in fifoTree;
      Get enqVal <- ".enqVal" in fifoTree;
      Let isEnq <- And [isValid #enqVal; isZero (TruncMsb 1 _ #sz)];
      RegWrite ".elements" in fifoTree <- ITE #isEnq
                                 (#elements@[ Add [#deqPtr; TruncLsb 1 _ #sz] <- getData #enqVal])
                                 #elements;
      RegWrite ".size" in fifoTree <- Add [#sz; ITE #isEnq $1 $0];
      Put ".enqDone" in fifoTree <- #isEnq;
      Retv ).

  Definition fifo: Mod fifoTree :=
    fun ty => [ fifoDeq ty; fifoEnq ty; Retv ].
End Fifo.

Section FifoCompile.
  (* 4-entry Bool FIFO: LgCapacity=2, so capacity = 2^2 = 4 *)
  Local Definition compiledMod := compile (fifo Bool 2).
End FifoCompile.

Set Extraction Output Directory "./Example/Fifo".
Extraction "Compile" kindSize Z.log2_up getDefault isEq compiledMod.
