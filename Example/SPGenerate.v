From Stdlib Require Import ZArith Zmod List.
Require Import Guru.Library Guru.Syntax Guru.Notations Guru.Compiler Guru.Extraction.
Require Import Guru.Example.SimpleProcessor.

Set Implicit Arguments.
Unset Strict Implicit.
Set Asymmetric Patterns.

Import ListNotations.

Section SPCompile.
  Local Open Scope guru_scope.

  Let SPAddr    := Bit 8.
  Let SPInst    := Bit 8.
  Let SPInstMem := Array 256 (Bit 8).
  Let SPDataMem := Array 256 (Bit 8).

  (* Fetch: instruction = instMem[pc] *)
  Let spGetInst ty (addr : ty SPAddr) (imem : ty SPInstMem) : Expr ty SPInst :=
    #imem @[ #addr ].

  (* Execute: write instruction value into data memory at PC address *)
  Let spExecInst ty (addr : ty SPAddr) (inst : ty SPInst) (dmem : ty SPDataMem)
      : Expr ty SPDataMem := #dmem @[ #addr <- #inst ].

  (* Next PC: sequential, PC + 1 *)
  Let spNextPc ty (addr : ty SPAddr) (_ : ty SPInst) : Expr ty SPAddr :=
    Add [#addr; $1].

  (* Trivial branch predictor: always predict PC+1, no state *)
  Let SPPredState := Bit 0.
  Let spPredictedPc ty (addr : ty SPAddr) (_ : ty SPPredState) : Expr ty SPAddr :=
    Add [#addr; $1].
  Let spUpdatePredState ty (_ _ : ty SPAddr) (_ : ty SPPredState)
      : Expr ty SPPredState := ConstDef.

  (* Instantiate the pipelined implementation *)
  Let spMod : Mod :=
    impl (Default SPAddr) (Default SPInstMem) (Default SPDataMem)
         spGetInst spExecInst spNextPc
         (Default SPPredState)
         spPredictedPc spUpdatePredState.

  Local Definition compiledMod := compile spMod.
End SPCompile.

Set Extraction Output Directory "./Example/SPPrettyPrinter".
Extraction "Compile" size compiledMod.
