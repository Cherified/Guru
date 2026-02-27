From Stdlib Require Import ZArith.
Require Import Guru.Library Guru.Syntax Guru.Compiler Guru.Extraction.
Require Import Guru.Example.Fifo.

Set Implicit Arguments.
Unset Strict Implicit.
Set Asymmetric Patterns.

Section FifoCompile.
  (* 4-entry Bool FIFO: LgCapacity=2, so capacity = 2^2 = 4 *)
  Local Definition compiledMod := compile (fifo Bool 2).
End FifoCompile.

Set Extraction Output Directory "./Example/FifoPrettyPrinter".
Extraction "Compile" size compiledMod.
