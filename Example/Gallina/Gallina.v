(*
 * Copyright (c) 2025-2026 Cherified Systems LLC
 *
 * SPDX-License-Identifier: MIT
 *)

(* Simulation test for CallGallina: a Gallina register holding an unbounded history
   (list Z), updated through DPI-C calls into the extracted Gallina functions. *)

From Stdlib Require Import String List ZArith Zmod.
From Guru Require Import Primitives Library Syntax Combinators Notations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Asymmetric Patterns.

Import ListNotations.

Section Gallina.
  Local Open Scope string.
  Local Open Scope guru_scope.

  Definition histReg : GallinaReg := {| gRegType := list Z; gRegInit := nil |}.

  Definition gTree : Tree Elem :=
    Node ""
      [ Leaf "cnt" (EReg (Build_Reg (Bit 8) (Some (getDefault _))));
        Leaf "hist" (EGallinaReg histReg) ].

  Definition histPath := getGallinaRegPathTree gTree ".hist".

  Definition OutK := STRUCT_TYPE { "sum" :: Bit 16 ;
                                   "len" :: Bit 8 ;
                                   "pick" :: Bit 8 }.

  (* Push v; return the sum and length of the history and an oracle-picked element
     (the latest one when the oracle returns 0). *)
  Definition pushHist (o: nat -> nat) (v: type (Bit 8)) (h: list Z) : type OutK * list Z :=
    let h' := Zmod.to_Z v :: h in
    let len := length h' in
    let pick := nth (Nat.modulo (o 0%nat) len) h' 0%Z in
    (STRUCT_CONST { "sum" ::= Zmod.of_Z _ (fold_left Z.add h' 0%Z) ;
                    "len" ::= Zmod.of_Z _ (Z.of_nat len) ;
                    "pick" ::= Zmod.of_Z _ pick }, h').

  Definition clearHist (o: nat -> nat) (v: type (Bit 0)) (h: list Z) : type (Bit 0) * list Z :=
    (Zmod.zero, nil).

  Definition gRule ty : Action ty gTree (Bit 0) :=
    ( RegRead c <- ".cnt" in gTree;
      LetG r : OutK <- pushHist ( #c ) in histPath;
      Sys [ DispString ty "cnt="; DispDecimal #c;
            DispString ty " sum="; DispDecimal (#r`"sum");
            DispString ty " len="; DispDecimal (#r`"len");
            DispString ty " pick="; DispDecimal (#r`"pick");
            DispString ty "\n" ];
      If (Eq #c $5) Then (
        LetG z : Bit 0 <- clearHist ( Const ty (Bit 0) Zmod.zero ) in histPath;
        Retv );
      If (Eq #c $9) Then (
        Sys [ Finish ty ];
        Retv );
      RegWrite ".cnt" in gTree <- Add [#c; $1];
      Retv ).

  Definition gallinaMod: Mod gTree :=
    fun ty => [ gRule ty ].
End Gallina.

From Guru Require Import Extraction.
Set Extraction Output Directory "./Example/Gallina".

From Guru Require Import Compiler.
Definition compiledMod := compile gallinaMod.
Extraction "Compile" kindSize Z.log2_up getDefault isEq compiledMod.
