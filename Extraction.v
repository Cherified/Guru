From Stdlib Require Import ExtrHaskellBasic ExtrHaskellNatInt ExtrHaskellString ExtrHaskellZInteger.
Require Import Guru.Lib.Library.
Require Import Guru.Compiler.

From Stdlib Require Import List.
Require Import Guru.Syntax.
Require Import Guru.Notations.

Require Extraction.

Definition compiledMod := compile {|modDecl := Notations.decl;
                                    modActions := fun ty =>
                                                    (LetA _ <- Notations.act ty ; Return ConstDef)%guru :: nil |}.

Extraction Language Haskell.

Extraction "Compile"
  size
  genFinStruct
  genFinArray
  compiledMod.

(*
Warning: Setting extraction output directory by default to "/Users/muralivi/Cherified/Guru". Use "Set Extraction Output Directory" or command line option "-output-directory"
to set a different directory for extracted files to appear in. [extraction-default-directory,extraction,default]
The file /Users/muralivi/Cherified/Guru/Compile.hs has been created by extraction.
*)
