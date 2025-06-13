From Stdlib Require Import ExtrHaskellBasic ExtrHaskellNatInteger ExtrHaskellString ExtrHaskellZInteger.
Require Import Guru.Library Guru.Compiler.

Require Extraction.

Extraction Language Haskell.

Extract Inductive Prod => "(,)" [ "(,)" ].

(*
Warning: Setting extraction output directory by default to "/Users/muralivi/Cherified/Guru". Use "Set Extraction Output Directory" or command line option "-output-directory"
to set a different directory for extracted files to appear in. [extraction-default-directory,extraction,default]
The file /Users/muralivi/Cherified/Guru/Compile.hs has been created by extraction.
*)
