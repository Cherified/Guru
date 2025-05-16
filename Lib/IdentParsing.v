(* Adopted from https://github.com/mit-plv/rupicola/blob/master/src/Rupicola/Lib/IdentParsing.v and
   https://github.com/mit-plv/coqutil/blob/master/src/coqutil/Macros/ident_to_string.v *)

Require Import String.
Require Import Ltac2.Ltac2. Import Ltac2.Option Ltac2.Constr Ltac2.Constr.Unsafe.

Module Import Private.
  Import Coq.Lists.List Coq.Strings.Ascii BinNat.
  Local Ltac2 rec list_constr_of_constr_list xs :=
    match! xs with cons ?x ?xs => x :: list_constr_of_constr_list xs | nil => [] end.
  Local Definition f : ltac:(do 256 refine (ascii->_); exact unit) := ltac:(intros;exact tt).
  Definition app : unit := ltac2:(
    let args := eval cbv in (map (fun n => ascii_of_N (N.of_nat n)) (seq 0 256)) in
    refine (make (App 'f (Array.of_list (list_constr_of_constr_list args))))).
End Private.

(* This implementation uses typeclasses, which allows it to play better with
   other Coq mechanisms like `Program Definition`; it also makes
   `binder_to_string` unnecessary. *)

(* The following examples fail with TacInTerm, but work with TC::

     Definition nlet {A P} (vars: list string) (val : A) (body : forall a : A, P a) : P val :=
       let x := val in body x.

     Notation "'Let/n' x := val 'in' body" :=
       (nlet [IdentParsing.TacInTerm.ident_to_string x] val (fun x => body))
         (at level 200, x ident, body at level 200,
          only parsing).
    Definition x := (Let/n a := 1 in a + 1).

    Notation "'Let/n' x := val 'in' body" :=
      (nlet [IdentParsing.binder_to_string val x] val (fun x => body))
        (at level 200, x ident, body at level 200,
         only parsing).
    Program Definition x := (Let/n a := _ in a + 1). *)

Ltac2 constr_string_of_string (s : string) :=
  let asciis := match kind (eval red in app) with App _ x => x | _ => Control.throw No_value end in
  let scons := 'String.String in
  let l := String.length s in
  let rec f i :=
    if Int.equal i l then 'String.EmptyString else
      make (App scons (Array.of_list [Array.get asciis (Char.to_int (String.get s i)); f (Int.add i 1)])) in
  f 0.

Inductive __Ltac2_Marker := __ltac2_marker.

Ltac serialize_ident_in_context :=
  ltac2:(match! goal with
         | [ h: __Ltac2_Marker |- _ ] =>
             let coq_string := constr_string_of_string (Ident.to_string h) in
             exact ($coq_string)
         | [  |- _ ] =>
             exact ("!! IndentParsing: no ident found"%string)
         end).

Class __IdentToString := __identToString: string.

Set Default Proof Mode "Classic". (* after Rocq 9, Default Proof Mode "Ltac2" will parse hint extern as ltac2 *)
#[global] Hint Extern 1 __IdentToString => serialize_ident_in_context : typeclass_instances.

Notation Stringify a :=
  (match __ltac2_marker return __IdentToString with a => _ end).
