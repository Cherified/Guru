Require Export Bool Ascii String List Psatz PeanoNat.
Require Export Guru.Lib.Word Guru.Lib.WordProperties Guru.Lib.EclecticLib.

Global Set Implicit Arguments.
Global Set Asymmetric Patterns.

Global Open Scope string_scope.
Global Open Scope nat_scope.
Global Open Scope list_scope.

Inductive Kind :=
| Bool   : Kind
| Bit    : nat -> Kind
| Struct : list (string * Kind) -> Kind
| Array  : nat -> Kind -> Kind.

Axiom cheat: forall t, t.

Section KindDec.
  Local Notation contra k1 k2 := (right (fun H : k1 = k2 => match match H in (_ = a) return match a with
                                                                                            | k1 => True
                                                                                            | _ => False
                                                                                            end with
                                                                  | eq_refl => I
                                                                  end return False with
                                                            end)).

  Fixpoint Kind_dec k1: forall k2: Kind, {k1 = k2} + {k1 <> k2} :=
    match k1 with
    | Bool => fun k2 => match k2 with
                        | Bool => left eq_refl
                        | Bit n => contra Bool (Bit n)
                        | Struct ls => contra Bool (Struct ls)
                        | Array n k => contra Bool (Array n k)
                        end
    | Bit n => fun k2 => match k2 with
                         | Bool => contra (Bit n) Bool
                         | Bit n1 => match Nat.eq_dec n n1 with
                                     | left pf => left (match match pf in (_ = a) return (a = n) with
                                                              | eq_refl => eq_refl
                                                              end with
                                                        | eq_refl => eq_refl
                                                        end)
                                     | right pf => right (fun H : Bit n = Bit n1 =>
                                                            match pf match H in (_ = a) return (n = match a with
                                                                                                    | Bit n0 => n0
                                                                                                    | _ => n
                                                                                                    end) with
                                                                    | eq_refl => eq_refl
                                                                    end return False with
                                                            end)

                                     end
                         | Struct ls => contra (Bit n) (Struct ls)
                         | Array n' k => contra (Bit n) (Array n' k)
                         end
    | Struct ls => fun k2 => match k2 with
                             | Bool => contra (Struct ls) Bool
                             | Bit n => contra (Struct ls) (Bit n)
                             | Struct ls' => match list_eq_dec (prod_dec string_dec Kind_dec) ls ls' with
                                             | left pf => left match match pf in (_ = a) return (a = ls) with
                                                                     | eq_refl => eq_refl
                                                                     end with
                                                            | eq_refl => eq_refl
                                                            end
                                             | right n => right (fun H : Struct ls = Struct ls' =>
                                                                   match n match H in (_ = a) return (ls = match a with
                                                                                                           | Struct l => l
                                                                                                           | _ => ls
                                                                                                           end) with
                                                                           | eq_refl => eq_refl
                                                                           end return False with
                                                                   end)
                                             end
                             | Array n k => contra (Struct ls) (Array n k)
                             end
    | Array n k => fun k2 => match k2 with
                             | Bool => contra (Array n k) Bool
                             | Bit n' => contra (Array n k) (Bit n')
                             | Struct ls => contra (Array n k) (Struct ls)
                             | Array n' k' =>
                                 match Nat.eq_dec n n' with
                                 | left e =>
                                     match Kind_dec k k' with
                                     | left pf =>
                                         left
                                           match match e in (_ = a) return (a = n) with
                                                 | eq_refl => eq_refl
                                                 end with
                                           | eq_refl =>
                                               match match pf in (_ = a) return (a = k) with
                                                     | eq_refl => eq_refl
                                                     end with
                                               | eq_refl => eq_refl
                                               end
                                           end
                                     | right pf =>
                                         right
                                           (fun H : Array n k = Array n' k' =>
                                              match pf match H in (_ = a) return (k = match a with
                                                                                      | Array _ k0 => k0
                                                                                      | _ => k
                                                                                      end) with
                                                      | eq_refl => eq_refl
                                                      end return False with
                                              end)
                                     end
                                 | right pf =>
                                     right
                                       (fun H : Array n k = Array n' k' =>
                                          match pf match H in (_ = a) return (n = match a with
                                                                                  | Array n1 _ => n1
                                                                                  | _ => n
                                                                                  end) with
                                                  | eq_refl => eq_refl
                                                  end return False with
                                          end)
                                 end
                             end
    end.
End KindDec.

Section DiffTuple.
  Variable A: Type.
  Variable Convert: A -> Type.
  Fixpoint DiffTuple (ls: list A) := match ls return Type with
                                     | nil => Empty_set
                                     | a :: xs => (Convert a * DiffTuple xs)%type
                                     end.
End DiffTuple.

Section SameTuple.
  Variable T: Type.
  Fixpoint SameTuple n := match n return Type with
                          | 0 => Empty_set
                          | S m => (T * SameTuple m)%type
                          end.
End SameTuple.

Section KindInd.
  Variable P: Kind -> Type.
  Variable pBool: P Bool.
  Variable pBit: forall n, P (Bit n).
  Variable pStruct: forall ls: list (string * Kind), (fix help ls := match ls return Type with
                                                                     | nil => unit: Type
                                                                     | (_, k) :: xs => (P k * help xs)%type
                                                                     end) ls -> P (Struct ls).
  Variable pArray: forall n k, P k -> P (Array n k).

  Fixpoint KindCustomInd (k: Kind): P k :=
    match k return P k with
    | Bool => pBool
    | Bit n => pBit n
    | Struct ls => pStruct ls ((fix help2 ls :=
                                  match ls return ((fix help (ls' : list (string * Kind)) : Type := match ls' with
                                                                                                    | nil => unit
                                                                                                    | (_, k) :: xs => (P k * help xs)%type
                                                                                                    end) ls) with
                                  | nil => tt
                                  | (_, k) :: xs => (KindCustomInd k, help2 xs)
                                  end) ls)
    | Array n k => pArray n (KindCustomInd k)
    end.
End KindInd.

Fixpoint type (k: Kind): Type :=
  match k with
  | Bool => bool
  | Bit n => word n
  | Struct skl => (fix helper skl : Type :=
                     match skl with
                     | nil => Empty_set
                     | (_, k) :: xs => (type k * helper xs)%type
                     end) skl (* @DiffTuple (string * Kind)%type (fun x => type (snd x)) skl *)
  | Array n k' => SameTuple (type k') n
  end.

Section typeDec.
  Lemma isEq k: forall (e1: type k) (e2: type k),
      {e1 = e2} + {e1 <> e2}.
  Proof.
    induction k using KindCustomInd; simpl; intros.
    - apply bool_dec.
    - apply weq.
    - induction ls.
      + destruct e1.
      + destruct a as (_, k).
        destruct X as (indPf, helpPf).
        apply (prod_dec indPf (IHls helpPf)).
    - induction n.
      + destruct e1.
      + apply (prod_dec IHk IHn).
  Defined.
End typeDec.

Definition forceOption A (o : option A) : match o with
                                          | Some _ => A
                                          | None => unit
                                          end :=
  match o with
  | Some a => a
  | None => tt
  end.

Section FinStruct.
  Fixpoint FinStruct (ls: list (string * Kind)) := match ls with
                                                   | nil => Empty_set
                                                   | x :: xs => (unit + FinStruct xs)%type
                                                   end.

  Fixpoint fieldType {ls: list (string * Kind)}: FinStruct ls -> type (Struct ls) -> Type :=
    match ls return FinStruct ls -> type (Struct ls) -> Type with
    | nil => fun i _ => match i with
                        end
    | (_, k) :: xs => fun i e => match i return Type with
                                 | inl _ => type k
                                 | inr y => @fieldType xs y (snd e)
                                 end
    end.

  Fixpoint fieldVal (ls: list (string * Kind)): forall (i: FinStruct ls) (e: type (Struct ls)), fieldType i e :=
    match ls return forall (i: FinStruct ls) (e: type (Struct ls)), fieldType i e with
    | nil => fun i _ => match i with
                        end
    | (_, k) :: xs => fun i e => match i return @fieldType (_ :: xs) i e with
                                 | inl _ => fst e
                                 | inr y => @fieldVal xs y (snd e)
                                 end
    end.

  Fixpoint getFinStructOption (s: string) (ls: list (string * Kind)): option (FinStruct ls) :=
    match ls with
    | nil => None
    | (s', k) :: xs => match String.eqb s s' return option (FinStruct (_ :: xs)) with
                       | true => Some (inl tt)
                       | false => match getFinStructOption s xs return option (FinStruct (_ :: xs)) with
                                  | None => None
                                  | Some y => Some (inr y)
                                  end
                       end
    end.

  Definition getFinStruct s ls := forceOption (getFinStructOption s ls).
End FinStruct.

Section FinArray.
  Fixpoint FinArray n := match n with
                         | 0 => Empty_set
                         | S m => (unit + FinArray m)%type
                         end.

  Fixpoint elementVal {k} {n}: forall (i: FinArray n) (e: type (Array n k)), type k :=
    match n return forall (i: FinArray n) (e: type (Array n k)), type k with
    | 0 => fun i _ => match i with
                      end
    | S m => fun i e => match i return type k with
                        | inl _ => fst e
                        | inr y => elementVal y (snd e)
                        end
    end.

  Fixpoint getFinArrayOption n k: option (FinArray n) :=
    match n with
    | 0 => None
    | S m => match k return option (FinArray (S m)) with
             | 0 => Some (inl tt)
             | S k' => match getFinArrayOption m k' with
                       | None => None
                       | Some y => Some (inr y)
                       end
             end
    end.

  Definition getFinArray n k := forceOption (getFinArrayOption n k).
End FinArray.

