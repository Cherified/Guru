Require Export Bool Ascii String List Psatz PeanoNat.
Require Export Guru.Lib.Word Guru.Lib.WordProperties.

Set Implicit Arguments.
Set Asymmetric Patterns.

Inductive Kind :=
| Bool   : Kind
| Bit    : nat -> Kind
| Struct : list (string * Kind) -> Kind
| Array  : nat -> Kind -> Kind.

Axiom cheat: forall t, t.

Section ProdDec.
  Variable A B: Type.
  Variable Adec: forall a1 a2: A, {a1 = a2} + {a1 <> a2}.
  Variable Bdec: forall b1 b2: B, {b1 = b2} + {b1 <> b2}.

  Definition prod_dec (x y: (A * B)%type): {x = y} + {x <> y} :=
    match x, y with
    | (a1, b1), (a2, b2) => match Adec a1 a2 with
                            | left pf => match Bdec b1 b2 with
                                         | left pf1 => left (match match pf in (_ = a) return (a = a1) with
                                                                   | eq_refl => eq_refl
                                                                   end in (_ = a) return ((a, b1) = (a2, b2)) with
                                                             | eq_refl =>
                                                                 match
                                                                   match pf1 in (_ = a) return (a = b1) with
                                                                   | eq_refl => eq_refl
                                                                   end in (_ = a) return ((a2, a) = (a2, b2))
                                                                 with
                                                                 | eq_refl => eq_refl
                                                                 end
                                                             end)
                                         | right pf1 =>
                                             right (fun H : (a1, b1) = (a2, b2) =>
                                                      match pf1 match H in (_ = a) return (b1 = snd a) with
                                                              | eq_refl => eq_refl
                                                              end return False
                                                      with
                                                      end)
                                                          
                                         end
                            | right pf => right (fun H : (a1, b1) = (a2, b2) =>
                                                   match
                                                     pf match H in (_ = a) return (a1 = fst a) with
                                                       | eq_refl => eq_refl
                                                       end return False
                                                   with
                                                   end)
                            end
    end.
End ProdDec.

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
    | Struct ls =>
        fun k2 => match k2 with
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
                                     | nil => unit
                                     | a :: xs => (Convert a * DiffTuple xs)%type
                                     end.
End DiffTuple.

Section SameTuple.
  Variable T: Type.
  Fixpoint SameTuple n := match n return Type with
                          | 0 => unit
                          | S m => (T * SameTuple m)%type
                          end.
End SameTuple.

Section KindInd.
  Variable P: Kind -> Type.
  Variable pBool: P Bool.
  Variable pBit: forall n, P (Bit n).
  Variable pStruct: forall ls: list (string * Kind), DiffTuple (fun x => P (snd x)) ls -> P (Struct ls).
  Variable pArray: forall n k, P k -> P (Array n k).

  Fixpoint KindCustomInd (k: Kind): P k :=
    match k return P k with
    | Bool => pBool
    | Bit n => pBit n
    | Struct ls => pStruct ls ((fix help2 ls :=
                                  match ls return DiffTuple (fun x => P (snd x)) ls with
                                  | nil => tt
                                  | x :: xs => (KindCustomInd (snd x), help2 xs)
                                  end) ls)
    | Array n k => pArray n (KindCustomInd k)
    end.
End KindInd.

Fixpoint type (k: Kind): Type :=
  match k with
  | Bool => bool
  | Bit n => word n
  | Struct ls => DiffTuple (fun x => type (snd x)) ls
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
      + left; destruct e1, e2; reflexivity.
      + destruct X as (indPf, helpPf).
        apply (prod_dec indPf (IHls helpPf)).
    - induction n.
      + left; destruct e1, e2; reflexivity.
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


  Fixpoint FinStruct_dec (ls: list (string * Kind)): forall i j: FinStruct ls, {i = j} + {i <> j} :=
    match ls return forall i j: FinStruct ls, {i = j} + {i <> j} with
    | nil => fun i j => match i with
                        end
    | _ :: xs => fun i j => match i with
                            | inl y => match j with
                                       | inl z => match y, z with
                                                  | tt, tt => left eq_refl
                                                  end
                                       | inr z => right (fun H : inl y = inr z =>
                                                           match match H in (_ = a) return match a with
                                                                                           | inl _ => True
                                                                                           | inr _ => False
                                                                                           end with
                                                                 | eq_refl => I
                                                                 end return False with
                                                           end)
                                       end
                            | inr y => match j with
                                       | inl z => right (fun H : inr y = inl z =>
                                                           match match H in (_ = a) return match a with
                                                                                           | inl _ => False
                                                                                           | inr _ => True
                                                                                           end with
                                                                 | eq_refl => I
                                                                 end return False with
                                                           end)
                                       | inr z => match FinStruct_dec xs y z with
                                                  | left pf => left (f_equal _ pf)
                                                  | right pf =>
                                                      right
                                                        (fun H : inr y = inr z =>
                                                           match
                                                             pf (f_equal (fun e => match e with
                                                                                   | inl _ => y
                                                                                   | inr f => f
                                                                                   end) H) return False with
                                                           end)
                                                  end
                                       end
                            end
    end.

  Fixpoint fieldK {ls: list (string * Kind)}: FinStruct ls -> Kind :=
    match ls return FinStruct ls -> Kind with
    | nil => fun i => match i with
                      end
    | x :: xs => fun i => match i return Kind with
                          | inl _ => snd x
                          | inr y => @fieldK xs y
                          end
    end.

  Fixpoint fieldType {ls: list (string * Kind)}: FinStruct ls -> type (Struct ls) -> Type :=
    match ls return FinStruct ls -> type (Struct ls) -> Type with
    | nil => fun i _ => match i with
                        end
    | x :: xs => fun i e => match i return Type with
                            | inl _ => type (snd x)
                            | inr y => @fieldType xs y (snd e)
                            end
    end.

  Fixpoint fieldVal (ls: list (string * Kind)): forall (e: type (Struct ls)) (i: FinStruct ls), fieldType i e :=
    match ls return forall (e: type (Struct ls)) (i: FinStruct ls), fieldType i e with
    | nil => fun _ i => match i with
                        end
    | x :: xs => fun e i => match i return @fieldType (_ :: xs) i e with
                            | inl _ => fst e
                            | inr y => @fieldVal xs (snd e) y
                            end
    end.

  Fixpoint getFinStructOption (s: string) (ls: list (string * Kind)): option (FinStruct ls) :=
    match ls with
    | nil => None
    | x :: xs => match String.eqb s (fst x) return option (FinStruct (_ :: xs)) with
                 | true => Some (inl tt)
                 | false => match getFinStructOption s xs return option (FinStruct (_ :: xs)) with
                            | None => None
                            | Some y => Some (inr y)
                            end
                 end
    end.

  Definition getFinStruct s ls := forceOption (getFinStructOption s ls).

  Section StructFuncTuple.
    Variable ty: Kind -> Type.

    Fixpoint getStructFuncToTuple ls: (forall i: FinStruct ls, ty (fieldK i)) -> DiffTuple (fun x => ty (snd x)) ls :=
      match ls return (forall i: FinStruct ls, ty (fieldK i)) -> DiffTuple (fun x => ty (snd x)) ls with
      | nil => fun _ => tt
      | x :: xs => fun vals => (vals (inl tt), getStructFuncToTuple xs (fun i => vals (inr i)))
      end.

    Fixpoint getStructTupleToFunc ls: DiffTuple (fun x => ty (snd x)) ls -> forall i: FinStruct ls, ty (fieldK i) :=
      match ls return DiffTuple (fun x => ty (snd x)) ls -> forall i: FinStruct ls, ty (fieldK i) with
      | nil => fun _ i => match i with
                          end
      | x :: xs => fun vals i => match i with
                                 | inl _ => fst vals
                                 | inr y => getStructTupleToFunc xs (snd vals) y
                                 end
      end.
  End StructFuncTuple.
End FinStruct.

Section FinArray.
  Fixpoint FinArray n := match n with
                         | 0 => Empty_set
                         | S m => (unit + FinArray m)%type
                         end.

  Fixpoint FinArray_dec n: forall i j: FinArray n, {i = j} + {i <> j} :=
    match n return forall i j: FinArray n, {i = j} + {i <> j} with
    | 0 => fun i j => match i with
                        end
    | S m => fun i j => match i with
                        | inl y => match j with
                                   | inl z => match y, z with
                                              | tt, tt => left eq_refl
                                              end
                                   | inr z => right (fun H : inl y = inr z =>
                                                       match match H in (_ = a) return match a with
                                                                                       | inl _ => True
                                                                                       | inr _ => False
                                                                                       end with
                                                             | eq_refl => I
                                                             end return False with
                                                       end)
                                   end
                        | inr y => match j with
                                   | inl z => right (fun H : inr y = inl z =>
                                                       match match H in (_ = a) return match a with
                                                                                       | inl _ => False
                                                                                       | inr _ => True
                                                                                       end with
                                                             | eq_refl => I
                                                             end return False with
                                                       end)
                                   | inr z => match FinArray_dec m y z with
                                              | left pf => left (f_equal _ pf)
                                              | right pf =>
                                                  right
                                                    (fun H : inr y = inr z =>
                                                       match
                                                         pf (f_equal (fun e => match e with
                                                                               | inl _ => y
                                                                               | inr f => f
                                                                               end) H) return False with
                                                       end)
                                              end
                                   end
                        end
    end.

  Fixpoint FinArray_to_nat n: FinArray n -> nat :=
    match n return FinArray n -> nat with
    | 0 => fun i => match i with
                    end
    | S m => fun i => match i with
                      | inl _ => m
                      | inr y => FinArray_to_nat _ y
                      end
    end.

  Fixpoint elementVal {k} {n}: forall (e: type (Array n k)) (i: FinArray n), type k :=
    match n return forall (e: type (Array n k)) (i: FinArray n), type k with
    | 0 => fun _ i => match i with
                      end
    | S m => fun e i => match i return type k with
                        | inl _ => fst e
                        | inr y => elementVal (snd e) y
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

  Section ArrayFuncTuple.
    Variable ty: Kind -> Type.
    Variable k: Kind.

    Fixpoint getArrayFuncToTuple n: (FinArray n -> ty k) -> SameTuple (ty k) n :=
      match n return (FinArray n -> ty k) -> SameTuple (ty k) n with
      | 0 => fun _ => tt
      | S m => fun vals => (vals (inl tt), getArrayFuncToTuple m (fun i => vals (inr i)))
      end.

    Fixpoint getArrayTupleToFunc n: SameTuple (ty k) n -> forall i: FinArray n, ty k :=
      match n return SameTuple (ty k) n -> forall i: FinArray n, ty k with
      | 0 => fun _ i => match i with
                        end
      | S m => fun vals i => match i with
                             | inl _ => fst vals
                             | inr y => getArrayTupleToFunc m (snd vals) y
                             end
      end.
  End ArrayFuncTuple.
End FinArray.

Section DiffTupleDefault.
  Variable A: Type.
  Variable ConvertType: A -> Type.
  Variable convertVal: forall a, ConvertType a.

  Fixpoint DiffTupleDefault ls :=
    match ls return DiffTuple ConvertType ls with
    | nil => tt
    | x :: xs => (convertVal x, DiffTupleDefault xs)
    end.
End DiffTupleDefault.

Section SameTupleDefault.
  Variable A: Type.
  Variable val: A.

  Fixpoint SameTupleDefault n :=
    match n return SameTuple A n with
    | 0 => tt
    | S m => (val, SameTupleDefault m)
    end.
End SameTupleDefault.

Fixpoint getDefault (k: Kind): type k :=
  match k return type k with
  | Bool => false
  | Bit n => wzero n
  | Struct ls => DiffTupleDefault (fun x => type (snd x)) (fun x => getDefault (snd x)) ls
  | Array n k' => SameTupleDefault (getDefault k') n
  end.

Fixpoint size (k: Kind) :=
  match k with
  | Bool => 1
  | Bit n => n
  | Struct ls => (fix help ls :=
                    match ls with
                    | nil => 0
                    | x :: xs => size (@fieldK (x :: xs) (inl tt)) + help xs
                    end) ls
  | Array n k => n * size k
  end.

Section ToBit.
  Variable toBit: forall k, type k -> word (size k).

  Fixpoint evalStructToBit ls: forall (f: forall (i: FinStruct ls), type (fieldK i)),
      word (size (Struct ls)) :=
    match ls return forall (f: forall (i: FinStruct ls), type (fieldK i)),
        word (size (Struct ls)) with
    | nil => fun _ => WO
    | _ :: xs => fun f => wcombine (toBit _ (f (inl tt)))
                            (@evalStructToBit xs (fun (x: FinStruct xs) => (f (inr x))))
    end.

  Fixpoint evalArrayToBit k n: forall (f: forall (i: FinArray n), type k),
      word (size (Array n k)) :=
    match n return forall (f: forall (i: FinArray n), type k),
        word (size (Array n k)) with
    | 0 => fun _ => WO
    | S m => fun f => wcombine (toBit _ (f (inl tt)))
                        (@evalArrayToBit k m (fun (x: FinArray m) => (f (inr x))))
    end.
End ToBit.

Fixpoint evalToBit k: type k -> word (size k) :=
  match k return type k -> word (size k) with
  | Bool => fun v => if v then WO~1 else WO~0
  | Bit n => fun v => v
  | Struct ls => fun v => evalStructToBit evalToBit _ (getStructTupleToFunc _ _ v)
  | Array n k => fun v => evalArrayToBit evalToBit _ _ (getArrayTupleToFunc _ _ _ v)
  end.

Section FromBit.
  Variable fromBit: forall k, word (size k) -> type k.

  Fixpoint evalBitToStruct ls: word (size (Struct ls)) -> forall (i: FinStruct ls), type (fieldK i) :=
    match ls return word (size (Struct ls)) -> forall (i: FinStruct ls), type (fieldK i) with
    | nil => fun _ i => match i with
                        end
    | x :: xs => fun v i => match i return type (@fieldK (x :: xs) i) with
                            | inl _ => fromBit _ (@truncMsb (size (@fieldK (x :: xs) (inl tt))) _ v)
                            | inr y => evalBitToStruct _ (@truncLsb (size (Struct xs)) _ v) y
                            end
    end.

  Fixpoint evalBitToArray k n: word (size (Array n k)) -> forall (i: FinArray n), type k :=
    match n return word (size (Array n k)) -> forall (i: FinArray n), type k with
    | 0 => fun _ i => match i with
                      end
    | S m => fun v i => match i return type k with
                        | inl _ => fromBit _ (@truncMsb (size k) _ v)
                        | inr y => evalBitToArray _ _ (@truncLsb (size (Array m k)) _ v) y
                        end
    end.
End FromBit.

Fixpoint evalFromBit k: word (size k) -> type k :=
  match k return word (size k) -> type k with
  | Bool => fun v => if weq v WO~1 then true else false
  | Bit n => fun v => v
  | Struct ls => fun v => getStructFuncToTuple _ _ (evalBitToStruct evalFromBit _ v)
  | Array n k => fun v => getArrayFuncToTuple _ _ _ (evalBitToArray evalFromBit _ _ v)
  end.
