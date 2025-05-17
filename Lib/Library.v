Require Import String Ascii PeanoNat List Bool.
Require Import Guru.Lib.Word.

Set Implicit Arguments.
Unset Strict Implicit.
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
    | Struct ls => pStruct ((fix help2 ls :=
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

Section ForceOption.
  Variable A: Type.
  Definition forceOption A (o : option A) : match o with
                                            | Some _ => A
                                            | None => unit
                                            end :=
    match o with
    | Some a => a
    | None => tt
    end.
End ForceOption.

Section FinStruct.
  Variable K: Type.
  Fixpoint FinStruct (ls: list (string * K)) := match ls with
                                              | nil => Empty_set
                                              | x :: xs => (unit + FinStruct xs)%type
                                              end.


  Fixpoint FinStruct_dec (ls: list (string * K)): forall i j: FinStruct ls, {i = j} + {i <> j} :=
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
                                       | inr z => match FinStruct_dec y z with
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

  Fixpoint FinStruct_to_nat (ls: list (string * K)) : FinStruct ls -> nat :=
    match ls return FinStruct ls -> nat with
    | nil => fun i => match i with
                      end
    | x :: xs => fun i => match i return nat with
                          | inl _ => 0
                          | inr y => @FinStruct_to_nat xs y
                          end
    end.

  Fixpoint fieldNameK (ls: list (string * K)): FinStruct ls -> (string * K) :=
    match ls return FinStruct ls -> (string * K) with
    | nil => fun i => match i with
                      end
    | x :: xs => fun i => match i return (string * K) with
                          | inl _ => x
                          | inr y => @fieldNameK xs y
                          end
    end.

  Fixpoint fieldName (ls: list (string * K)): FinStruct ls -> string :=
    match ls return FinStruct ls -> string with
    | nil => fun i => match i with
                      end
    | x :: xs => fun i => match i return string with
                          | inl _ => fst x
                          | inr y => @fieldName xs y
                          end
    end.

  Fixpoint fieldK (ls: list (string * K)): FinStruct ls -> K :=
    match ls return FinStruct ls -> K with
    | nil => fun i => match i with
                      end
    | x :: xs => fun i => match i return K with
                          | inl _ => snd x
                          | inr y => @fieldK xs y
                          end
    end.

  Fixpoint getFinStructOption (s: string) (ls: list (string * K)): option (FinStruct ls) :=
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
    Variable ty: K -> Type.

    Fixpoint funcToStruct ls: (forall i: FinStruct ls, ty (fieldK i)) -> DiffTuple (fun x => ty (snd x)) ls :=
      match ls return (forall i: FinStruct ls, ty (fieldK i)) -> DiffTuple (fun x => ty (snd x)) ls with
      | nil => fun _ => tt
      | x :: xs => fun vals => (vals (inl tt), funcToStruct (fun i => vals (inr i)))
      end.

    Fixpoint structToFunc ls: DiffTuple (fun x => ty (snd x)) ls -> forall i: FinStruct ls, ty (fieldK i) :=
      match ls return DiffTuple (fun x => ty (snd x)) ls -> forall i: FinStruct ls, ty (fieldK i) with
      | nil => fun _ i => match i with
                          end
      | x :: xs => fun vals i => match i return ty (@fieldK (x :: xs) i) with
                                 | inl _ => fst vals
                                 | inr y => structToFunc (snd vals) y
                                 end
      end.
  End StructFuncTuple.
End FinStruct.

Section FinToFinStruct.
  Variable X Y: Type.
  Fixpoint finToFinStruct (xs: list (string * X)): forall (ys: list (string * Y)),
      length xs = length ys -> FinStruct xs -> FinStruct ys :=
    match xs return forall (ys: list (string * Y)), length xs = length ys -> FinStruct xs -> FinStruct ys with
    | nil => fun _ _ i => match i with
                          end
    | p :: ps =>
        fun ys pf i =>
          match ys return length (p :: ps) = length ys -> FinStruct (p :: ps) -> FinStruct ys with
          | nil => fun pf _ =>
                     match match pf in (_ = a) return match a with
                                                      | 0 => False
                                                      | S _ => True
                                                      end with
                           | eq_refl => I
                           end return (FinStruct nil) with
                     end
                       
          | q :: qs => fun pf1 i => match i return FinStruct (q :: qs) with
                                    | inl y => inl tt
                                    | inr y => inr (@finToFinStruct ps qs
                                                      match pf1 with
                                                      | eq_refl => eq_refl
                                                      end
                                                      y)
                                    end
          end pf i
    end.
End FinToFinStruct.

Section ConvFinStruct.
  Variable A K: Type.
  Variable getK: A -> K.
  Variable ty: K -> Type.
  Variable conv: forall a, ty (getK a).

  Fixpoint convFinStruct (ls: list (string * A)): forall i: FinStruct (map (fun x => (fst x, getK (snd x))) ls),
      ty (fieldK i) :=
    match ls return forall i: FinStruct (map (fun x => (fst x, getK (snd x))) ls), ty (fieldK i) with
    | nil => fun i => match i with
                      end
    | x :: xs => fun i => match i with
                          | inl _ => conv (snd x)
                          | inr y => @convFinStruct xs y
                          end
    end.
End ConvFinStruct.

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
                                   | inr z => match FinArray_dec y z with
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
                      | inr y => FinArray_to_nat y
                      end
    end.

  Fixpoint FinArray_of_nat_lt i n {struct i} : i < n -> FinArray n :=
    match n return i < n -> FinArray n with
    | 0 => fun H: i < 0 => False_rect (FinArray 0) (Nat.nlt_0_r i H)
    | S m => match i return i < S m -> FinArray (S m) with
             | 0 => fun _ => inl tt
             | S j => fun H: S j < S m => inr (FinArray_of_nat_lt (proj2 (Nat.succ_lt_mono j m) H))
             end
    end.

  Definition FinArray_of_nat_ltDec i n (pf: i <? n = true): FinArray n :=
    @FinArray_of_nat_lt i n (proj1 (Nat.ltb_lt i n) pf).

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

    Fixpoint funcToArray n: (FinArray n -> ty k) -> SameTuple (ty k) n :=
      match n return (FinArray n -> ty k) -> SameTuple (ty k) n with
      | 0 => fun _ => tt
      | S m => fun vals => (vals (inl tt), funcToArray (fun i => vals (inr i)))
      end.

    Fixpoint arrayToFunc n: SameTuple (ty k) n -> forall i: FinArray n, ty k :=
      match n return SameTuple (ty k) n -> forall i: FinArray n, ty k with
      | 0 => fun _ i => match i with
                        end
      | S m => fun vals i => match i with
                             | inl _ => fst vals
                             | inr y => arrayToFunc (snd vals) y
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

Fixpoint Default (k: Kind): type k :=
  match k return type k with
  | Bool => false
  | Bit n => wzero n
  | Struct ls => DiffTupleDefault (fun x => Default (snd x)) ls
  | Array n k' => SameTupleDefault (Default k') n
  end.

Fixpoint size (k: Kind) :=
  match k with
  | Bool => 1
  | Bit n => n
  | Struct ls => (fix help ls :=
                    match ls with
                    | nil => 0
                    | x :: xs => size (@fieldK _ (x :: xs) (inl tt)) + help xs
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
    | _ :: xs => fun f => wcombine (toBit (f (inl tt)))
                            (@evalStructToBit xs (fun (x: FinStruct xs) => (f (inr x))))
    end.

  Fixpoint evalArrayToBit k n: forall (f: forall (i: FinArray n), type k),
      word (size (Array n k)) :=
    match n return forall (f: forall (i: FinArray n), type k),
        word (size (Array n k)) with
    | 0 => fun _ => WO
    | S m => fun f => wcombine_flip (@evalArrayToBit k m (fun (x: FinArray m) => (f (inr x)))) (toBit (f (inl tt)))
    end.
End ToBit.

Fixpoint evalToBit k: type k -> word (size k) :=
  match k return type k -> word (size k) with
  | Bool => fun v => if v then (WO~1)%word else (WO~0)%word
  | Bit n => fun v => v
  | Struct ls => fun v => evalStructToBit evalToBit (structToFunc v)
  | Array n k => fun v => evalArrayToBit evalToBit (arrayToFunc v)
  end.

Section FromBit.
  Variable fromBit: forall k, word (size k) -> type k.

  Fixpoint evalBitToStruct ls: word (size (Struct ls)) -> forall (i: FinStruct ls), type (@fieldK _ ls i) :=
    match ls return word (size (Struct ls)) -> forall (i: FinStruct ls), type (@fieldK _ ls i) with
    | nil => fun _ i => match i with
                        end
    | x :: xs => fun v i => match i return type (@fieldK _ (x :: xs) i) with
                            | inl _ => fromBit (@truncMsb (size (@fieldK _ (x :: xs) (inl tt))) _ v)
                            | inr y => evalBitToStruct (@truncLsb (size (Struct xs)) _ v) y
                            end
    end.

  Fixpoint evalBitToArray k n: word (size (Array n k)) -> forall (i: FinArray n), type k :=
    match n return word (size (Array n k)) -> forall (i: FinArray n), type k with
    | 0 => fun _ i => match i with
                      end
    | S m => fun v i => match i return type k with
                        | inl _ => fromBit (@truncMsb (size k) _ v)
                        | inr y => evalBitToArray (@truncLsb (size (Array m k)) _ v) y
                        end
    end.
End FromBit.

Fixpoint evalFromBit k: word (size k) -> type k :=
  match k return word (size k) -> type k with
  | Bool => fun v => if weq v (WO~1)%word then true else false
  | Bit n => fun v => v
  | Struct ls => fun v => funcToStruct (evalBitToStruct evalFromBit v)
  | Array n k => fun v => funcToArray (evalBitToArray evalFromBit v)
  end.

Fixpoint evalOrBinary (k : Kind) : type k -> type k -> type k :=
  match k return type k -> type k -> type k with
  | Bool => orb
  | Bit n => @wor n
  | Struct ls => fun a b => funcToStruct (fun i => evalOrBinary (structToFunc a i) (structToFunc b i))
  | Array n k => fun a b => funcToArray (fun i => evalOrBinary (arrayToFunc a i) (arrayToFunc b i))
  end.

Section WordArray.
  Variable T: Type.
  Variable val: T.
  Variable n: nat.
  Variable finMap: FinArray n -> T.
  Variable w: word (Nat.log2_up n).

  Definition readArray : T :=
    match lt_dec (Z.to_nat (wordVal _ w)) n with
    | left pf => finMap (FinArray_of_nat_lt pf)
    | right _ => val
    end.

  Definition writeArray : FinArray n -> T :=
    match lt_dec (Z.to_nat (wordVal _ w)) n return FinArray n -> T with
    | left pf => fun i => match FinArray_dec (FinArray_of_nat_lt pf) i return T with
                          | left _ => val
                          | right _ => finMap i
                          end
    | right _ => finMap
    end.
End WordArray.

Section UpdFinStruct.
  Variable K: Type.
  Variable ty: K -> Type.
  Variable ls: list (string * K).
  Variable orig: forall i: FinStruct ls, ty (fieldK i).
  Variable x: FinStruct ls.
  Variable updVal: ty (fieldK x).
  Definition updStruct (i: FinStruct ls): ty (fieldK i) :=
    match FinStruct_dec x i with
    | left pf => match pf in _ = Y return ty (fieldK Y) with
                 | eq_refl => updVal
                 end
    | right _ => orig i
    end.
End UpdFinStruct.

Section UpdFinArray.
  Variable A: Type.
  Variable n: nat.
  Variable orig: forall i: FinArray n, A.
  Variable p: FinArray n.
  Variable updVal: A.
  Definition updArray (i: FinArray n): A :=
    match FinArray_dec p i with
    | left pf => match pf in _ = Y return A with
                 | eq_refl => updVal
                 end
    | right _ => orig i
    end.
End UpdFinArray.
  
Section FoldFinStruct.
  Variable K A B: Type.
  Variable def: A.
  Variable ls: list (string * K).
  Variable f: B -> A -> A.
  Fixpoint foldFinStruct (ls: list (string * K)): (FinStruct ls -> B) -> A :=
    match ls return (FinStruct ls -> B) -> A with
    | nil => fun _ => def
    | x :: xs => fun func => f (func (inl tt)) (@foldFinStruct xs (fun i => func (inr i)))
    end.
End FoldFinStruct.

Section GenFinStruct.
  Variable K: Type.
  Fixpoint genFinStruct ls: list (@FinStruct K ls) :=
    match ls with
    | nil => nil
    | _ :: xs => inl tt :: map inr (genFinStruct xs)
    end.
End GenFinStruct.

Fixpoint genFinArray n: list (FinArray n) :=
  match n with
  | 0 => nil
  | S m => inl tt :: map inr (genFinArray m)
  end.

Section StringToNum.
  Local Open Scope Z.
  Local Open Scope char.
  Definition hexDigitToZ (c : ascii) : option Z :=
    match c with
    | "0" => Some 0
    | "1" => Some 1
    | "2" => Some 2
    | "3" => Some 3
    | "4" => Some 4
    | "5" => Some 5
    | "6" => Some 6
    | "7" => Some 7
    | "8" => Some 8
    | "9" => Some 9
    | "a" | "A" => Some 10
    | "b" | "B" => Some 11
    | "c" | "C" => Some 12
    | "d" | "D" => Some 13
    | "e" | "E" => Some 14
    | "f" | "F" => Some 15
    | _   => None
    end.

  Definition binDigitToZ c : option Z :=
    match c with
    | "0" => Some 0
    | "1" => Some 1
    | _   => None
    end.
  Local Close Scope char.

  Fixpoint readHexZAux acc s : option Z :=
  match s with
    | ""%string => Some acc
    | String c s' =>
      match hexDigitToZ c with
        | Some n => readHexZAux (16 * acc + n) s'
        | None => None
      end
  end.

  Definition readHexZ := readHexZAux 0.

  Definition hex s := forceOption (readHexZ s).

  Fixpoint readBinAux acc s : option Z :=
    match s with
    | ""%string => Some acc
    | String c s' =>
        match binDigitToZ c with
        | Some n => readBinAux (2 * acc + n) s'
        | None => None
        end
    end.

  Definition readBinZ := readBinAux 0.

  Definition bin s := forceOption (readBinZ s).
End StringToNum.

Section Nth_pf.
  Variable A: Type.

  Fixpoint nth_pf (ls: list A): forall i, i < length ls -> A.
    refine (
    match ls return forall i, i < length ls -> A with
    | nil => fun _ pf => _
    | x :: xs => fun i => match i return i < length (x :: xs) -> A with
                          | 0 => fun _ => x
                          | S m => fun pf => nth_pf xs m (PeanoNat.lt_S_n _ _ pf)
                          end
    end).
    abstract (simpl in pf; Lia.lia).
  Defined.
End Nth_pf.

Theorem idx_offset_len idx offset len (pfGe: idx >= offset) (pfLt: idx < offset + len): idx - offset < len.
Proof.
  Lia.lia.
Qed.

Definition evalReadArray (n m: nat) (k: Kind) (i: word m) (v: type (Array n k)) :=
  match lt_dec (Z.to_nat (wordVal _ i)) n return type k with
  | left pf => arrayToFunc v (FinArray_of_nat_lt pf)
  | right _ => Default k
  end.

Arguments evalReadArray [n m k] i !v.

Section ArrayFromListZ.
  Variable width: nat.
  Fixpoint arrayFromListZ (ls: list Z): SameTuple (word width) (length ls) :=
    match ls return SameTuple (word width) (length ls) with
    | nil => tt
    | x :: xs => (ZToWord width x, arrayFromListZ xs)
    end.

  Fixpoint arrayFromListZSize size (ls: list Z): SameTuple (word width) size :=
    match size with
    | 0 => tt
    | S m => match ls with
             | x :: xs => (ZToWord width x, arrayFromListZSize m xs)
             | nil => (wzero width, arrayFromListZSize m nil)
             end
    end.

  Fixpoint arrayFromListZSizeOffset (size: nat): forall offset: nat, list Z -> SameTuple (word width) size :=
    match size return nat -> list Z -> SameTuple (word width) size with
    | 0 => fun _ _ => tt
    | S m => fun offset ls => match offset with
                              | 0 => match ls with
                                     | nil => (wzero width, arrayFromListZSizeOffset m 0 nil)
                                     | x :: xs => (ZToWord width x, arrayFromListZSizeOffset m 0 xs)
                                     end
                              | S k => (wzero width, arrayFromListZSizeOffset m k ls)
                              end
    end.

  Section ArrayFromListZEq.
    Variable size: nat.
    Variable arr: type (Array size (Bit width)).
    Variable offset: nat.
    Variable ls: list Z.

    Definition ArrayFromListZEq := forall (i: FinArray size)
                                          (pfGe: FinArray_to_nat i >= offset)
                                          (pfLt: FinArray_to_nat i < offset + length ls),
        nth_pf (idx_offset_len pfGe pfLt) = wordVal width (arrayToFunc (ty := type) (k := Bit width) arr i).

    Definition ReadArrayFromListZEq := forall m (i: word m)
                                              (pfGe: Z.to_nat (wordVal m i) >= offset)
                                              (pfLt: Z.to_nat (wordVal m i) < offset + length ls),
        evalReadArray i arr = ZToWord width (nth_pf (idx_offset_len pfGe pfLt)).
  End ArrayFromListZEq.
End ArrayFromListZ.

Definition lgCeil i := S (Nat.log2_iter (pred (pred i)) 0 1 0).
