Section Abstract.
  Variable T: Type.
  Variable Mod: T -> Type.
  Variable State: T -> Type.
  Variable Simulates: forall {t1 t2}, Mod t1 -> Mod t2 -> (State t1 -> State t2 -> Prop) -> Prop.
  Variable SimulatesTrans: forall {t1 t2 t3 m1 m2 m3 r12 r23},
      @Simulates t1 t2 m1 m2 r12 ->
      @Simulates t2 t3 m2 m3 r23 ->
      @Simulates t1 t3 m1 m3
        (fun s1 s3 => exists s2, r12 s1 s2 /\ r23 s2 s3).

  (* Outer module B1 (and B2) parameterized by an inner module parameter "a" *)

  (* B1 simulates itself independent of its inner module a *)
  Variable TB1: T -> T.
  Variable B1: forall {ta: T} (a: Mod ta), Mod (TB1 ta).
  Variable R_B1_diff_a: forall {ta1 ta2: T}, (State ta1 -> State ta2 -> Prop) ->
                                             State (TB1 ta1) -> State (TB1 ta2) -> Prop.
  Variable Simulates_B1_diff_a:
    forall {ta1 ta2: T} (a1: Mod ta1) (a2: Mod ta2) (sa1: State ta1) (sa2: State ta2)
           (R_diff_a: State ta1 -> State ta2 -> Prop),
      Simulates (B1 a1) (B1 a2) (R_B1_diff_a R_diff_a).

  (* B2 simulates itself independent of its inner module a *)
  Variable TB2: T -> T.
  Variable B2: forall {ta: T} (a: Mod ta), Mod (TB2 ta).
  Variable R_B2_diff_a: forall {ta1 ta2: T}, (State ta1 -> State ta2 -> Prop) ->
                                             State (TB2 ta1) -> State (TB2 ta2) -> Prop.
  Variable Simulates_B2_diff_a:
    forall {ta1 ta2: T} (a1: Mod ta1) (a2: Mod ta2) (sa1: State ta1) (sa2: State ta2)
           (R_diff_a: State ta1 -> State ta2 -> Prop),
      Simulates (B2 a1) (B2 a2) (R_B2_diff_a R_diff_a).

  (* B1 simulates B2 if the inner modules of both are the same *)
  Variable R_B1_B2_same_a: forall {ta: T} (a: Mod ta) (sa: State ta),
      State (TB1 ta) -> State (TB2 ta) -> Prop.
  Variable Simulates_B1_B2_same_a:
    forall {ta: T} (a: Mod ta) (sa: State ta),
      Simulates (B1 a) (B2 a) (R_B1_B2_same_a a sa).

  Section Simulates_B1_B2_diff_a.
    Context {ta1 ta2: T}.
    Variable a1: Mod ta1.
    Variable a2: Mod ta2.
    Variable sa1: State ta1.
    Variable sa2: State ta2.
    Variable R_diff_a: State ta1 -> State ta2 -> Prop.

    Definition R_B1_B2_diff_a: State (TB1 ta1) -> State (TB2 ta2) -> Prop :=
      fun s11 s22 => exists s12, (R_B1_diff_a R_diff_a s11 s12 /\ R_B1_B2_same_a a2 sa2 s12 s22).

    (* B1 simulates B2 *)
    Definition Simulates_B1_B2_diff_a: Simulates (B1 a1) (B2 a2) R_B1_B2_diff_a :=
      SimulatesTrans (Simulates_B1_diff_a a1 a2 sa1 sa2 R_diff_a) (Simulates_B1_B2_same_a a2 sa2).
  End Simulates_B1_B2_diff_a.
End Abstract.
