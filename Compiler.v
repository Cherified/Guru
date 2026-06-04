From Stdlib Require Import String List ZArith.
Require Import Guru.Library Guru.Syntax.

Set Implicit Arguments.
Unset Strict Implicit.
Set Asymmetric Patterns.

Local Definition CTmp := (string * nat)%type.
Definition CExpr := Expr (fun k => CTmp).
Section CTmp.
  Variable x: CTmp.
  Local Definition cTmpName: string := fst x.
  Local Definition cTmpIdx: nat := snd x.
End CTmp.

Local Definition CReg := (string * nat)%type.
Section CReg.
  Variable x: CReg.
  Local Definition cRegName: string := fst x.
  Local Definition cRegPos: nat := snd x.
End CReg.

Local Definition CMem := (string * nat)%type.
Section CMem.
  Variable x: CMem.
  Local Definition cMemName: string := fst x.
  Local Definition cMemPos: nat := snd x.
End CMem.

Local Definition CMeth := (string * nat)%type.
Section CMeth.
  Variable x: CMeth.
  Local Definition cMethName: string := fst x.
  Local Definition cMethPos: nat := snd x.
End CMeth.

Inductive Compiled :=
| CReadReg (x : CReg) (k: Kind) (t: CTmp) (cont: Compiled)
| CWriteReg (x : CReg) k (v: CExpr k) (cont: Compiled)
| CReadRqMem (x: CMem) (sz: nat) (k: Kind) (ports: nat) (i: CExpr (Bit (Z.log2_up (Z.of_nat sz)))) (p: nat) (cont: Compiled)
| CReadRpMem (x: CMem) (sz: nat) (k: Kind) (ports: nat) (p: nat) (t: CTmp) (cont: Compiled)
| CWriteMem (x: CMem) (sz: nat) (k: Kind) (ports: nat) (i: CExpr (Bit (Z.log2_up (Z.of_nat sz)))) (v: CExpr k) (cont: Compiled)
| CSend (x: CMeth) k (v: CExpr k) (cont: Compiled)
| CRecv (x: CMeth) (k: Kind) (t: CTmp) (cont: Compiled)
| CLetExpr (t: CTmp) k (v: CExpr k) (cont: Compiled)
| CLetAction (k': Kind) (a: Compiled) (cont: Compiled)
| CNonDet (t: CTmp) (k: Kind) (cont: Compiled)
| CIfElse (p: CExpr Bool) (k': Kind) (t f cont: Compiled)
| CSys (ls: list (SysT (fun k => CTmp))) (cont: Compiled)
| CReturn (t: CTmp) k (v: CExpr k).

(* Synchronous memory issues:
   - Bypass if ReadRq before ReadRp
   - Bypass if Write before ReadRp (from address reg if address is registered)
   - Bypass if Write before ReadRq (to data reg if data is registered)
   - Correct orders for address registered: ReadRp, ReadRq, Write; ReadRp, Write, ReadRq
   - Only Correct order for data registered: ReadRp, ReadRq, Write

   We support just data registered synchronous memory for now,
   and error out in the compiler if any of the above bypass conditions arise.
   The compiler also errors out if multiple Writes occur *)

(* Structure to keep track of Mem ReadRq, ReadRp and Write,
   to ensure only order [ReadRp; ReadRq; Write] is used *)



Section TreePathNaming.
  Variable A: Type.

  Fixpoint countLeaves (t: Tree A) : nat :=
    match t with
    | Leaf _ _ => 1
    | Node _ children =>
        (fix loop (ls: list (Tree A)) : nat :=
           match ls with
           | nil => 0
           | x :: xs => @countLeaves x + loop xs
           end) children
    end.

  Fixpoint getPathIndex (t: Tree A) : LeafPath t -> nat :=
    match t return LeafPath t -> nat with
    | Leaf _ _ => fun _ => 0
    | Node _ children =>
        (fix loop (ls: list (Tree A)) :
           ((fix loop (ls : list (Tree A)) : Type :=
              match ls with
              | nil => Empty_set
              | x :: xs => (LeafPath x + loop xs)%type
              end) ls) -> nat :=
           match ls return
             ((fix loop (ls : list (Tree A)) : Type :=
                match ls with
                | nil => Empty_set
                | x :: xs => (LeafPath x + loop xs)%type
                end) ls) -> nat
           with
           | nil => fun p => match (p : Empty_set) with end
           | x :: xs => fun p =>
               match p with
               | inl pl => @getPathIndex x pl
               | inr pr => @countLeaves x + loop xs pr
               end
           end) children
    end.

  Fixpoint getPathName (t: Tree A) : LeafPath t -> string :=
    match t return LeafPath t -> string with
    | Leaf name _ => fun _ => name
    | Node name children =>
        (fix loop (ls: list (Tree A)) :
           ((fix loop (ls : list (Tree A)) : Type :=
              match ls with
              | nil => Empty_set
              | x :: xs => (LeafPath x + loop xs)%type
              end) ls) -> string :=
           match ls return
             ((fix loop (ls : list (Tree A)) : Type :=
                match ls with
                | nil => Empty_set
                | x :: xs => (LeafPath x + loop xs)%type
                end) ls) -> string
           with
           | nil => fun p => match (p : Empty_set) with end
           | x :: xs => fun p =>
               match p with
               | inl pl => match name with
                           | ""%string => @getPathName x pl
                           | _ => (name ++ "_" ++ @getPathName x pl)%string
                           end
               | inr pr => loop xs pr
               end
           end) children
    end.
End TreePathNaming.

Arguments countLeaves [A] t.
Arguments getPathIndex [A] [t] p.
Arguments getPathName [A] [t] p.

Section CompileAction.
  Variable t: Tree ModElem.

  (* CompileState keeps track of the compilation context:
     - list (string * Kind): Tracks active temporary variables created by let-expressions.
       Their positions in this list determine their unique indices in compiled variables.
     - list (nat * nat): Tracks read-requests (memIdx, portIdx) made in this execution path.
       Used to detect and reject [Write; ReadRq] sequential bypass violations.
     - list (nat * nat): Tracks read-responses (memIdx, portIdx) made in this execution path.
       Used to detect and reject [ReadRq; ReadRp] sequential bypass violations.
     - list nat: Tracks written memory indices (memIdx) in this execution path.
       Used to enforce single-write-per-step memory rules.
     - list nat: Tracks send method indices (sendIdx) called in this execution path.
       Used to enforce single-send constraints. *)
  Definition CompileState :=
    (list (string * Kind) *
       (list (nat * nat) * list (nat * nat) * list nat * list nat))%type.

  Local Open Scope bool.

  Definition hasRq (rqs: list (nat * nat)) (memIdx: nat) (port: nat) : bool :=
    existsb (fun '(m, p) => (m =? memIdx) && (p =? port)) rqs.

  Definition hasRp (rps: list (nat * nat)) (memIdx: nat) (port: nat) : bool :=
    existsb (fun '(m, p) => (m =? memIdx) && (p =? port)) rps.

  Definition hasWr (wrs: list nat) (memIdx: nat) : bool :=
    existsb (fun m => m =? memIdx) wrs.

  Definition hasSend (sends: list nat) (sendIdx: nat) : bool :=
    existsb (fun s => s =? sendIdx) sends.

  (* compileAction compiles a given Action into a Compiled program syntax tree:
     - CTmp argument (retVar): Represents the target temporary variable where the final return value
       of this action will be stored (eventually compiled into a CReturn statement).
     - Returns: A tuple of type:
       (bool * CompileState * Compiled)
       where:
       - bool: Represents the compilation validity flag (returns 'false' if any bypass or write violations occur).
       - CompileState: The updated CompileState, defined as above.
       - Compiled: The structured compiled program syntax tree representing the compiled output. *)
  Fixpoint compileAction k (a: @Action (fun k => CTmp) t k):
    CompileState -> CTmp ->
    (bool * CompileState * Compiled) :=
    match a return CompileState -> CTmp ->
                   (bool * CompileState * Compiled)
    with
    | ReadReg s x cont =>
        fun '(tmps, (rqs, rps, wrs, sends)) retVar =>
          let tmp := (s, length tmps) in
          let regIdx := getPathIndex x.(regPath) in
          let regName := getPathName x.(regPath) in
          let '(result, newSt, rest) :=
            compileAction (cont tmp)
              ((s, regKind (getRegFromPath x)) :: tmps, (rqs, rps, wrs, sends)) retVar in
          (result, newSt, CReadReg (regName, regIdx) (regKind (getRegFromPath x)) tmp rest)
    | WriteReg x v cont =>
        fun '(tmps, (rqs, rps, wrs, sends)) retVar =>
          let regIdx := getPathIndex x.(regPath) in
          let regName := getPathName x.(regPath) in
          let '(result, newSt, rest) :=
            compileAction cont
              (tmps, (rqs, rps, wrs, sends)) retVar in
          (result, newSt, CWriteReg (regName, regIdx) v rest)
    | ReadRqMem x i p cont =>
        fun '(tmps, (rqs, rps, wrs, sends)) retVar =>
          let memIdx := getPathIndex x.(memPath) in
          let memName := getPathName x.(memPath) in
          let portIdx := finNum p in
          let '(valid, newSt, rest) :=
            compileAction cont
              (tmps, ((memIdx, portIdx) :: rqs, rps, wrs, sends)) retVar in
          ((negb (hasRq rqs memIdx portIdx || hasWr wrs memIdx)) && valid, newSt,
            @CReadRqMem (memName, memIdx) (memSize (getMemFromPath x)) (memKind (getMemFromPath x)) (memPort (getMemFromPath x)) i portIdx rest)
    | ReadRpMem s x p cont =>
        fun '(tmps, (rqs, rps, wrs, sends)) retVar =>
          let tmp := (s, length tmps) in
          let memIdx := getPathIndex x.(memPath) in
          let memName := getPathName x.(memPath) in
          let portIdx := finNum p in
          let '(valid, newSt, rest) :=
            compileAction (cont tmp)
              ((s, memKind (getMemFromPath x)) :: tmps,
                (rqs, (memIdx, portIdx) :: rps, wrs, sends)) retVar in
          ((negb (hasRp rps memIdx portIdx || hasRq rqs memIdx portIdx)) && valid, newSt,
            @CReadRpMem (memName, memIdx) (memSize (getMemFromPath x)) (memKind (getMemFromPath x)) (memPort (getMemFromPath x)) portIdx tmp rest)
    | WriteMem x i v cont =>
        fun '(tmps, (rqs, rps, wrs, sends)) retVar =>
          let memIdx := getPathIndex x.(memPath) in
          let memName := getPathName x.(memPath) in
          let '(valid, newSt, rest) :=
            compileAction cont
              (tmps, (rqs, rps, memIdx :: wrs, sends)) retVar in
          ((negb (hasWr wrs memIdx)) && valid, newSt,
            @CWriteMem (memName, memIdx) (memSize (getMemFromPath x)) (memKind (getMemFromPath x)) (memPort (getMemFromPath x)) i v rest)
    | Send x v cont =>
        fun '(tmps, (rqs, rps, wrs, sends)) retVar =>
          let sendIdx := getPathIndex x.(sendPath) in
          let sendName := getPathName x.(sendPath) in
          let '(valid, newSt, rest) :=
            compileAction cont (tmps, (rqs, rps, wrs, sendIdx :: sends)) retVar in
          ((negb (hasSend sends sendIdx)) && valid, newSt, CSend (sendName, sendIdx) v rest)
    | Recv s x cont =>
        fun '(tmps, (rqs, rps, wrs, sends)) retVar =>
          let tmp := (s, length tmps) in
          let recvIdx := getPathIndex x.(recvPath) in
          let recvName := getPathName x.(recvPath) in
          let '(result, newSt, rest) :=
            compileAction (cont tmp)
              ((s, getRecvKind x) :: tmps, (rqs, rps, wrs, sends)) retVar in
          (result, newSt, CRecv (recvName, recvIdx) (getRecvKind x) tmp rest)
    | LetExp s k' v cont =>
        fun '(tmps, (rqs, rps, wrs, sends)) retVar =>
          let tmp := (s, length tmps) in
          let '(result, newSt, rest) :=
            compileAction (cont tmp) ((s, k') :: tmps, (rqs, rps, wrs, sends)) retVar in
          (result, newSt, CLetExpr tmp v rest)
    | LetAction s k' act cont =>
        fun '(tmps, (rqs, rps, wrs, sends)) retVar =>
          let tmp := (s, length tmps) in
          let '(valid1, newCSt1, rest1) :=
            compileAction act ((s, k') :: tmps, (rqs, rps, wrs, sends)) tmp in
          let '(valid, newCSt, rest) := compileAction (cont tmp) newCSt1 retVar in
          (valid1 && valid, newCSt, CLetAction k' rest1 rest)
    | NonDet s k' cont =>
        fun '(tmps, (rqs, rps, wrs, sends)) retVar =>
          let tmp := (s, length tmps) in
          let '(result, newSt, rest) :=
            compileAction (cont tmp) ((s, k') :: tmps, (rqs, rps, wrs, sends)) retVar in
          (result, newSt, CNonDet tmp k' rest)
    | IfElse s p k' t_branch f_branch cont =>
        fun '(tmps, (rqs, rps, wrs, sends)) retVar =>
          let tmp := (s, length tmps) in
          let '(validT, (tmpsT, (rqsT, rpsT, wrsT, sendsT)), restT) :=
            compileAction t_branch ((s, k') :: tmps, (rqs, rps, wrs, sends)) tmp in
          let '(validF, (tmpsF, (rqsF, rpsF, wrsF, sendsF)), restF) :=
            compileAction f_branch (tmpsT, (rqs, rps, wrs, sends)) tmp in
          let '(valid, newCSt, rest) :=
            compileAction (cont tmp)
              (tmpsF, (rqsT ++ rqsF, rpsT ++ rpsF, wrsT ++ wrsF, sendsT ++ sendsF)) retVar in
          (validT && validF && valid, newCSt, CIfElse p k' restT restF rest)
    | System ls cont =>
        fun st retVar =>
          let '(result, newSt, rest) := compileAction cont st retVar in
          (result, newSt, CSys ls rest)
    | Return v =>
        fun st retVar =>
          (true, st, CReturn retVar v)
    end.
End CompileAction.

Section Compile.
  Variable t: Tree ModElem.
  Variable m: Mod t.

  Definition CompiledModule := (Tree ModElem * list (string * Kind) * Compiled)%type.

  Definition compile: option CompiledModule :=
    let retString := "final"%string in
    let initState := ((retString, Bit 0) :: nil, (nil, nil, nil, nil)) in
    let '(valid, (tmps, _), code) :=
      compileAction (combineActions (m (fun k => CTmp))) initState (retString, 0) in
    if valid
    then Some (t, tmps, code)
    else None.
End Compile.
