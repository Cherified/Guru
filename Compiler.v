(*
 * Copyright (c) 2025-2026 Cherified Systems LLC
 *
 * SPDX-License-Identifier: MIT
 *)

From Stdlib Require Import String List ZArith.
From Guru Require Import Library Syntax.

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
| CReadReg (isCross: bool) (x : CReg) (k: Kind) (t: CTmp) (cont: Compiled)
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
               | inl pl => (name ++ "_" ++ @getPathName x pl)%string
               | inr pr => loop xs pr
               end
           end) children
    end.
End TreePathNaming.

Arguments countLeaves [A] t.
Arguments getPathIndex [A] [t] p.
Arguments getPathName [A] [t] p.

Section CompileAction.
  Variable t: Tree DomainElem.

  (* CompileState keeps track of the compilation context:
     - list (string * Kind): Tracks active temporary variables created by let-expressions.
       Their positions in this list determine their unique indices in compiled variables.
     - list (nat * nat): Tracks read-requests (memIdx, portIdx) made in this execution path.
       Used to detect and reject [Write; ReadRq] sequential bypass violations.
     - list (nat * nat): Tracks read-responses (memIdx, portIdx) made in this execution path.
       Used to detect and reject [ReadRq; ReadRp] sequential bypass violations.
     - list nat: Tracks written memory indices (memIdx) in this execution path.
       Used to enforce single-write-per-action memory rules.
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
          (result, newSt, CReadReg (regCross (getRegFromPath x)) (regName, regIdx) (regKind (getRegFromPath x)) tmp rest)
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

Section CdcCheck.
  (* Clock-Domain Crossing (CDC) Invariants verified by `checkCdcMod`:
     1. Cross-register kind & reset (`checkTreeCrossRegs`):
        Every cross register (`regCross = true`) must have kind `Bool` or `Option k`,
        and must be initialized to its default/zero value (`regInit = Some (getDefault k)`).
     2. Domain locality (`domainOk` in `scanActionCdc`):
        Every non-cross register read, every register write (including cross-register writes),
        every memory operation (`ReadRqMem`, `ReadRpMem`, `WriteMem`), every `Send`, and
        every `Recv` in an action must belong to that action's clock domain (`getLeafDomain x = dom`).
        Only a `ReadReg` on a cross register (`regCross = true`) may cross clock domains.
     3. Single-write isolation when writing a cross register (`singleWrOk` & `maxOneWrOk` in `checkActionCdc`):
        An action performs at most 1 unique cross-register write (`length (nub crossWrites) <= 1`).
        Whenever an action writes a cross register, it must perform zero non-cross writes
        (`hasNonCrossWrite = false`: no non-cross `WriteReg`, no `WriteMem`, no `ReadRqMem`, no `Send`).
     4. Single cross-register read per action (`maxOneRdOk` in `checkActionCdc`):
        An action performs at most 1 unique cross-register read (`length (nub crossReads) <= 1`).
     5. No read-and-write of the same cross register in one action (`disjointOk` in `checkActionCdc`):
        No single action both reads and writes the same cross register.
     6. Unique writer action and unique reader action per cross register across the module (`noDupNat` in `checkCdcMod`):
        At most one action across the entire module writes any given cross register, and
        at most one action across the entire module reads any given cross register. *)
  Variable t: Tree DomainElem.
  Local Open Scope bool.

  Definition isValidCrossKind (k : Kind) : bool :=
    match k with
    | Bool => true
    | TaggedUnion (("None"%string, Bit 0) :: ("Some"%string, _) :: nil) => true
    | _ => false
    end.

  Definition isValidCrossInit (r : Reg) : bool :=
    match r.(regInit) with
    | None => false
    | Some init => isEq init (getDefault r.(regKind))
    end.

  Fixpoint checkTreeCrossRegs (tr : Tree DomainElem) : bool :=
    match tr with
    | Leaf _ (_, EReg r) =>
        if r.(regCross)
        then isValidCrossKind r.(regKind) && isValidCrossInit r
        else true
    | Leaf _ _ => true
    | Node _ children =>
        (fix loop (ls : list (Tree DomainElem)) : bool :=
           match ls with
           | nil => true
           | x :: xs => checkTreeCrossRegs x && loop xs
           end) children
    end.

  Fixpoint nubNat (ls : list nat) : list nat :=
    match ls with
    | nil => nil
    | x :: xs =>
        if existsb (Nat.eqb x) xs
        then nubNat xs
        else x :: nubNat xs
    end.

  Fixpoint nubCrossRead (ls : list (string * nat * Kind)) : list (string * nat * Kind) :=
    match ls with
    | nil => nil
    | ((_, idx, _) as x) :: xs =>
        if existsb (fun '(_, idx', _) => idx =? idx') xs
        then nubCrossRead xs
        else x :: nubCrossRead xs
    end.

  Fixpoint noDupNat (ls : list nat) : bool :=
    match ls with
    | nil => true
    | x :: xs => negb (existsb (Nat.eqb x) xs) && noDupNat xs
    end.

  (* scanActionCdc traverses an Action in clock domain `dom` and returns a 4-tuple:
     (domainOk, hasNonCrossWrite, crossWrites, crossReads)
     where:
     - domainOk (bool):
         `true` iff every non-cross register/memory/send/recv accessed by the action
         belongs to `dom`, and every cross-register write (`WriteReg` with `regCross = true`)
         also originates from `dom` (`getLeafDomain x = dom`).
     - hasNonCrossWrite (bool):
         `true` if the action contains any non-cross `WriteReg`, any `WriteMem`,
         any `ReadRqMem`, or any `Send`.
     - crossWrites (list nat):
         List of leaf indices (`getPathIndex`) of cross-domain registers (`regCross = true`)
         written by the action.
     - crossReads (list (string * nat * Kind)):
         List of `(regName, regIdx, regKind)` tuples for every cross-domain register
         read (`ReadReg` with `regCross = true`) in the action. *)
  Fixpoint scanActionCdc (dom : string) {k} (a : @Action (fun _ => unit) t k)
    : (bool * bool * list nat * list (string * nat * Kind)) :=
    match a with
    | ReadReg _ x cont =>
        let r := getRegFromPath x in
        let idx := getPathIndex x.(regPath) in
        let name := getPathName x.(regPath) in
        let ldom := getLeafDomain x.(regPath) in
        let '(ok, ncw, cw, cr) := scanActionCdc dom (cont tt) in
        if r.(regCross)
        then (ok, ncw, cw, (name, idx, r.(regKind)) :: cr)
        else ((String.eqb ldom dom) && ok, ncw, cw, cr)
    | WriteReg x v cont =>
        let r := getRegFromPath x in
        let idx := getPathIndex x.(regPath) in
        let ldom := getLeafDomain x.(regPath) in
        let '(ok, ncw, cw, cr) := scanActionCdc dom cont in
        let ok' := (String.eqb ldom dom) && ok in
        if r.(regCross)
        then (ok', ncw, idx :: cw, cr)
        else (ok', true, cw, cr)
    | ReadRqMem x i p cont =>
        let ldom := getLeafDomain x.(memPath) in
        let '(ok, ncw, cw, cr) := scanActionCdc dom cont in
        ((String.eqb ldom dom) && ok, true, cw, cr)
    | ReadRpMem _ x p cont =>
        let ldom := getLeafDomain x.(memPath) in
        let '(ok, ncw, cw, cr) := scanActionCdc dom (cont tt) in
        ((String.eqb ldom dom) && ok, ncw, cw, cr)
    | WriteMem x i v cont =>
        let ldom := getLeafDomain x.(memPath) in
        let '(ok, ncw, cw, cr) := scanActionCdc dom cont in
        ((String.eqb ldom dom) && ok, true, cw, cr)
    | Send x v cont =>
        let ldom := getLeafDomain x.(sendPath) in
        let '(ok, ncw, cw, cr) := scanActionCdc dom cont in
        ((String.eqb ldom dom) && ok, true, cw, cr)
    | Recv _ x cont =>
        let ldom := getLeafDomain x.(recvPath) in
        let '(ok, ncw, cw, cr) := scanActionCdc dom (cont tt) in
        ((String.eqb ldom dom) && ok, ncw, cw, cr)
    | LetExp _ _ _ cont =>
        scanActionCdc dom (cont tt)
    | LetAction _ _ a1 cont =>
        let '(ok1, ncw1, cw1, cr1) := scanActionCdc dom a1 in
        let '(ok2, ncw2, cw2, cr2) := scanActionCdc dom (cont tt) in
        (ok1 && ok2, ncw1 || ncw2, cw1 ++ cw2, cr1 ++ cr2)
    | NonDet _ _ cont =>
        scanActionCdc dom (cont tt)
    | IfElse _ _ _ t_b f_b cont =>
        let '(okT, ncwT, cwT, crT) := scanActionCdc dom t_b in
        let '(okF, ncwF, cwF, crF) := scanActionCdc dom f_b in
        let '(okC, ncwC, cwC, crC) := scanActionCdc dom (cont tt) in
        (okT && okF && okC, ncwT || ncwF || ncwC, cwT ++ cwF ++ cwC, crT ++ crF ++ crC)
    | System _ cont =>
        scanActionCdc dom cont
    | Return _ =>
        (true, false, nil, nil)
    end.

  Definition checkActionCdc (dom : string) (a : @Action (fun _ => unit) t (Bit 0))
    : (bool * list nat * list (string * nat * Kind)) :=
    let '(domOk, hasNonCrossWrite, rawCw, rawCr) := scanActionCdc dom a in
    let cw := nubNat rawCw in
    let cr := nubCrossRead rawCr in
    let maxOneWrOk := length cw <=? 1 in
    let maxOneRdOk := length cr <=? 1 in
    let singleWrOk :=
      match cw with
      | nil => true
      | _ :: _ => negb hasNonCrossWrite
      end in
    let disjointOk :=
      match cw, cr with
      | wIdx :: _, (_, rIdx, _) :: _ => negb (wIdx =? rIdx)
      | _, _ => true
      end in
    (domOk && maxOneWrOk && maxOneRdOk && singleWrOk && disjointOk, cw, cr).

  Fixpoint checkActionsCdc (ls : list (string * @Action (fun _ => unit) t (Bit 0)))
    : (bool * list nat * list (string * nat * Kind * string)) :=
    match ls with
    | nil => (true, nil, nil)
    | (dom, a) :: rest =>
        let '(ok1, cw, cr) := checkActionCdc dom a in
        let '(ok2, restCw, restCr) := checkActionsCdc rest in
        let cr' :=
          match cr with
          | (rName, rIdx, rKind) :: _ => (rName, rIdx, rKind, dom) :: restCr
          | nil => restCr
          end in
        (ok1 && ok2, cw ++ restCw, cr')
    end.

  Definition checkCdcMod (ls : list (string * @Action (fun _ => unit) t (Bit 0)))
    : (bool * list (string * nat * Kind * string)) :=
    let '(actionsOk, modCrossWrites, modCrossReads) := checkActionsCdc ls in
    (checkTreeCrossRegs t &&
     actionsOk &&
     noDupNat modCrossWrites &&
     noDupNat (map (fun '(_, idx, _, _) => idx) modCrossReads),
     modCrossReads).
End CdcCheck.

Fixpoint addToDomainGroup {A} (dom : string) (a : A) (groups : list (string * list A)) : list (string * list A) :=
  match groups with
  | nil => (dom, a :: nil) :: nil
  | (d, acts) :: rest =>
      if String.eqb dom d
      then (d, a :: acts) :: rest
      else (d, acts) :: addToDomainGroup dom a rest
  end.

Definition groupActionsByDomain {A} (ls : list (string * A)) : list (string * list A) :=
  map (fun '(d, acts) => (d, rev_append acts nil))
      (fold_left (fun acc '(dom, a) => addToDomainGroup dom a acc) ls nil).

Section Compile.
  Variable t: Tree DomainElem.
  Variable m: Mod t.
  Local Open Scope bool.

  Definition CompiledModule :=
    (Tree DomainElem *
     list (string * nat * Kind * string) *
     list (list (string * Kind) * Compiled * string))%type.

  Fixpoint compileDomains (groups : list (string * list (@Action (fun k => CTmp) t (Bit 0))))
    : (bool * list (list (string * Kind) * Compiled * string)) :=
    match groups with
    | nil => (true, nil)
    | (d, acts) :: rest =>
        let retString := "final"%string in
        let initState := ((retString, Bit 0) :: nil, (nil, nil, nil, nil)) in
        let combAct := combineActions acts in
        let '(valid, (tmpsDom, _), code) :=
          compileAction combAct initState (retString, 0) in
        let '(validRest, codesRest) :=
          compileDomains rest in
        (valid && validRest, (tmpsDom, code, d) :: codesRest)
    end.

  Definition compile: option CompiledModule :=
    let '(cdcOk, crossReads) := checkCdcMod (m (fun _ => unit)) in
    let groups := groupActionsByDomain (m (fun k => CTmp)) in
    let '(valid, codes) := compileDomains groups in
    if cdcOk && valid
    then Some (t, crossReads, codes)
    else None.
End Compile.
