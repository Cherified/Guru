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
| CReadRqMem (x: CMem) (k: Kind) sz (i: CExpr (Bit (Z.log2_up (Z.of_nat sz)))) (p: nat) (cont: Compiled)
| CReadRpMem (x: CMem) (p: nat) (k: Kind) (sz: nat) (t: CTmp) (cont: Compiled)
| CWriteMem (x: CMem) sz (i: CExpr (Bit (Z.log2_up (Z.of_nat sz)))) k (v: CExpr k) (ports: nat) (cont: Compiled)
| CReadRegU (x : CReg) (k: Kind) (t: CTmp) (cont: Compiled)
| CWriteRegU (x : CReg) k (e: CExpr k) (cont: Compiled)
| CReadRqMemU (x: CMem) (k: Kind) sz (i: CExpr (Bit (Z.log2_up (Z.of_nat sz)))) (p: nat) (cont: Compiled)
| CReadRpMemU (x: CMem) (p: nat) (k: Kind) (sz: nat) (t: CTmp) (cont: Compiled)
| CWriteMemU (x: CMem) sz (i: CExpr (Bit (Z.log2_up (Z.of_nat sz)))) k (v: CExpr k) (ports: nat) (cont: Compiled)
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
Section MemCalls.
  Variable ls: list (string * MemU).
  Definition MemCalls := DiffTuple (fun x => (bool * (SameTuple (bool * bool) (snd x).(memUPort)))%type) ls.
  Variable portCalls: MemCalls.
  Definition memCallsAddRq x p := updDiffTuple portCalls (let (write, rqRps) := readDiffTuple portCalls x in
                                                          let (rq, rp) := readSameTuple rqRps p in
                                                          (write, updSameTuple rqRps p (true, rp))).
  Definition memCallsAddRp x p := updDiffTuple portCalls (let (write, rqRps) := readDiffTuple portCalls x in
                                                          let (rq, rp) := readSameTuple rqRps p in
                                                          (write, updSameTuple rqRps p (rq, true))).
  Definition memCallsAddWr x := updDiffTuple portCalls (let (write, rqRps) := readDiffTuple portCalls x in
                                                        (true, rqRps)).
  Definition memCallsHasRq x p := fst (readSameTuple (snd (readDiffTuple portCalls x)) p).
  Definition memCallsHasRp x p := snd (readSameTuple (snd (readDiffTuple portCalls x)) p).
  Definition memCallsHasWr x := fst (readDiffTuple portCalls x).
End MemCalls.

Section UnionMemCalls.
  Variable ls: list (string * MemU).
  Variable p1 p2: MemCalls ls.
  Local Open Scope bool.
  Definition unionMemCalls : MemCalls ls :=
    combineDiffTuple
      (fun _ '(w1, arr1) '(w2, arr2) =>
         (w1 || w2, combineSameTuple (fun '(x1, y1) '(x2, y2) => (x1 || x2, y1 || y2)) arr1 arr2)) p1 p2.
End UnionMemCalls.

Section CompileAction.
  Variable modLists: ModLists.

  Definition CompileState :=
    (list (string * Kind) * (* List of LET names and Kinds. List position determines the full name *)
       MemCalls (mmems modLists) *
       MemCalls (mmemUs modLists))%type.

  Local Open Scope bool.

  Fixpoint compileAction k (a: @Action (fun k => CTmp) modLists k):
    CompileState -> CTmp ->
    (bool * ((DiffTuple (fun _ => bool) modLists.(msends)) (* Keeps track of which sends are called in the cont *) *
               CompileState) * Compiled) :=
    match a return CompileState -> CTmp ->
                   (bool * ((DiffTuple (fun _ => bool) modLists.(msends) * CompileState)) * Compiled)
    with
    | ReadReg s x cont =>
        fun '(tmps, memCalls, memUCalls) retVar =>
          let tmp := (s, length tmps) in
          let (result, rest) :=
            compileAction (cont tmp)
              ((s, fieldK x) :: tmps, memCalls, memUCalls) retVar in
          (result, CReadReg (fieldName x, x.(finNum)) (fieldK x) tmp rest)
    | WriteReg x v cont =>
        fun '(tmps, memCalls, memUCalls) retVar =>
          let (result, rest) :=
            compileAction cont
              (tmps, memCalls, memUCalls) retVar in
          (result, CWriteReg (fieldName x, x.(finNum)) v rest)
    | ReadRqMem x i p cont =>
        fun '(tmps, memCalls, memUCalls) retVar =>
          let '(valid, newSt, rest) :=
            compileAction cont
              (tmps, memCallsAddRq memCalls p, memUCalls) retVar in
          (* [Write; ReadRq] is not allowed *)
          ((negb (memCallsHasRq memCalls p || memCallsHasWr memCalls x)) && valid, newSt,
            CReadRqMem (fieldName x, x.(finNum)) (memUKind (fieldK x)) i p.(finNum) rest)
    | ReadRpMem s x p cont =>
        fun '(tmps, memCalls, memUCalls) retVar =>
          let tmp := (s, length tmps) in
          let '((valid, newSt), rest) :=
            compileAction (cont tmp)
              ((s, memUKind (fieldK x)) :: tmps,
                memCallsAddRp memCalls p, memUCalls) retVar in
          (* [ReadRq; ReadRp] is not allowed *)
          ((negb (memCallsHasRp memCalls p || memCallsHasRq memCalls p)) && valid, newSt,
            CReadRpMem (fieldName x, x.(finNum)) p.(finNum) (memUKind (fieldK x))
              (memUSize (fieldK x)) tmp rest)
    | WriteMem x i v cont =>
        fun '(tmps, memCalls, memUCalls) retVar =>
          let '((valid, newSt), rest) :=
            compileAction cont
              (tmps,  memCallsAddWr memCalls x, memUCalls) retVar in
          ((negb (memCallsHasWr memCalls x)) && valid, newSt,
            CWriteMem (fieldName x, x.(finNum)) i v (memUPort (fieldK x)) rest)
    | ReadRegU s x cont =>
        fun '(tmps, memCalls, memUCalls) retVar =>
          let tmp := (s, length tmps) in
          let (result, rest) :=
            compileAction (cont tmp)
              ((s, fieldK x) :: tmps, memCalls, memUCalls) retVar in
          (result, CReadRegU (fieldName x, x.(finNum)) (fieldK x) tmp rest)
    | WriteRegU x v cont =>
        fun '(tmps, memCalls, memUCalls) retVar =>
          let (result, rest) :=
            compileAction cont
              (tmps, memCalls, memUCalls) retVar in
          (result, CWriteRegU (fieldName x, x.(finNum)) v rest)
    | ReadRqMemU x i p cont =>
        fun '(tmps, memCalls, memUCalls) retVar =>
          let '((valid, newSt), rest) :=
            compileAction cont
              (tmps, memCalls, memCallsAddRq memUCalls p) retVar in
          (* [Write; ReadRq] is not allowed *)
          ((negb (memCallsHasRq memUCalls p || memCallsHasWr memUCalls x)) && valid, newSt,
            CReadRqMemU (fieldName x, x.(finNum)) (memUKind (fieldK x)) i p.(finNum) rest)
    | ReadRpMemU s x p cont =>
        fun '(tmps, memCalls, memUCalls) retVar =>
          let tmp := (s, length tmps) in
          let '((valid, newSt), rest) :=
            compileAction (cont tmp)
              ((s, memUKind (fieldK x)) :: tmps, memCalls,
                memCallsAddRp memUCalls p) retVar in
          (* [ReadRq; ReadRp] is not allowed *)
          ((negb (memCallsHasRp memUCalls p || memCallsHasRq memUCalls p)) && valid, newSt,
            CReadRpMemU (fieldName x, x.(finNum)) p.(finNum) (memUKind (fieldK x))
              (memUSize (fieldK x)) tmp rest)
    | WriteMemU x i v cont =>
        fun '(tmps, memCalls, memUCalls) retVar =>
          let '((valid, newSt), rest) :=
            compileAction cont
              (tmps,  memCalls, memCallsAddWr memUCalls x) retVar in
          ((negb (memCallsHasWr memUCalls x)) && valid, newSt,
            CWriteMemU (fieldName x, x.(finNum)) i v (memUPort (fieldK x)) rest)
    | Send x v cont =>
        fun '(tmps, memCalls, memUCalls) retVar =>
          let '((valid, (sends, newCSt)), rest) :=
            compileAction cont (tmps, memCalls, memUCalls) retVar in
          (negb (readDiffTuple sends x) && valid, (updDiffTuple sends (p := x) true, newCSt),
            CSend (fieldName x, x.(finNum)) v rest)
    | Recv s x cont =>
        fun '(tmps, memCalls, memUCalls) retVar =>
          let tmp := (s, length tmps) in          
          let (result, rest) :=
            compileAction (cont tmp) ((s, fieldK x) :: tmps, memCalls, memUCalls) retVar in
          (result, CRecv (fieldName x, x.(finNum)) (fieldK x) tmp rest)
    | LetExp s k' v cont =>
        fun '(tmps, memCalls, memUCalls) retVar =>
          let tmp := (s, length tmps) in          
          let (result, rest) :=
            compileAction (cont tmp) ((s, k') :: tmps, memCalls, memUCalls) retVar in
          (result, CLetExpr tmp v rest)
    | LetAction s k' act cont =>
        fun '(tmps, memCalls, memUCalls) retVar =>
          let tmp := (s, length tmps) in          
          let '(valid1, (sends1, newCSt1), rest1) :=
            compileAction act ((s, k') :: tmps, memCalls, memUCalls) tmp in
          let '(valid, (sends, newCSt), rest) := compileAction (cont tmp) newCSt1 retVar in
          (valid1 && valid && negb (foldDiffTuple orb false (combineDiffTuple (fun _ => andb) sends1 sends)),
            (combineDiffTuple (fun _ => orb) sends1 sends, newCSt), CLetAction k' rest1 rest)
    | NonDet s k' cont =>
        fun '(tmps, memCalls, memUCalls) retVar =>
          let tmp := (s, length tmps) in          
          let (result, rest) :=
            compileAction (cont tmp) ((s, k') :: tmps, memCalls, memUCalls) retVar in
          (result, CNonDet tmp k' rest)
    | IfElse s p k' t f cont =>
        fun '(tmps, memCalls, memUCalls) retVar =>
          let tmp := (s, length tmps) in          
          let '(validT, (sendsT, (tmpsT, memCallsT, memUCallsT)), restT) :=
            compileAction t ((s, k') :: tmps, memCalls, memUCalls) tmp in
          let '(validF, (sendsF, (tmpsF, memCallsF, memUCallsF)), restF) :=
            compileAction f (tmpsT, memCalls, memUCalls) tmp in
          let '(valid, (sends, newCSt), rest) :=
            compileAction (cont tmp)
              (tmpsF, unionMemCalls memCallsT memCallsF, unionMemCalls memUCallsT memUCallsF) retVar in
          (validT && validF && valid &&
             negb (foldDiffTuple orb false (combineDiffTuple (fun _ => andb)
                                              (combineDiffTuple (fun _ => orb) sendsT sendsF) sends)),
            (combineDiffTuple (fun _ => orb) sends sends, newCSt), CIfElse p k' restT restF rest)
    | System ls cont =>
        fun st retVar =>
          let (result, rest) := compileAction cont st retVar in
          (result, CSys ls rest)
    | Return v =>
        fun st retVar =>
          (true, (defaultDiffTuple (fun _ => false) modLists.(msends), st), CReturn retVar v)
    end.
End CompileAction.

Section Compile.
  Variable m: Mod.

  Local Definition noMemCalls ls: MemCalls ls :=
    defaultDiffTuple (fun _ => (false, SameTupleDefault (false, false) _)) ls.

  Definition CompiledModule := (ModDecl *
                                  list (string * Kind) *
                                  Compiled)%type.

  Definition compile: option CompiledModule :=
    let retString := "final"%string in
    let initState := ((retString, Bit 0) :: nil, @noMemCalls _, @noMemCalls _) in
    let '(valid, (_, (tmps, _, _)), code) :=
      compileAction (combineActions (modActions m (fun k => CTmp))) initState (retString, 0) in
    if valid
    then Some (modDecl m, tmps, code)
    else None.
End Compile.

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

Section CompileActionTree.
  Variable t: Tree ModStateElem.

  (* CompileStateTree keeps track of the compilation context:
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
  Definition CompileStateTree :=
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

  (* compileActionTree compiles a given ActionTree into a Compiled program syntax tree:
     - CTmp argument (retVar): Represents the target temporary variable where the final return value
       of this action will be stored (eventually compiled into a CReturn statement).
     - Returns: A tuple of type:
       (bool * CompileStateTree * Compiled)
       where:
       - bool: Represents the compilation validity flag (returns 'false' if any bypass or write violations occur).
       - CompileStateTree: The updated CompileStateTree, defined as above.
       - Compiled: The structured compiled program syntax tree representing the compiled output. *)
  Fixpoint compileActionTree k (a: @ActionTree (fun k => CTmp) t k):
    CompileStateTree -> CTmp ->
    (bool * CompileStateTree * Compiled) :=
    match a return CompileStateTree -> CTmp ->
                   (bool * CompileStateTree * Compiled)
    with
    | ReadRegTree s x cont =>
        fun '(tmps, (rqs, rps, wrs, sends)) retVar =>
          let tmp := (s, length tmps) in
          let regIdx := getPathIndex x.(regPath) in
          let regName := getPathName x.(regPath) in
          let '(result, newSt, rest) :=
            compileActionTree (cont tmp)
              ((s, registerKind (getRegFromPath x)) :: tmps, (rqs, rps, wrs, sends)) retVar in
          (result, newSt, CReadReg (regName, regIdx) (registerKind (getRegFromPath x)) tmp rest)
    | WriteRegTree x v cont =>
        fun '(tmps, (rqs, rps, wrs, sends)) retVar =>
          let regIdx := getPathIndex x.(regPath) in
          let regName := getPathName x.(regPath) in
          let '(result, newSt, rest) :=
            compileActionTree cont
              (tmps, (rqs, rps, wrs, sends)) retVar in
          (result, newSt, CWriteReg (regName, regIdx) v rest)
    | ReadRqMemTree x i p cont =>
        fun '(tmps, (rqs, rps, wrs, sends)) retVar =>
          let memIdx := getPathIndex x.(memPath) in
          let memName := getPathName x.(memPath) in
          let portIdx := finNum p in
          let '(valid, newSt, rest) :=
            compileActionTree cont
              (tmps, ((memIdx, portIdx) :: rqs, rps, wrs, sends)) retVar in
          ((negb (hasRq rqs memIdx portIdx || hasWr wrs memIdx)) && valid, newSt,
            CReadRqMem (memName, memIdx) (memoryKind (getMemFromPath x)) i portIdx rest)
    | ReadRpMemTree s x p cont =>
        fun '(tmps, (rqs, rps, wrs, sends)) retVar =>
          let tmp := (s, length tmps) in
          let memIdx := getPathIndex x.(memPath) in
          let memName := getPathName x.(memPath) in
          let portIdx := finNum p in
          let '(valid, newSt, rest) :=
            compileActionTree (cont tmp)
              ((s, memoryKind (getMemFromPath x)) :: tmps,
                (rqs, (memIdx, portIdx) :: rps, wrs, sends)) retVar in
          ((negb (hasRp rps memIdx portIdx || hasRq rqs memIdx portIdx)) && valid, newSt,
            CReadRpMem (memName, memIdx) portIdx (memoryKind (getMemFromPath x))
              (memorySize (getMemFromPath x)) tmp rest)
    | WriteMemTree x i v cont =>
        fun '(tmps, (rqs, rps, wrs, sends)) retVar =>
          let memIdx := getPathIndex x.(memPath) in
          let memName := getPathName x.(memPath) in
          let '(valid, newSt, rest) :=
            compileActionTree cont
              (tmps, (rqs, rps, memIdx :: wrs, sends)) retVar in
          ((negb (hasWr wrs memIdx)) && valid, newSt,
            CWriteMem (memName, memIdx) i v (memoryPort (getMemFromPath x)) rest)
    | SendTree x v cont =>
        fun '(tmps, (rqs, rps, wrs, sends)) retVar =>
          let sendIdx := getPathIndex x.(sendPath) in
          let sendName := getPathName x.(sendPath) in
          let '(valid, newSt, rest) :=
            compileActionTree cont (tmps, (rqs, rps, wrs, sendIdx :: sends)) retVar in
          ((negb (hasSend sends sendIdx)) && valid, newSt, CSend (sendName, sendIdx) v rest)
    | RecvTree s x cont =>
        fun '(tmps, (rqs, rps, wrs, sends)) retVar =>
          let tmp := (s, length tmps) in
          let recvIdx := getPathIndex x.(recvPath) in
          let recvName := getPathName x.(recvPath) in
          let '(result, newSt, rest) :=
            compileActionTree (cont tmp)
              ((s, getRecvKind x) :: tmps, (rqs, rps, wrs, sends)) retVar in
          (result, newSt, CRecv (recvName, recvIdx) (getRecvKind x) tmp rest)
    | LetExpTree s k' v cont =>
        fun '(tmps, (rqs, rps, wrs, sends)) retVar =>
          let tmp := (s, length tmps) in
          let '(result, newSt, rest) :=
            compileActionTree (cont tmp) ((s, k') :: tmps, (rqs, rps, wrs, sends)) retVar in
          (result, newSt, CLetExpr tmp v rest)
    | LetActionTree s k' act cont =>
        fun '(tmps, (rqs, rps, wrs, sends)) retVar =>
          let tmp := (s, length tmps) in
          let '(valid1, newCSt1, rest1) :=
            compileActionTree act ((s, k') :: tmps, (rqs, rps, wrs, sends)) tmp in
          let '(valid, newCSt, rest) := compileActionTree (cont tmp) newCSt1 retVar in
          (valid1 && valid, newCSt, CLetAction k' rest1 rest)
    | NonDetTree s k' cont =>
        fun '(tmps, (rqs, rps, wrs, sends)) retVar =>
          let tmp := (s, length tmps) in
          let '(result, newSt, rest) :=
            compileActionTree (cont tmp) ((s, k') :: tmps, (rqs, rps, wrs, sends)) retVar in
          (result, newSt, CNonDet tmp k' rest)
    | IfElseTree s p k' t_branch f_branch cont =>
        fun '(tmps, (rqs, rps, wrs, sends)) retVar =>
          let tmp := (s, length tmps) in
          let '(validT, (tmpsT, (rqsT, rpsT, wrsT, sendsT)), restT) :=
            compileActionTree t_branch ((s, k') :: tmps, (rqs, rps, wrs, sends)) tmp in
          let '(validF, (tmpsF, (rqsF, rpsF, wrsF, sendsF)), restF) :=
            compileActionTree f_branch (tmpsT, (rqs, rps, wrs, sends)) tmp in
          let '(valid, newCSt, rest) :=
            compileActionTree (cont tmp)
              (tmpsF, (rqsT ++ rqsF, rpsT ++ rpsF, wrsT ++ wrsF, sendsT ++ sendsF)) retVar in
          (validT && validF && valid, newCSt, CIfElse p k' restT restF rest)
    | SystemTree ls cont =>
        fun st retVar =>
          let '(result, newSt, rest) := compileActionTree cont st retVar in
          (result, newSt, CSys ls rest)
    | ReturnTree v =>
        fun st retVar =>
          (true, st, CReturn retVar v)
    end.
End CompileActionTree.

Section CompileTree.
  Variable t: Tree ModStateElem.
  Variable m: ModTree t.

  Definition CompiledModuleTree := (Tree ModStateElem * list (string * Kind) * Compiled)%type.

  Definition compileTree: option CompiledModuleTree :=
    let retString := "final"%string in
    let initState := ((retString, Bit 0) :: nil, (nil, nil, nil, nil)) in
    let '(valid, (tmps, _), code) :=
      compileActionTree (combineActionsTree (m (fun k => CTmp))) initState (retString, 0) in
    if valid
    then Some (t, tmps, code)
    else None.
End CompileTree.
