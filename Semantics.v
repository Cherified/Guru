From Stdlib Require Import String List Psatz Zmod Bool.
Require Import Guru.Library Guru.Syntax.

Set Implicit Arguments.
Set Asymmetric Patterns.

Axiom cheat: forall t, t.

#[bypass_check(guard)]
Fixpoint evalExpr k (e: Expr type k) {struct e}: type k :=
  match e in Expr _ k return type k with
  | Var _ v => v
  | Const _ v => v
  | Or _ ls => fold_left (@evalOrBinary _) (map (@evalExpr _) ls) (Default _)
  | And ls => fold_left andb (map (@evalExpr Bool) ls) true
  | Xor ls => fold_left xorb (map (@evalExpr Bool) ls) false
  | Not v => negb (@evalExpr _ v)
  | Inv _ v => Zmod.not (@evalExpr _ v)
  | TruncLsb _ _ v => Zmod_lastn _ (@evalExpr _ v)
  | TruncMsb _ _ v => Zmod.firstn _ (@evalExpr _ v)
  | UXor n v => Z_uxor (Zmod.to_Z (@evalExpr _ v))
  | Add n ls => fold_left Zmod.add (map (@evalExpr (Bit n)) ls) Zmod.zero
  | Mul n ls => fold_left Zmod.mul (map (@evalExpr (Bit n)) ls) Zmod.one
  | Band n ls => fold_left Zmod.and (map (@evalExpr (Bit n)) ls) (bits.of_Z _ (-1))
  | Bxor n ls => fold_left Zmod.or (map (@evalExpr (Bit n)) ls) Zmod.zero
  | Div n a b => Zmod.udiv (@evalExpr _ a) (@evalExpr _ b)
  | Rem n a b => Zmod.umod (@evalExpr _ a) (@evalExpr _ b)
  | Sll _ _ a b => Zmod.slu (@evalExpr _ a) (Zmod.to_Z (@evalExpr _ b))
  | Srl _ _ a b => Zmod.sru (@evalExpr _ a) (Zmod.to_Z (@evalExpr _ b))
  | Sra _ _ a b => Zmod.srs (@evalExpr _ a) (Zmod.to_Z (@evalExpr _ b))
  | Concat _ _ a b => Zmod.app (@evalExpr _ b) (@evalExpr _ a)
  | ITE _ p t f => if @evalExpr _ p then @evalExpr _ t else @evalExpr _ f
  | Eq _ a b => isEq (@evalExpr _ a) (@evalExpr _ b)
  | ReadStruct _ v i => readDiffTuple (Convert := fun x => type (snd x)) (@evalExpr _ v) i
  | ReadArray n _ k v i =>
      readNatToFinType (Default _) (readSameTuple (@evalExpr _ v)) (Z.to_nat (Zmod.to_Z (@evalExpr _ i)))
  | ReadArrayConst _ _ v i => readSameTuple (@evalExpr _ v) i
  | UpdateStruct ls vs p v => updDiffTuple (Convert := fun x => type (snd x)) (@evalExpr _ vs) (@evalExpr _ v)
  | UpdateArrayConst n k vs p v => updSameTuple (@evalExpr _ vs) p (@evalExpr _ v)
  | UpdateArray n k vs m i v =>
      updSameTupleNat (@evalExpr _ vs) (Z.to_nat (Zmod.to_Z (@evalExpr _ i))) (@evalExpr _ v)
  | ToBit _ v => evalToBit (@evalExpr _ v)
  | FromBit _ v => evalFromBit (@evalExpr _ v)
  (* The following 2 don't pass the guardedness checks in Rocq *)
  | BuildStruct ls vs => mapDiffTuple (fun x => @evalExpr (snd x)) vs
  | BuildArray n k vs => mapSameTuple (@evalExpr k) vs
  end.

Fixpoint evalLetExpr k (le: LetExpr type k): type k :=
  match le with
  | RetE e => evalExpr e
  | SystemE ls cont => evalLetExpr cont
  | LetEx s k' le cont => let t := evalLetExpr le in evalLetExpr (cont t)
  | IfElseE s p k' t f cont => evalLetExpr (cont (if evalExpr p
                                                  then evalLetExpr t
                                                  else evalLetExpr f))
  end.

Definition FuncState (ls: list (string * Kind)) := DiffTuple (fun x => type (snd x)) ls.
Definition FuncMemState (ls: list (string * MemU)) :=
  DiffTuple (fun x => (type (Array (snd x).(memUSize) (snd x).(memUKind)) *
                         type (Array (snd x).(memUPort) (snd x).(memUKind))))%type ls.
Definition FuncIo (ls: list (string * Kind)) := DiffTuple (fun x => list (type (snd x))) ls.

#[projections(primitive)]
Record ModState regs mems regUs memUs :=
  { stateRegs  : FuncState regs;
    stateMems  : FuncMemState mems;
    stateRegUs : FuncState regUs;
    stateMemUs : FuncMemState memUs}.

Section SemAction.
  Variable modLists: ModLists.

  Inductive SemAction k: Action type modLists k ->
                         ModState modLists.(mregs) modLists.(mmems) modLists.(mregUs) modLists.(mmemUs) ->
                         ModState modLists.(mregs) modLists.(mmems) modLists.(mregUs) modLists.(mmemUs) ->
                         FuncIo modLists.(msends) ->
                         FuncIo modLists.(mrecvs) ->
                         type k -> Prop :=
  | SemReadReg s x cont old new puts gets ret
      (contPf: SemAction (cont (readDiffTuple old.(stateRegs) x)) old new puts gets ret):
    SemAction (ReadReg s x cont) old new puts gets ret
  | SemWriteReg x (v: Expr type (fieldK x)) cont old new puts gets ret
      (contPf: SemAction cont {|stateRegs := updDiffTuple old.(stateRegs) (evalExpr v);
                                stateMems := old.(stateMems);
                                stateRegUs := old.(stateRegUs);
                                stateMemUs := old.(stateMemUs)|} new puts gets ret):
    SemAction (WriteReg x v cont) old new puts gets ret
  | SemReadRqMem x (i: Expr type (Bit (Z.log2_up (Z.of_nat ((fieldK x).(memUSize)))))) p cont old new puts gets ret
      (contPf:
        SemAction
          cont
          {|stateRegs := old.(stateRegs);
            stateMems := let arr := readDiffTuple old.(stateMems) x in
                         updDiffTuple (old.(stateMems))
                           (fst arr, updSameTuple (snd arr) p (readNatToFinType (Default _) (readSameTuple (fst arr))
                                                                 (Z.to_nat (Zmod.to_Z (evalExpr i)))));
            stateRegUs := old.(stateRegUs);
            stateMemUs := old.(stateMemUs)|} new puts gets ret):
    SemAction (ReadRqMem x i p cont) old new puts gets ret
  | SemReadRpMem s x p cont old new puts gets ret
      (contPf: SemAction (cont (readSameTuple (snd (readDiffTuple old.(stateMems) x)) p)) old new puts gets ret):
      SemAction (ReadRpMem s x p cont) old new puts gets ret
  | SemWriteMem x (i: Expr type (Bit (Z.log2_up (Z.of_nat (fieldK x).(memUSize))))) v cont old new puts gets ret
      (contPf:
        SemAction
          cont
          {|stateRegs := old.(stateRegs);
            stateMems :=
              let arr := readDiffTuple old.(stateMems) x in
              updDiffTuple (old.(stateMems))
                (updSameTupleNat (fst arr) (Z.to_nat (Zmod.to_Z (@evalExpr _ i))) (evalExpr v), snd arr);
            stateRegUs := old.(stateRegUs);
            stateMemUs := old.(stateMemUs)|} new puts gets ret):
    SemAction (WriteMem x i v cont) old new puts gets ret
  | SemReadRegU s x cont old new puts gets ret
      (contPf: SemAction (cont (readDiffTuple old.(stateRegUs) x)) old new puts gets ret):
    SemAction (ReadRegU s x cont) old new puts gets ret
  | SemWriteRegU x (v: Expr type (fieldK x)) cont old new puts gets ret
      (contPf: SemAction cont {|stateRegs := old.(stateRegs);
                                stateMems := old.(stateMems);
                                stateRegUs := updDiffTuple old.(stateRegUs) (evalExpr v);
                                stateMemUs := stateMemUs old|} new puts gets ret):
    SemAction (WriteRegU x v cont) old new puts gets ret
  | SemReadRqMemU x (i: Expr type (Bit (Z.log2_up (Z.of_nat (fieldK x).(memUSize))))) p cont old new puts gets ret
      (contPf:
        SemAction
          cont
          {|stateRegs := old.(stateRegs);
            stateMems := old.(stateMems);
            stateRegUs := old.(stateRegUs);
            stateMemUs := let arr := readDiffTuple old.(stateMemUs) x in
                          updDiffTuple (old.(stateMemUs))
                            (fst arr, updSameTuple (snd arr) p (readNatToFinType (Default _) (readSameTuple (fst arr))
                                                                  (Z.to_nat (Zmod.to_Z (evalExpr i)))))|}
          new puts gets ret):
      SemAction (ReadRqMemU x i p cont) old new puts gets ret
  | SemReadRpMemU s x p cont old new puts gets ret
      (contPf: SemAction (cont (readSameTuple (snd (readDiffTuple old.(stateMemUs) x)) p)) old new puts gets ret):
      SemAction (ReadRpMemU s x p cont) old new puts gets ret
  | SemWriteMemU x (i: Expr type (Bit (Z.log2_up (Z.of_nat (fieldK x).(memUSize))))) v cont old new puts gets ret
      (contPf:
        SemAction
          cont
          {|stateRegs := old.(stateRegs);
            stateMems := old.(stateMems);
            stateRegUs := old.(stateRegUs);
            stateMemUs :=
              let arr := readDiffTuple old.(stateMemUs) x in
              updDiffTuple (old.(stateMemUs))
                (updSameTupleNat (fst arr) (Z.to_nat (Zmod.to_Z (@evalExpr _ i))) (evalExpr v), snd arr)|}
          new puts gets ret):
    SemAction (WriteMemU x i v cont) old new puts gets ret
  | SemSend x v cont old new puts gets ret
      putsStep
      (contPf: SemAction cont old new putsStep gets ret)
      (putsVal: puts = updDiffTuple putsStep (evalExpr v :: readDiffTuple putsStep x)):
      SemAction (Send x v cont) old new puts gets ret
  | SemRecv s x cont old new puts gets ret
      recvStep getsStep
      (contPf: SemAction (cont recvStep) old new puts getsStep ret)
      (putsVal: gets = updDiffTuple getsStep (recvStep :: readDiffTuple getsStep x)):
      SemAction (Recv s x cont) old new puts gets ret
  | SemLetExp s k' (e: Expr type k') cont old new puts gets ret
      (contPf: SemAction (cont (evalExpr e)) old new puts gets ret):
    SemAction (LetExp s e cont) old new puts gets ret
  | SemLetAction s k' a cont old new puts gets ret
      newStep putsStep getsStep (retStep: type k') interPuts interGets
      (aPf: SemAction a old newStep putsStep getsStep retStep)
      (contPf: SemAction (cont retStep) newStep new interPuts interGets ret)
      (interPutsEq: puts = combineDiffTuple (fun _ => @List.app _) putsStep interPuts)
      (interGetsEq: gets = combineDiffTuple (fun _ => @List.app _) getsStep interGets):
    SemAction (LetAction s a cont) old new puts gets ret
  | SemNonDet s k' cont old new puts gets ret v
      (contPf: SemAction (cont v) old new puts gets ret):
    SemAction (NonDet s k' cont) old new puts gets ret
  | SemIfElse s (p: Expr type Bool) k' t f cont old new puts gets ret
      newStep putsStep getsStep (retStep: type k') interPuts interGets
      (tPf: evalExpr p = true -> SemAction t old newStep putsStep getsStep retStep)
      (fPf: evalExpr p = false -> SemAction f old newStep putsStep getsStep retStep)
      (contPf: SemAction (cont retStep) newStep new interPuts interGets ret)
      (interPutsEq: puts = combineDiffTuple (fun _ => @List.app _) putsStep interPuts)
      (interGetsEq: gets = combineDiffTuple (fun _ => @List.app _) getsStep interGets):
    SemAction (IfElse s p t f cont) old new puts gets ret
  | SemSystem ls cont old new puts gets ret
      (contPf: SemAction cont old new puts gets ret): SemAction (System ls cont) old new puts gets ret
  | SemReturn e old new puts gets ret
      (oldIsNew: new = old)
      (putsEmpty: puts = defaultDiffTuple (fun _ => nil) _)
      (getsEmpty: gets = defaultDiffTuple (fun _ => nil) _)
      (retEval: ret = evalExpr e): SemAction (Return e) old new puts gets ret.

  Section Step.
    Variable ls: list (Action type modLists (Bit 0)).

    Inductive Step: ModState modLists.(mregs) modLists.(mmems) modLists.(mregUs) modLists.(mmemUs) ->
                    ModState modLists.(mregs) modLists.(mmems) modLists.(mregUs) modLists.(mmemUs) ->
                    FuncIo modLists.(msends) ->
                    FuncIo modLists.(mrecvs) ->
                    Prop :=
    | SingleStep old newStep putsStep getsStep
          a (inA: In a ls) (aPf: SemAction a old newStep putsStep getsStep Zmod.zero):
      Step old newStep putsStep getsStep.

    Definition SemAnyAction := MultiStep Step
                                 (defaultDiffTuple (fun _ => nil) _)
                                 (defaultDiffTuple (fun _ => nil) _)
                                 (combineDiffTuple (fun _ => @List.app _) (ls := _))
                                 (combineDiffTuple (fun _ => @List.app _) (ls := _)).
  End Step.
End SemAction.

Section SemMod.
  Variable decl: ModDecl.

  Definition ModStateModDecl :=
    ModState (map (fun x => (fst x, (snd x).(regKind))) decl.(modRegs))
      (map (fun x => (fst x, memToMemU (snd x))) decl.(modMems))
      decl.(modRegUs)
      decl.(modMemUs).

  Inductive InitModConsistent: ModStateModDecl -> Prop :=
  | InitModStateCreate
      (mems: FuncMemState (map (fun x => (fst x, memToMemU (snd x))) decl.(modMems)))
      (regUs: FuncState decl.(modRegUs))
      (memUs: FuncMemState decl.(modMemUs))
      (memsEq: mapDiffTuple (fun _ => fst) mems =
                 createDiffTupleMap (mapF := fun x => (fst x, memToMemU (snd x)))
                   (fun x => memInitFull (snd x)) decl.(modMems))
      old (oldEq: old = {|stateRegs := createDiffTupleMap (mapF := fun x => (fst x, (snd x).(regKind)))
                                         (fun x => regInit (snd x)) decl.(modRegs);
                          stateMems := mems;
                          stateRegUs := regUs;
                          stateMemUs := memUs|}): InitModConsistent old.

  Section SemModDefn.
    Variable ls: forall ty, list (Action ty (getModLists decl) (Bit 0)).
    Variable puts: FuncIo decl.(modSends).
    Variable gets: FuncIo decl.(modRecvs).

    Inductive SemMod : Prop :=
    | SemModProp old new
        (initGood: InitModConsistent old) (steps: SemAnyAction (ls type) old new puts gets).
  End SemModDefn.
End SemMod.

(* Given a consistent initial condition and a trace for m1, m1 implements m2 iff
   there exists some initial condition for m2 that produces the same trace as m1.
   Note that this permits that if ununitialized registers are initialized badly,
   then m2 can never produce the same trace as m1.
   This is okay because m2 does indeed exhibit the behavior of m1 because of some initialization,
   which is what m1 is trying to simulate.
   For instance, if the spec says emit any random number based on the initialization value of a register,
   an implementation that produces the same deterministic value everytime is a valid implementation *)
Record TraceInclusion m1 m2 := { traceSendsEq: modSends (modDecl m1) = modSends (modDecl m2);
                                 traceRecvsEq: modRecvs (modDecl m1) = modRecvs (modDecl m2);
                                 traceInclusion: forall puts gets,
                                   SemMod (modActions m1) puts gets ->
                                   SemMod (modActions m2)
                                     (match traceSendsEq in _ = Y return _ Y with
                                              | eq_refl => puts
                                              end)
                                     (match traceRecvsEq in _ = Y return _ Y with
                                      | eq_refl => gets
                                      end) }.

(* TODO Simulator *)
