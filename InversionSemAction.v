Require Import String List.
Require Import Guru.Lib.Library.
Require Import Guru.Syntax Guru.Semantics.

Set Implicit Arguments.
Set Asymmetric Patterns.

Section InversionSemAction.
  Variable regs: list (string * Kind).
  Variable mems: list (string * (nat * Kind)).
  Variable sends: list (string * Kind).
  Variable recvs: list (string * Kind).

  Theorem InversionSemAction
    k (a: Action type regs mems sends recvs k) old new puts gets ret
    (semA: SemAction a old new puts gets ret):
    match a with
    | ReadReg x cont => SemAction (cont (stateRegs old x)) old new puts gets ret
    | WriteReg x v cont =>
        SemAction cont {|stateRegs := fun i => match FinStruct_dec x i with
                                               | left pf => match pf in _ = Y return type (fieldK Y) with
                                                            | eq_refl => evalExpr v
                                                            end
                                               | right _ => stateRegs old i
                                               end;
                         stateMems := stateMems old |} new puts gets ret
    | ReadMem x i cont =>
        SemAction (cont (readArray (Default _) (arrayToFunc (stateMems old x)) (evalExpr i)))
          old new puts gets ret
    | WriteMem x i v cont =>
        SemAction
          cont
          {|stateRegs := stateRegs old;
            stateMems :=
              fun j =>
                match FinStruct_dec x j with
                | left pf =>
                    match pf in _ = Y
                          return type (Array (fst (fieldK Y)) (snd (fieldK Y))) with
                    | eq_refl => funcToArray (writeArray (evalExpr v)
                                                (arrayToFunc (stateMems old x)) (evalExpr i))
                    end
                | right _ => stateMems old j
                end |} new puts gets ret
    | Send x v cont =>
        exists putsStep,
        SemAction cont old new putsStep gets ret /\
          puts = fun i => match FinStruct_dec x i with
                          | left pf => match pf in _ = Y return list (type (fieldK Y)) with
                                       | eq_refl => evalExpr v :: putsStep x
                                       end
                          | right _ => putsStep i
                          end
    | Recv x cont =>
        exists recvStep getsStep,
        SemAction (cont recvStep) old new puts getsStep ret /\
          gets = fun i => match FinStruct_dec x i with
                          | left pf => match pf in _ = Y return list (type (fieldK Y)) with
                                       | eq_refl => recvStep :: getsStep x
                                       end
                          | right _ => getsStep i
                          end
    | LetExpr s k' e cont =>
        SemAction (cont (evalExpr e)) old new puts gets ret
    | LetAction s k' a cont =>
        exists newStep putsStep getsStep retStep interPuts interGets,
        SemAction a old newStep putsStep getsStep retStep /\
          SemAction (cont retStep) newStep new interPuts interGets ret /\
          (puts = fun i => putsStep i ++ interPuts i) /\
          gets = fun i => getsStep i ++ interGets i
    | NonDet s k' cont =>
        exists v,
        SemAction (cont v) old new puts gets ret
    | IfElse s p k' t f cont =>
        exists newStep putsStep getsStep retStep interPuts interGets,
        (evalExpr p = true -> SemAction t old newStep putsStep getsStep retStep) /\
          (evalExpr p = false -> SemAction f old newStep putsStep getsStep retStep) /\
          SemAction (cont retStep) newStep new interPuts interGets ret
    | Sys ls cont =>
        SemAction cont old new puts gets ret
    | Return e =>
        new = old /\ (puts = fun i => nil) /\ gets = fun i => nil
    end.
  Proof.
    destruct semA; eauto; repeat eexists; eauto; try discriminate.
  Qed.
End InversionSemAction.
