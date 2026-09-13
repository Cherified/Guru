(*
 * Copyright (c) 2025-2026 Cherified Systems LLC
 *
 * SPDX-License-Identifier: MIT
 *)

From Stdlib Require Import String ZArith List Zmod Bool.
From Guru Require Import Library Syntax Semantics Extraction.

(* Top-Level Abstract IO Monad *)
Parameter IO : Type -> Type.
Parameter io_ret : forall {A}, A -> IO A.
Parameter io_bind : forall {A B}, IO A -> (A -> IO B) -> IO B.

(* Foreign Monadic Reference Types *)
Parameter IoReg : Type -> Type.
Parameter newReg : forall {A}, A -> IO (IoReg A).
Parameter readReg : forall {A}, IoReg A -> IO A.
Parameter writeReg : forall {A}, IoReg A -> A -> IO unit.

Parameter IoMem : Type -> Type.
Parameter newRam : forall {A}, Z -> A -> IO (IoMem A).
Parameter readRam : forall {A}, IoMem A -> Z -> IO A.
Parameter writeRam : forall {A}, IoMem A -> Z -> A -> IO unit.

(* 1:1 Mirror Simulation Leaf State (IoMem ** IoMem for RAM & Ports!) *)
Definition SimElemState (e: Elem) : Type :=
  match e with
  | EReg r => IoReg (type (regKind r))
  | EMem m => IoMem (type (memKind m)) ** IoMem (type (memKind m))
  | ESend _ => unit
  | ERecv _ => unit
  end.

Definition initSimElemIO (e: Elem) : IO (SimElemState e) :=
  match e return IO (SimElemState e) with
  | EReg r =>
      let init := match r.(regInit) with
                  | Some v => v
                  | None => getDefault _
                  end in
      newReg init
  | EMem m =>
      io_bind (newRam (Z.of_nat m.(memSize)) (getDefault _)) (fun ram =>
      io_bind (newRam (Z.of_nat m.(memPort)) (getDefault _)) (fun ports =>
      io_ret (ram ,, ports)))
  | ESend _ => io_ret tt
  | ERecv _ => io_ret tt
  end.

Definition SimDomainElemState (de: DomainElem) : Type :=
  SimElemState (snd de).

Fixpoint initSimStateIO (t: Tree DomainElem) : IO (TreeState SimDomainElemState t) :=
  match t return IO (TreeState SimDomainElemState t) with
  | Leaf _ de => initSimElemIO (snd de)
  | Node _ children =>
      (fix loop (ls: list (Tree DomainElem)) : IO (ListTreeState SimDomainElemState ls) :=
         match ls return IO (ListTreeState SimDomainElemState ls) with
         | nil => io_ret tt
         | x :: xs =>
             io_bind (initSimStateIO x) (fun sx =>
             io_bind (loop xs) (fun sxs =>
             io_ret (sx ,, sxs)))
         end) children
  end.

Parameter castSimReg : forall {t: Tree DomainElem} (x: RegPath t),
  SimDomainElemState (getLeaf x.(regPath)) -> IoReg (type (regKind (getRegFromPath x))).

Parameter castSimMem : forall {t: Tree DomainElem} (x: MemPath t),
  SimDomainElemState (getLeaf x.(memPath)) -> IoMem (type (getMemFromPath x).(memKind)) ** IoMem (type (getMemFromPath x).(memKind)).

Parameter io_putStr : string -> IO unit.
Parameter io_finish : IO unit.
Parameter io_dispVal : forall {k: Kind}, type k -> FullFormat k -> IO unit.
Parameter io_send : string -> forall (k: Kind), type k -> IO unit.
Parameter io_recv : string -> forall (k: Kind), IO (type k).
Parameter io_stepCycle : nat -> IO unit.

Section TreeLeafName.
  Variable A: Type.

  Fixpoint getLeafName (t: Tree A) : LeafPath t -> string :=
    match t return LeafPath t -> string with
    | Leaf name _ => fun _ => name
    | Node _ children =>
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
                end) ls) -> string with
           | nil => fun empty => match empty with end
           | x :: xs => fun p_sum =>
               match p_sum with
               | inl p_x => getLeafName x p_x
               | inr p_xs => loop xs p_xs
               end
           end) children
    end.
End TreeLeafName.

Arguments getLeafName [A] [t] p.

Section SimLoop.
  Variable t: Tree DomainElem.

  Definition evalSysT (st: SysT type) : IO unit :=
    match st with
    | DispString _ s => io_putStr s
    | DispExpr e ff => io_dispVal (evalExpr e) ff
    | Finish _ => io_finish
    end.

  Fixpoint evalSysTs (ls: list (SysT type)) : IO unit :=
    match ls with
    | nil => io_ret tt
    | x :: xs => io_bind (evalSysT x) (fun _ => evalSysTs xs)
    end.

  (* Blazing Fast In-Place Evaluator (100% Pure Dependent Types & Prod Accessors!) *)
  Fixpoint evalActionIO {k: Kind} (st: TreeState SimDomainElemState t) (act: Action type t k) : IO (type k) :=
    match act with
    | ReadReg s path cont =>
        let reg := castSimReg path (readTreeState t st path.(regPath)) in
        io_bind (readReg reg) (fun val => evalActionIO st (cont val))
    | WriteReg path v cont =>
        let reg := castSimReg path (readTreeState t st path.(regPath)) in
        io_bind (writeReg reg (evalExpr v)) (fun _ => evalActionIO st cont)
    | ReadRqMem path idx p cont =>
        let mem := castSimMem path (readTreeState t st path.(memPath)) in
        let zidx := Zmod.to_Z (evalExpr idx) in
        let sz := Z.of_nat (getMemFromPath path).(memSize) in
        let readAction :=
          if (zidx <? sz)%Z then
            readRam mem.(Fst) zidx
          else
            io_ret (getDefault _) in
        io_bind readAction (fun val =>
        io_bind (writeRam mem.(Snd) (Z.of_nat p.(finNum)) val) (fun _ =>
        evalActionIO st cont))
    | ReadRpMem s path p cont =>
        let mem := castSimMem path (readTreeState t st path.(memPath)) in
        io_bind (readRam mem.(Snd) (Z.of_nat p.(finNum))) (fun val =>
        evalActionIO st (cont val))
    | WriteMem path idx v cont =>
        let mem := castSimMem path (readTreeState t st path.(memPath)) in
        let zidx := Zmod.to_Z (evalExpr idx) in
        let sz := Z.of_nat (getMemFromPath path).(memSize) in
        let writeAction :=
          if (zidx <? sz)%Z then
            writeRam mem.(Fst) zidx (evalExpr v)
          else
            io_ret tt in
        io_bind writeAction (fun _ => evalActionIO st cont)
    | Send path v cont =>
        let name := getLeafName path.(sendPath) in
        let k := getSendKind path in
        io_bind (io_send name k (evalExpr v)) (fun _ =>
        evalActionIO st cont)
    | Recv s path cont =>
        let name := getLeafName path.(recvPath) in
        let k := getRecvKind path in
        io_bind (io_recv name k) (fun val =>
        evalActionIO st (cont val))
    | LetExp s e cont =>
        evalActionIO st (cont (evalExpr e))
    | LetAction s a cont =>
        io_bind (evalActionIO st a) (fun val => evalActionIO st (cont val))
    | NonDet s k' cont =>
        evalActionIO st (cont (getDefault _))
    | IfElse s p tb fb cont =>
        io_bind (if evalExpr p then evalActionIO st tb else evalActionIO st fb)
          (fun val => evalActionIO st (cont val))
    | System ls cont =>
        io_bind (evalSysTs ls) (fun _ => evalActionIO st cont)
    | Return e =>
        io_ret (evalExpr e)
    end.

  (* Executes one clock cycle across scheduled rules *)
  Fixpoint stepSimIO (st: TreeState SimDomainElemState t) (rules: list (Action type t (Bit 0))) : IO unit :=
    match rules with
    | nil => io_ret tt
    | r :: rs => io_bind (evalActionIO st r) (fun _ => stepSimIO st rs)
    end.

  (* Bounded Multi-Cycle Simulation Loop *)
  Fixpoint loopCyclesHelperIO (c: nat) (n: nat) (st: TreeState SimDomainElemState t) (rules: list (Action type t (Bit 0))) : IO unit :=
    match n with
    | 0 => io_ret tt
    | S k => io_bind (io_stepCycle c) (fun _ =>
             io_bind (stepSimIO st rules) (fun _ =>
             loopCyclesHelperIO (S c) k st rules))
    end.

  Definition loopCyclesIO (n: nat) (st: TreeState SimDomainElemState t) (rules: list (Action type t (Bit 0))) : IO unit :=
    loopCyclesHelperIO 0 n st rules.

  Definition evalModCyclesIO (n: nat) (m: Mod t) : IO unit :=
    io_bind (initSimStateIO t) (fun st => loopCyclesIO n st (map snd (m type))).

  (* Top-Level Turnkey Simulation Entry Point (Single Cycle) *)
  Definition evalModIO (m: Mod t) : IO unit :=
    io_bind (initSimStateIO t) (fun st => stepSimIO st (map snd (m type))).
End SimLoop.

(* Custom GHC Extraction Directives *)
Extraction Language Haskell.
Extract Constant IO "a" => "Prelude.IO a".
Extract Constant io_ret => "Prelude.return".
Extract Constant io_bind => "(\m f -> m Prelude.>>= f)".
Extract Constant IoReg "a" => "Data.IORef.IORef a".
Extract Constant newReg => "Data.IORef.newIORef".
Extract Constant readReg => "Data.IORef.readIORef".
Extract Constant writeReg => "Data.IORef.writeIORef".
Extract Constant IoMem "a" => "Data.Array.IO.IOArray Prelude.Integer a".
Extract Constant newRam => "(\sz def -> Data.Array.IO.newArray (0, sz Prelude.- 1) def)".
Extract Constant readRam => "Data.Array.IO.readArray".
Extract Constant writeRam => "Data.Array.IO.writeArray".
Extract Constant castSimReg => "(\_ _ s -> unsafeCoerce s)".
Extract Constant castSimMem => "(\_ _ s -> unsafeCoerce s)".
Extract Constant io_putStr => "(\s ->
  let unesc ('\\':'n':xs) = '\n' : unesc xs
      unesc ('\\':'t':xs) = '\t' : unesc xs
      unesc ('\\':'r':xs) = '\r' : unesc xs
      unesc ('\\':'\\':xs) = '\\' : unesc xs
      unesc (c:xs) = c : unesc xs
      unesc [] = []
  in Prelude.putStr (unesc s))".
Extract Constant io_finish => "System.Exit.exitSuccess".
Extract Constant io_dispVal => "(\_ v ff ->
  let simFormatVal val format =
        case format of
          FBool zeroPad sz bf ->
            let s = if unsafeCoerce val then ""1"" else ""0""
                padChar = if zeroPad then '0' else ' '
            in if sz Prelude.<= 0 then s else Prelude.replicate (Prelude.fromInteger sz Prelude.- 1) padChar Prelude.++ s
          FBit n zeroPad sz bf ->
            let s = case bf of
                      Hex -> Numeric.showHex (unsafeCoerce val :: Prelude.Integer) """"
                      Decimal -> Prelude.show (unsafeCoerce val :: Prelude.Integer)
                      _ -> Numeric.showIntAtBase 2 Data.Char.intToDigit (unsafeCoerce val :: Prelude.Integer) """"
                padChar = if zeroPad then '0' else ' '
            in if sz Prelude.<= 0 then s else Prelude.replicate (Prelude.fromInteger sz Prelude.- Prelude.length s) padChar Prelude.++ s
          FStruct ls ffs ->
            let fmtFields [] _ _ = []
                fmtFields ((s,k):xs) vTuple fTuple =
                  let (v1, v2) = unsafeCoerce vTuple
                      (f1, f2) = unsafeCoerce fTuple
                      rest = fmtFields xs v2 f2
                  in if kindSize k Prelude.> 0
                     then (s Prelude.++ ""="" Prelude.++ simFormatVal v1 f1) : rest
                     else rest
            in ""{"" Prelude.++ Data.List.intercalate "", "" (fmtFields ls val ffs) Prelude.++ ""}""
          FArray n k subF ->
            let arr = unsafeCoerce val
                items = Prelude.map (\i -> Prelude.show i Prelude.++ ""="" Prelude.++ simFormatVal (arr Data.IntMap.Strict.! Prelude.fromInteger i) subF) [0 .. n Prelude.- 1]
            in ""["" Prelude.++ Data.List.intercalate "", "" items Prelude.++ ""]""
          FTaggedUnion ls tagBF dataBF ->
            let (dVal, tVal) = unsafeCoerce val
            in ""{data="" Prelude.++ simFormatVal dVal (FBit 0 Prelude.False 0 dataBF) Prelude.++ "", tag="" Prelude.++ simFormatVal tVal (FBit 0 Prelude.False 0 tagBF) Prelude.++ ""}""
  in Prelude.putStr (simFormatVal v ff))".

Extract Constant io_send => "(\name k val -> Prelude.return ())".

Extract Constant io_recv => "(\name k -> Prelude.return (unsafeCoerce (getDefault k)))".
Extract Constant io_stepCycle => "(\_ -> Prelude.return ())".


(* High-Speed SameTuple IntMap Extraction Mappings *)
Extract Inductive SameTuple => "Data.IntMap.Strict.IntMap" [ "(Data.IntMap.Strict.fromList Prelude.. Prelude.zip [0..])" ] "(\f st -> f (Data.IntMap.Strict.elems st))".
Extract Constant readSameTuple => "(\_ arr idx -> arr Data.IntMap.Strict.! Prelude.fromInteger idx)".
Extract Constant updSameTuple => "(\_ arr idx val -> Data.IntMap.Strict.insert (Prelude.fromInteger idx) val arr)".
Extract Constant updSameTupleNat => "(\_ arr idx val -> Data.IntMap.Strict.insert (Prelude.fromInteger idx) val arr)".
Extract Constant mapSameTuple => "(\f _ st -> Data.IntMap.Strict.map f st)".

(* High-Speed Zmod Data.Bits Extraction Mappings *)
Extract Constant Z.pow => "(\x y -> if x Prelude.== 2 then Data.Bits.shiftL 1 (Prelude.fromIntegral y) else if y Prelude.< 0 then 0 else x Prelude.^ y)".
Extract Constant Z.pow_pos => "(\x y -> if x Prelude.== 2 then Data.Bits.shiftL 1 (Prelude.fromIntegral y) else x Prelude.^ y)".
Extract Constant Zmod.to_Z => "(\_ x -> x)".
Extract Constant Zmod.of_Z => "(\m z -> z Data.Bits..&. (m Prelude.- 1))".
Extract Constant Zmod.zero => "(\_ -> 0)".
Extract Constant Zmod.one => "(\_ -> 1)".
Extract Constant Zmod.add => "(\m x y -> (x Prelude.+ y) Data.Bits..&. (m Prelude.- 1))".
Extract Constant Zmod.sub => "(\m x y -> (x Prelude.- y) Data.Bits..&. (m Prelude.- 1))".
Extract Constant Zmod.opp => "(\m x -> (Prelude.negate x) Data.Bits..&. (m Prelude.- 1))".
Extract Constant Zmod.mul => "(\m x y -> (x Prelude.* y) Data.Bits..&. (m Prelude.- 1))".
Extract Constant Zmod.udiv => "(\m x y -> if y Prelude.== 0 then (m Prelude.- 1) else (x `Prelude.quot` y) Data.Bits..&. (m Prelude.- 1))".
Extract Constant Zmod.umod => "(\m x y -> if y Prelude.== 0 then x else x `Prelude.rem` y)".
Extract Constant Zmod.and => "(\_ x y -> x Data.Bits..&. y)".
Extract Constant Zmod.or => "(\_ x y -> x Data.Bits..|. y)".
Extract Constant Zmod.xor => "(\_ x y -> Data.Bits.xor x y)".
Extract Constant Zmod.not => "(\m x -> Data.Bits.xor (m Prelude.- 1) x)".
Extract Constant Zmod.eqb => "(\_ x y -> x Prelude.== y)".
Extract Constant Zmod.slu => "(\m x n -> Data.Bits.shiftL x (Prelude.fromIntegral n) Data.Bits..&. (m Prelude.- 1))".
Extract Constant Zmod.sru => "(\_ x n -> Data.Bits.shiftR x (Prelude.fromIntegral n))".
Extract Constant Zmod.srs => "(\m x n -> let half = Data.Bits.shiftR m 1; sx = if x Prelude.>= half then x Prelude.- m else x in Data.Bits.shiftR sx (Prelude.fromIntegral n) Data.Bits..&. (m Prelude.- 1))".
Extract Constant Zmod.firstn => "(\n _ a -> a Data.Bits..&. (Data.Bits.shiftL 1 (Prelude.fromIntegral n) Prelude.- 1))".
Extract Constant Zmod_lastn => "(\n w a -> Data.Bits.shiftR a (Prelude.fromIntegral (w Prelude.- n)) Data.Bits..&. (Data.Bits.shiftL 1 (Prelude.fromIntegral n) Prelude.- 1))".
Extract Constant Zmod.app => "(\n _ a b -> Data.Bits.shiftL b (Prelude.fromIntegral n) Data.Bits..|. a)".
Extract Constant Z_uxor => "(\z -> if Prelude.even (Data.Bits.popCount z) then Prelude.False else Prelude.True)".
