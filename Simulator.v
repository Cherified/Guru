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

  Parameter getCyclesFromArgs : nat -> IO nat.

  Definition evalModCyclesIO (n: nat) (m: Mod t) : IO unit :=
    io_bind (getCyclesFromArgs n) (fun actualN =>
    io_bind (initSimStateIO t) (fun st => loopCyclesIO actualN st (map snd (m type)))).

  (* Top-Level Turnkey Simulation Entry Point (Single Cycle) *)
  Definition evalModIO (m: Mod t) : IO unit :=
    io_bind (initSimStateIO t) (fun st => stepSimIO st (map snd (m type))).
End SimLoop.

(* Custom GHC Extraction Directives *)
Extraction Language Haskell.
Extract Constant getCyclesFromArgs => "(\defN -> do
  args <- System.Environment.getArgs
  let parseCycles [] d = d
      parseCycles (""-c"" : s : _) _ | [(n, """")] <- Numeric.readDec s = Prelude.max 0 n
      parseCycles (""--cycles"" : s : _) _ | [(n, """")] <- Numeric.readDec s = Prelude.max 0 n
      parseCycles (arg : rest) d
        | Prelude.Just s <- Data.List.stripPrefix ""--cycles="" arg
        , [(n, """")] <- Numeric.readDec s = Prelude.max 0 n
        | [(n, """")] <- Numeric.readDec arg = Prelude.max 0 n
        | Prelude.otherwise = parseCycles rest d
  Prelude.return (parseCycles args defN))".
Extract Constant IO "a" => "Prelude.IO a".
Extract Inlined Constant io_ret => "Prelude.return".
Extract Inlined Constant io_bind => "(Prelude.>>=)".
Extract Constant IoReg "a" => "Data.IORef.IORef a".
Extract Inlined Constant newReg => "Data.IORef.newIORef".
Extract Inlined Constant readReg => "Data.IORef.readIORef".
Extract Inlined Constant writeReg => "Data.IORef.writeIORef".
Extract Constant IoMem "a" => "Data.Array.IO.IOArray Prelude.Integer a".
Extract Constant newRam => "(\sz def -> Data.Array.IO.newArray (0, sz Prelude.- 1) def)".
Extract Constant readRam => "Data.Array.IO.readArray".
Extract Constant writeRam => "Data.Array.IO.writeArray".
Extract Inlined Constant castSimReg => "(\_ _ s -> unsafeCoerce s)".
Extract Inlined Constant castSimMem => "(\_ _ s -> unsafeCoerce s)".
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
                items = Prelude.map (\i -> Prelude.show i Prelude.++ ""="" Prelude.++ simFormatVal (arr Data.Vector.! Prelude.fromInteger i) subF) [0 .. n Prelude.- 1]
            in ""["" Prelude.++ Data.List.intercalate "", "" items Prelude.++ ""]""
          FTaggedUnion ls tagBF dataBF ->
            let (dVal, tVal) = unsafeCoerce val
            in ""{data="" Prelude.++ simFormatVal dVal (FBit 0 Prelude.False 0 dataBF) Prelude.++ "", tag="" Prelude.++ simFormatVal tVal (FBit 0 Prelude.False 0 tagBF) Prelude.++ ""}""
  in Prelude.putStr (simFormatVal v ff))".

Extract Constant io_send => "(\name k val -> Prelude.return ())".

Extract Constant io_recv => "(\name k -> Prelude.return (unsafeCoerce (getDefault k)))".
Extract Constant io_stepCycle => "(\_ -> Prelude.return ())".


(* High-Speed SameTuple Vector Extraction Mappings *)
Extract Inductive SameTuple => "Data.Vector.Vector" [ "Data.Vector.fromList" ] "(\f st -> f (Data.Vector.toList st))".
Extract Inlined Constant readSameTuple => "(\_ arr idx -> Data.Vector.unsafeIndex arr (Prelude.fromIntegral (idx :: Prelude.Integer)))".
Extract Inlined Constant updSameTuple => "(\_ arr idx val -> let i = Prelude.fromIntegral (idx :: Prelude.Integer) in if i Prelude.>= 0 Prelude.&& i Prelude.< Data.Vector.length arr then Data.Vector.modify (\m -> Data.Vector.Mutable.unsafeWrite m i val) arr else arr)".
Extract Inlined Constant updSameTupleNat => "(\_ arr idx val -> let i = Prelude.fromIntegral (idx :: Prelude.Integer) in if i Prelude.>= 0 Prelude.&& i Prelude.< Data.Vector.length arr then Data.Vector.modify (\m -> Data.Vector.Mutable.unsafeWrite m i val) arr else arr)".
Extract Inlined Constant mapSameTuple => "(\f _ st -> Data.Vector.map f st)".
Extract Inlined Constant evalBinaryArray => "(\_ _ f v1 v2 -> unsafeCoerce (Data.Vector.zipWith (unsafeCoerce f) (unsafeCoerce v1) (unsafeCoerce v2)))".
Extract Inlined Constant evalUnaryArray => "(\_ _ f v -> unsafeCoerce (Data.Vector.map (unsafeCoerce f) (unsafeCoerce v)))".
Extract Constant SameTupleDefault => "(\val n -> Data.Vector.replicate (Prelude.fromIntegral n) val)".

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

(* High-Speed Nat and Z Conversions *)
Extract Inlined Constant Z.of_nat => "(\x -> x)".
Extract Inlined Constant Z.to_nat => "(\x -> Prelude.max 0 x)".
Extract Inlined Constant Pos.to_nat => "(\x -> x)".
Extract Inlined Constant Pos.of_nat => "(\x -> Prelude.max 1 x)".
Extract Inlined Constant Pos.of_succ_nat => "(\x -> x Prelude.+ 1)".

Extract Inlined Constant Z.eqb => "(\x y -> (x :: Prelude.Integer) Prelude.== (y :: Prelude.Integer))".
Extract Inlined Constant Z.ltb => "(\x y -> (x :: Prelude.Integer) Prelude.< (y :: Prelude.Integer))".
Extract Inlined Constant Z.leb => "(\x y -> (x :: Prelude.Integer) Prelude.<= (y :: Prelude.Integer))".
Extract Inlined Constant Z.gtb => "(\x y -> (x :: Prelude.Integer) Prelude.> (y :: Prelude.Integer))".
Extract Inlined Constant Z.geb => "(\x y -> (x :: Prelude.Integer) Prelude.>= (y :: Prelude.Integer))".
Extract Inlined Constant Pos.succ => "(\x -> (x :: Prelude.Integer) Prelude.+ 1)".
Extract Inlined Constant Pos.add => "(\x y -> (x :: Prelude.Integer) Prelude.+ (y :: Prelude.Integer))".
Extract Inlined Constant Pos.sub => "(\x y -> Prelude.max 1 ((x :: Prelude.Integer) Prelude.- (y :: Prelude.Integer)))".
Extract Inlined Constant Pos.mul => "(\x y -> (x :: Prelude.Integer) Prelude.* (y :: Prelude.Integer))".
Extract Inlined Constant Pos.eqb => "(\x y -> (x :: Prelude.Integer) Prelude.== (y :: Prelude.Integer))".
Extract Inlined Constant Pos.ltb => "(\x y -> (x :: Prelude.Integer) Prelude.< (y :: Prelude.Integer))".
Extract Inlined Constant Pos.leb => "(\x y -> (x :: Prelude.Integer) Prelude.<= (y :: Prelude.Integer))".
Extract Inlined Constant NatZ_mul => "(\x y -> (x :: Prelude.Integer) Prelude.* (y :: Prelude.Integer))".

Extract Inlined Constant fold_left => "(\f l a0 -> Data.List.foldl' f a0 l)".
Extract Inlined Constant readNatToFinType => "(\def n reader i -> if (i :: Prelude.Integer) Prelude.< n Prelude.&& (i :: Prelude.Integer) Prelude.>= 0 then reader i else def)".

(* High-Speed Bit Array Serialization (Zero Intermediate Heap Overhead) *)
Extract Constant evalToBitArray => "(\n k f arr ->
  case k of
    Bit m ->
      let ksz = Prelude.fromIntegral m
          mask = Data.Bits.shiftL 1 ksz Prelude.- 1
          vArr = unsafeCoerce arr :: Data.Vector.Vector Prelude.Integer
          len = Data.Vector.length vArr
          loop i acc sh =
            if i Prelude.>= len
            then acc
            else
              let elemVal = Data.Vector.unsafeIndex vArr i
                  acc' = acc Data.Bits..|. Data.Bits.shiftL (elemVal Data.Bits..&. mask) sh
              in acc' `Prelude.seq` loop (i Prelude.+ 1) acc' (sh Prelude.+ ksz)
      in loop 0 0 0
    Bool ->
      let vArr = unsafeCoerce arr :: Data.Vector.Vector Prelude.Bool
          len = Data.Vector.length vArr
          loop i acc sh =
            if i Prelude.>= len
            then acc
            else
              let b = Data.Vector.unsafeIndex vArr i
                  acc' = if b then acc Data.Bits..|. Data.Bits.shiftL 1 sh else acc
              in acc' `Prelude.seq` loop (i Prelude.+ 1) acc' (sh Prelude.+ 1)
      in loop 0 0 0
    _ ->
      let ksz = Prelude.fromIntegral (kindSize k)
          mask = Data.Bits.shiftL 1 ksz Prelude.- 1
          vArr = unsafeCoerce arr :: Data.Vector.Vector Type
          len = Data.Vector.length vArr
          loop i acc sh =
            if i Prelude.>= len
            then acc
            else
              let elemVal = Data.Vector.unsafeIndex vArr i
                  v = unsafeCoerce f elemVal :: Prelude.Integer
                  acc' = acc Data.Bits..|. Data.Bits.shiftL (v Data.Bits..&. mask) sh
              in acc' `Prelude.seq` loop (i Prelude.+ 1) acc' (sh Prelude.+ ksz)
      in loop 0 0 0)".

Extract Constant evalFromBitArray => "(\n k f v0 ->
  let nInt = Prelude.fromIntegral n in
  case k of
    Bit m ->
      let ksz = Prelude.fromIntegral m
          mask = Data.Bits.shiftL 1 ksz Prelude.- 1
      in unsafeCoerce (Data.Vector.create (do
           mv <- Data.Vector.Mutable.unsafeNew nInt
           let loop i remVal =
                 if i Prelude.>= nInt
                 then Prelude.return ()
                 else do
                   let elemBits = remVal Data.Bits..&. mask
                   Data.Vector.Mutable.unsafeWrite mv i elemBits
                   loop (i Prelude.+ 1) (Data.Bits.shiftR remVal ksz)
           loop 0 (unsafeCoerce v0 :: Prelude.Integer)
           Prelude.return mv))
    Bool ->
      let vInt = unsafeCoerce v0 :: Prelude.Integer
      in unsafeCoerce (Data.Vector.create (do
           mv <- Data.Vector.Mutable.unsafeNew nInt
           let loop i =
                 if i Prelude.>= nInt
                 then Prelude.return ()
                 else do
                   let b = Data.Bits.testBit vInt i
                   Data.Vector.Mutable.unsafeWrite mv i b
                   loop (i Prelude.+ 1)
           loop 0
           Prelude.return mv))
    _ ->
      let ksz = Prelude.fromIntegral (kindSize k)
          mask = Data.Bits.shiftL 1 ksz Prelude.- 1
      in unsafeCoerce (Data.Vector.create (do
           mv <- Data.Vector.Mutable.unsafeNew nInt
           let loop i remVal =
                 if i Prelude.>= nInt
                 then Prelude.return ()
                 else do
                   let elemBits = remVal Data.Bits..&. mask
                       val = unsafeCoerce f elemBits
                   Data.Vector.Mutable.unsafeWrite mv i val
                   loop (i Prelude.+ 1) (Data.Bits.shiftR remVal ksz)
           loop 0 (unsafeCoerce v0 :: Prelude.Integer)
           Prelude.return mv))".

(* High-Speed Direct evalToBit and evalFromBit (Zero Intermediate Heap Overhead) *)
Extract Constant evalToBit => "(\k v ->
  let go k v = case k of
        Bit _ -> unsafeCoerce v
        Bool -> if unsafeCoerce v then 1 else 0
        Array n k' -> case k' of
          Bit m ->
            let ksz = Prelude.fromIntegral m
                mask = Data.Bits.shiftL 1 ksz Prelude.- 1
                vArr = unsafeCoerce v :: Data.Vector.Vector Prelude.Integer
                len = Data.Vector.length vArr
                loop i acc sh =
                  if i Prelude.>= len
                  then acc
                  else
                    let elemVal = Data.Vector.unsafeIndex vArr i
                        acc' = acc Data.Bits..|. Data.Bits.shiftL (elemVal Data.Bits..&. mask) sh
                    in acc' `Prelude.seq` loop (i Prelude.+ 1) acc' (sh Prelude.+ ksz)
            in loop 0 0 0
          Bool ->
            let vArr = unsafeCoerce v :: Data.Vector.Vector Prelude.Bool
                len = Data.Vector.length vArr
                loop i acc sh =
                  if i Prelude.>= len
                  then acc
                  else
                    let b = Data.Vector.unsafeIndex vArr i
                        acc' = if b then acc Data.Bits..|. Data.Bits.shiftL 1 sh else acc
                    in acc' `Prelude.seq` loop (i Prelude.+ 1) acc' (sh Prelude.+ 1)
            in loop 0 0 0
          _ ->
            let ksz = Prelude.fromIntegral (kindSize k')
                mask = Data.Bits.shiftL 1 ksz Prelude.- 1
                vArr = unsafeCoerce v :: Data.Vector.Vector Type
                len = Data.Vector.length vArr
                loop i acc sh =
                  if i Prelude.>= len
                  then acc
                  else
                    let elemVal = Data.Vector.unsafeIndex vArr i
                        b = go k' elemVal
                        acc' = acc Data.Bits..|. Data.Bits.shiftL (b Data.Bits..&. mask) sh
                    in acc' `Prelude.seq` loop (i Prelude.+ 1) acc' (sh Prelude.+ ksz)
            in loop 0 0 0
        Struct [] -> 0
        Struct ((_, k1) : rest) ->
          let (v1, vRest) = unsafeCoerce v
              b1 = go k1 v1
              bRest = go (Struct rest) vRest
              sh = Prelude.fromIntegral (kindSize (Struct rest))
          in Data.Bits.shiftL b1 sh Data.Bits..|. bRest
        TaggedUnion ls ->
          let (dVal, tVal) = unsafeCoerce v
              tagSz = Prelude.fromIntegral (log2_up (Prelude.fromIntegral (Prelude.length ls)))
              bData = unsafeCoerce dVal :: Prelude.Integer
              bTag = unsafeCoerce tVal :: Prelude.Integer
          in Data.Bits.shiftL bData tagSz Data.Bits..|. bTag
  in go k (unsafeCoerce v))".

Extract Constant evalFromBit => "(\k v ->
  let go k v = case k of
        Bit _ -> unsafeCoerce v
        Bool -> unsafeCoerce (v Prelude.== 1)
        Array n k' -> case k' of
          Bit m ->
            let nInt = Prelude.fromIntegral n
                ksz = Prelude.fromIntegral m
                mask = Data.Bits.shiftL 1 ksz Prelude.- 1
            in unsafeCoerce (Data.Vector.create (do
                 mv <- Data.Vector.Mutable.unsafeNew nInt
                 let loop i remVal =
                       if i Prelude.>= nInt
                       then Prelude.return ()
                       else do
                         let elemBits = remVal Data.Bits..&. mask
                         Data.Vector.Mutable.unsafeWrite mv i elemBits
                         loop (i Prelude.+ 1) (Data.Bits.shiftR remVal ksz)
                 loop 0 (unsafeCoerce v :: Prelude.Integer)
                 Prelude.return mv))
          Bool ->
            let nInt = Prelude.fromIntegral n
                vInt = unsafeCoerce v :: Prelude.Integer
            in unsafeCoerce (Data.Vector.create (do
                 mv <- Data.Vector.Mutable.unsafeNew nInt
                 let loop i =
                       if i Prelude.>= nInt
                       then Prelude.return ()
                       else do
                         let b = Data.Bits.testBit vInt i
                         Data.Vector.Mutable.unsafeWrite mv i b
                         loop (i Prelude.+ 1)
                 loop 0
                 Prelude.return mv))
          _ ->
            let nInt = Prelude.fromIntegral n
                ksz = Prelude.fromIntegral (kindSize k')
                mask = Data.Bits.shiftL 1 ksz Prelude.- 1
            in unsafeCoerce (Data.Vector.create (do
                 mv <- Data.Vector.Mutable.unsafeNew nInt
                 let loop i remVal =
                       if i Prelude.>= nInt
                       then Prelude.return ()
                       else do
                         let elemBits = remVal Data.Bits..&. mask
                             elemVal = go k' (unsafeCoerce elemBits)
                         Data.Vector.Mutable.unsafeWrite mv i elemVal
                         loop (i Prelude.+ 1) (Data.Bits.shiftR remVal ksz)
                 loop 0 (unsafeCoerce v :: Prelude.Integer)
                 Prelude.return mv))
        Struct [] -> unsafeCoerce ()
        Struct ((_, k1) : rest) ->
          let restSz = Prelude.fromIntegral (kindSize (Struct rest))
              restMask = Data.Bits.shiftL 1 restSz Prelude.- 1
              b1 = Data.Bits.shiftR (unsafeCoerce v :: Prelude.Integer) restSz
              bRest = (unsafeCoerce v :: Prelude.Integer) Data.Bits..&. restMask
              v1 = go k1 (unsafeCoerce b1)
              vRest = go (Struct rest) (unsafeCoerce bRest)
          in unsafeCoerce (v1, vRest)
        TaggedUnion ls ->
          let dataSz = Prelude.fromIntegral (max_list (Prelude.map (kindSize Prelude.. Prelude.snd) ls))
              tagSz = Prelude.fromIntegral (log2_up (Prelude.fromIntegral (Prelude.length ls)))
              maskData = Data.Bits.shiftL 1 dataSz Prelude.- 1
              maskTag = Data.Bits.shiftL 1 tagSz Prelude.- 1
              dVal = (unsafeCoerce v :: Prelude.Integer) Data.Bits..&. maskData
              tVal = Data.Bits.shiftR (unsafeCoerce v :: Prelude.Integer) dataSz Data.Bits..&. maskTag
          in unsafeCoerce (dVal, tVal)
  in go k (unsafeCoerce v))".
