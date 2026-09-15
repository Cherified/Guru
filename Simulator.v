(*
 * Copyright (c) 2025-2026 Cherified Systems LLC
 *
 * SPDX-License-Identifier: MIT
 *)

From Stdlib Require Import String ZArith List Zmod Bool.
From Guru Require Import Library Syntax Semantics Composition Extraction.

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
Extract Constant IoMem "a" => "Data.Vector.Mutable.IOVector a".
Extract Constant newRam => "(\sz def -> Data.Vector.Mutable.replicate (Prelude.fromIntegral sz) def)".
Extract Constant readRam => "(\mem idx -> Data.Vector.Mutable.unsafeRead mem (Prelude.fromIntegral (idx :: Prelude.Integer)))".
Extract Constant writeRam => "(\mem idx val -> Data.Vector.Mutable.unsafeWrite mem (Prelude.fromIntegral (idx :: Prelude.Integer)) val)".
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
Extract Constant io_dispVal => "(\k v ff ->
  if kindSize k Prelude.<= 0
  then Prelude.return ()
  else
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
                  fmtFields ((s,kf):xs) vTuple fTuple =
                    let (v1, v2) = unsafeCoerce vTuple
                        (f1, f2) = unsafeCoerce fTuple
                        rest = fmtFields xs v2 f2
                    in if kindSize kf Prelude.> 0
                       then (s Prelude.++ ""="" Prelude.++ simFormatVal v1 f1) : rest
                       else rest
              in ""{"" Prelude.++ Data.List.intercalate "", "" (fmtFields ls val ffs) Prelude.++ ""}""
            FArray n k' subF ->
              let arr = unsafeCoerce val
                  items = Prelude.map (\i -> Prelude.show i Prelude.++ ""="" Prelude.++ simFormatVal (arr Data.Vector.! Prelude.fromInteger i) subF) [0 .. n Prelude.- 1]
              in ""["" Prelude.++ Data.List.intercalate "", "" items Prelude.++ ""]""
            FTaggedUnion ls tagBF dataBF ->
              let (dVal, tVal) = unsafeCoerce val
                  tagSize = log2_up (Prelude.toInteger (Prelude.length ls))
                  dataSize = Data.List.foldl' Prelude.max 0 (Prelude.map (kindSize Prelude.. Prelude.snd) ls)
                  dataStr = simFormatVal dVal (FBit dataSize Prelude.False dataSize dataBF)
                  tagStr = simFormatVal tVal (FBit tagSize Prelude.False tagSize tagBF)
              in if tagSize Prelude.<= 0
                 then ""{data="" Prelude.++ dataStr Prelude.++ ""}""
                 else if dataSize Prelude.<= 0
                      then ""{tag="" Prelude.++ tagStr Prelude.++ ""}""
                      else ""{data="" Prelude.++ dataStr Prelude.++ "", tag="" Prelude.++ tagStr Prelude.++ ""}""
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

Extract Constant cast_reg => "(\_ _ _ v -> v)".
Extract Constant cast_mem => "(\_ _ _ v -> v)".
Extract Constant cast_send => "(\_ _ _ v -> v)".
Extract Constant cast_recv => "(\_ _ _ v -> v)".
Extract Constant cast_reg_expr => "(\_ _ _ v -> v)".
Extract Constant cast_mem_expr => "(\_ _ _ v -> v)".
Extract Constant cast_mem_idx => "(\_ _ _ v -> v)".
Extract Constant cast_mem_port => "(\_ _ _ v -> v)".
Extract Constant cast_send_expr => "(\_ _ _ v -> v)".

Extract Constant getTreeRegsOfKind => "(\k t ->
  let go tree wrap acc = case tree of
        Leaf _ a -> case a of
          (_, EReg _) -> unsafeCoerce (wrap (unsafeCoerce ())) : acc
          _ -> acc
        Node _ children ->
          let goChildren [] _ a = a
              goChildren (c:cs) wrapChild a =
                go c (\p -> (unsafeCoerce wrapChild :: Any -> Any) (unsafeCoerce (Prelude.Left (unsafeCoerce p))))
                     (goChildren cs (\p -> (unsafeCoerce wrapChild :: Any -> Any) (unsafeCoerce (Prelude.Right (unsafeCoerce p)))) a)
          in goChildren children wrap acc
  in go t (\x -> x) [])".

Extract Constant embedLeafIntoPath_child => "(\_ p_child p_local ->
  let go pc = case unsafeCoerce pc of
        Prelude.Left px -> case unsafeCoerce px of
          Prelude.Left _ -> unsafeCoerce (Prelude.Left p_local)
          Prelude.Right pc' -> unsafeCoerce (Prelude.Left (go pc'))
        Prelude.Right pxs -> unsafeCoerce (Prelude.Right (go pxs))
  in go p_child)".

Extract Constant writeRegsListHelper => "(\curr k sz t paths ->
  let arr = Data.Vector.fromList paths
      len = Data.Vector.length arr
  in \idx newVal -> LetExp """" (Bit sz) idx (\idxVal ->
       let i = (unsafeCoerce idxVal :: Prelude.Integer) Prelude.- curr
           iInt = Prelude.fromIntegral i
       in if iInt Prelude.>= 0 Prelude.&& iInt Prelude.< len
          then let rk = Data.Vector.unsafeIndex arr iInt
               in WriteReg (rk_path t k rk) newVal (Return (Const (Bit 0) (unsafeCoerce (0 :: Prelude.Integer))))
          else Return (Const (Bit 0) (unsafeCoerce (0 :: Prelude.Integer)))))".

Extract Constant readRegsListHelper => "(\curr k acc sz t paths ->
  let arr = Data.Vector.fromList paths
      len = Data.Vector.length arr
  in \idx -> LetExp """" (Bit sz) idx (\idxVal ->
       let i = (unsafeCoerce idxVal :: Prelude.Integer) Prelude.- curr
           iInt = Prelude.fromIntegral i
       in if iInt Prelude.>= 0 Prelude.&& iInt Prelude.< len
          then let rk = Data.Vector.unsafeIndex arr iInt
               in ReadReg """" (rk_path t k rk) (\val ->
                    case acc of
                      [] -> Return (Var k val)
                      _  -> Return (Or k (Var k val : acc)))
          else case acc of
                 [] -> Return (Const k (getDefault k))
                 _  -> Return (Or k acc)))".

Extract Constant toAction => "(\_ k le ->
  let evalLet cur = case unsafeCoerce cur of
        RetE e -> evalExpr k (unsafeCoerce e)
        SystemE _ cont -> evalLet cont
        LetEx _ _ le0 cont -> evalLet (unsafeCoerce (cont (unsafeCoerce (evalLet le0))))
        IfElseE _ p _ t f cont ->
          let cond = unsafeCoerce (evalExpr Bool (unsafeCoerce p)) :: Prelude.Bool
              res = if cond then evalLet t else evalLet f
          in evalLet (unsafeCoerce (cont (unsafeCoerce res)))
  in Return (Var k (unsafeCoerce (evalLet le))))".

(* This is handled by a hack in evalExpr (evalE of evalExpr), passing it as a ReadArray.
   If evalExpr is removed, these two lines should also be removed *)
Extract Constant ArrayRotl => "(\n k arr p shamt -> ReadArray n (-1) k arr shamt)".
Extract Constant ArrayRotr => "(\n k arr p shamt -> ReadArray n (-2) k arr shamt)".

(* High-Speed Self-Contained Expression Evaluation *)
Extract Constant evalExpr => "(\_ e0 ->
  let kSize k = case k of
        Bool -> 1
        Bit n -> n
        Struct ls -> Data.List.foldl' (\acc (_, k') -> acc Prelude.+ kSize k') 0 ls
        Array n k0 -> (Prelude.fromIntegral n :: Prelude.Integer) Prelude.* kSize k0
        TaggedUnion ls ->
          let tagSz = Prelude.fromIntegral (log2_up (Prelude.fromIntegral (Prelude.length ls)))
              maxData = Data.List.foldl' (\acc (_, k') -> Prelude.max acc (kSize k')) 0 ls
          in tagSz Prelude.+ maxData

      toBit k v = case k of
        Bit _ -> unsafeCoerce v
        Bool -> if unsafeCoerce v then 1 else 0
        Array n k' -> case k' of
          Bit m ->
            let ksz = Prelude.fromIntegral m
                mask = Data.Bits.shiftL 1 ksz Prelude.- 1
                vArr = unsafeCoerce v :: Data.Vector.Vector Prelude.Integer
                len = Data.Vector.length vArr
                loop i acc sh =
                  if i Prelude.>= len then acc
                  else let elemVal = Data.Vector.unsafeIndex vArr i
                           acc' = acc Data.Bits..|. Data.Bits.shiftL (elemVal Data.Bits..&. mask) sh
                       in acc' `Prelude.seq` loop (i Prelude.+ 1) acc' (sh Prelude.+ ksz)
            in loop 0 0 0
          Bool ->
            let vArr = unsafeCoerce v :: Data.Vector.Vector Prelude.Bool
                len = Data.Vector.length vArr
                loop i acc =
                  if i Prelude.>= len then acc
                  else let b = Data.Vector.unsafeIndex vArr i
                           acc' = if b then Data.Bits.setBit acc i else acc
                       in acc' `Prelude.seq` loop (i Prelude.+ 1) acc'
            in loop 0 0
          _ ->
            let ksz = Prelude.fromIntegral (kSize k')
                mask = Data.Bits.shiftL 1 ksz Prelude.- 1
                vArr = unsafeCoerce v :: Data.Vector.Vector Type
                len = Data.Vector.length vArr
                loop i acc sh =
                  if i Prelude.>= len then acc
                  else let elemVal = Data.Vector.unsafeIndex vArr i
                           b = toBit k' elemVal
                           acc' = acc Data.Bits..|. Data.Bits.shiftL (b Data.Bits..&. mask) sh
                       in acc' `Prelude.seq` loop (i Prelude.+ 1) acc' (sh Prelude.+ ksz)
            in loop 0 0 0
        Struct ls ->
          let goFields [] _ acc = acc
              goFields ((_, k1) : rest) vTuple acc =
                let (v1, vRest) = unsafeCoerce vTuple
                    b1 = toBit k1 v1
                    sz = Prelude.fromIntegral (kSize k1)
                    acc' = Data.Bits.shiftL acc sz Data.Bits..|. (b1 Data.Bits..&. (Data.Bits.shiftL 1 sz Prelude.- 1))
                in acc' `Prelude.seq` goFields rest vRest acc'
          in goFields ls (unsafeCoerce v) 0
        TaggedUnion ls ->
          let (dVal, tVal) = unsafeCoerce v
              tagSz = Prelude.fromIntegral (log2_up (Prelude.fromIntegral (Prelude.length ls)))
              bData = unsafeCoerce dVal :: Prelude.Integer
              bTag = unsafeCoerce tVal :: Prelude.Integer
          in Data.Bits.shiftL bData tagSz Data.Bits..|. bTag

      fromBit k v0 =
        let v = v0 :: Prelude.Integer in
        case k of
        Bit _ -> unsafeCoerce v
        Bool -> unsafeCoerce (v Prelude.== 1)
        Array n k' -> case k' of
          Bit m ->
            let nInt = Prelude.fromIntegral n
                ksz = Prelude.fromIntegral m
                mask = Data.Bits.shiftL 1 ksz Prelude.- 1
            in unsafeCoerce (Data.Vector.generate nInt (\i ->
                 Data.Bits.shiftR v (i Prelude.* ksz) Data.Bits..&. mask))
          Bool ->
            let nInt = Prelude.fromIntegral n
            in unsafeCoerce (Data.Vector.generate nInt (\i ->
                 Data.Bits.testBit v i))
          _ ->
            let nInt = Prelude.fromIntegral n
                ksz = Prelude.fromIntegral (kSize k')
                mask = Data.Bits.shiftL 1 ksz Prelude.- 1
            in unsafeCoerce (Data.Vector.generate nInt (\i ->
                 fromBit k' (Data.Bits.shiftR v (i Prelude.* ksz) Data.Bits..&. mask)))
        Struct ls ->
          let totalSz = Prelude.fromIntegral (kSize (Struct ls))
              unpackFields [] _ _ = unsafeCoerce ()
              unpackFields ((_, k1) : rest) remSz remVal =
                let sz = Prelude.fromIntegral (kSize k1)
                    nextRemSz = remSz Prelude.- sz
                    mask = Data.Bits.shiftL 1 sz Prelude.- 1
                    b1 = Data.Bits.shiftR remVal nextRemSz Data.Bits..&. mask
                    v1 = fromBit k1 b1
                in unsafeCoerce (v1, unpackFields rest nextRemSz remVal)
          in unpackFields ls totalSz v
        TaggedUnion ls ->
          let dataSz = Prelude.fromIntegral (max_list (Prelude.map (kSize Prelude.. Prelude.snd) ls))
              tagSz = Prelude.fromIntegral (log2_up (Prelude.fromIntegral (Prelude.length ls)))
              maskData = Data.Bits.shiftL 1 dataSz Prelude.- 1
              maskTag = Data.Bits.shiftL 1 tagSz Prelude.- 1
              dVal = v Data.Bits..&. maskData
              tVal = Data.Bits.shiftR v dataSz Data.Bits..&. maskTag
          in unsafeCoerce (dVal, tVal)

      kEq k v1 v2 = case k of
        Bool -> (unsafeCoerce v1 :: Prelude.Bool) Prelude.== (unsafeCoerce v2 :: Prelude.Bool)
        Bit _ -> (unsafeCoerce v1 :: Prelude.Integer) Prelude.== (unsafeCoerce v2 :: Prelude.Integer)
        Array n k' ->
          let arr1 = unsafeCoerce v1 :: Data.Vector.Vector Type
              arr2 = unsafeCoerce v2 :: Data.Vector.Vector Type
              len = Data.Vector.length arr1
              loop i = if i Prelude.>= len then Prelude.True
                       else if kEq k' (Data.Vector.unsafeIndex arr1 i) (Data.Vector.unsafeIndex arr2 i)
                            then loop (i Prelude.+ 1)
                            else Prelude.False
          in loop 0
        Struct ls ->
          let go [] _ _ = Prelude.True
              go ((_, kField) : rest) tup1 tup2 =
                let (h1, r1) = unsafeCoerce tup1
                    (h2, r2) = unsafeCoerce tup2
                in if kEq kField h1 h2 then go rest r1 r2 else Prelude.False
          in go ls v1 v2
        TaggedUnion ls ->
          let (d1, t1) = unsafeCoerce v1 :: (Type, Prelude.Integer)
              (d2, t2) = unsafeCoerce v2 :: (Type, Prelude.Integer)
          in t1 Prelude.== t2 Prelude.&& (unsafeCoerce d1 :: Prelude.Integer) Prelude.== (unsafeCoerce d2 :: Prelude.Integer)

      kNot k v = case k of
        Bool -> unsafeCoerce (Prelude.not (unsafeCoerce v :: Prelude.Bool))
        Bit n -> let mask = Data.Bits.shiftL 1 (Prelude.fromIntegral n) Prelude.- 1
                 in unsafeCoerce (Data.Bits.xor mask (unsafeCoerce v :: Prelude.Integer))
        Array n k' ->
          let arr = unsafeCoerce v :: Data.Vector.Vector Type
          in unsafeCoerce (Data.Vector.map (kNot k') arr)
        Struct ls ->
          let go [] _ = unsafeCoerce ()
              go ((_, kField) : rest) tup =
                let (h, r) = unsafeCoerce tup
                in unsafeCoerce (kNot kField h, go rest r)
          in go ls v
        TaggedUnion ls ->
          let (d, t) = unsafeCoerce v :: (Type, Prelude.Integer)
              dataSz = max_list (Prelude.map (kSize Prelude.. Prelude.snd) ls)
              mask = Data.Bits.shiftL 1 (Prelude.fromIntegral dataSz) Prelude.- 1
              notD = Data.Bits.xor mask (unsafeCoerce d :: Prelude.Integer)
          in unsafeCoerce (notD, t)

      kOr k v1 v2 = case k of
        Bool -> unsafeCoerce ((unsafeCoerce v1 :: Prelude.Bool) Prelude.|| (unsafeCoerce v2 :: Prelude.Bool))
        Bit n -> let mask = Data.Bits.shiftL 1 (Prelude.fromIntegral n) Prelude.- 1
                 in unsafeCoerce (((unsafeCoerce v1 :: Prelude.Integer) Data.Bits..|. (unsafeCoerce v2 :: Prelude.Integer)) Data.Bits..&. mask)
        Array n k' ->
          unsafeCoerce (Data.Vector.zipWith (kOr k') (unsafeCoerce v1) (unsafeCoerce v2))
        Struct ls ->
          let go [] _ _ = unsafeCoerce ()
              go ((_, k') : rest) t1 t2 =
                let (h1, r1) = unsafeCoerce t1
                    (h2, r2) = unsafeCoerce t2
                in unsafeCoerce (kOr k' h1 h2, go rest r1 r2)
          in go ls v1 v2
        TaggedUnion ls ->
          let (d1, t1) = unsafeCoerce v1 :: (Type, Prelude.Integer)
              (d2, t2) = unsafeCoerce v2 :: (Type, Prelude.Integer)
          in unsafeCoerce ((unsafeCoerce d1 :: Prelude.Integer) Data.Bits..|. (unsafeCoerce d2 :: Prelude.Integer),
                           (t1 Data.Bits..|. t2))

      kAnd k v1 v2 = case k of
        Bool -> unsafeCoerce ((unsafeCoerce v1 :: Prelude.Bool) Prelude.&& (unsafeCoerce v2 :: Prelude.Bool))
        Bit n -> let mask = Data.Bits.shiftL 1 (Prelude.fromIntegral n) Prelude.- 1
                 in unsafeCoerce (((unsafeCoerce v1 :: Prelude.Integer) Data.Bits..&. (unsafeCoerce v2 :: Prelude.Integer)) Data.Bits..&. mask)
        Array n k' ->
          unsafeCoerce (Data.Vector.zipWith (kAnd k') (unsafeCoerce v1) (unsafeCoerce v2))
        Struct ls ->
          let go [] _ _ = unsafeCoerce ()
              go ((_, k') : rest) t1 t2 =
                let (h1, r1) = unsafeCoerce t1
                    (h2, r2) = unsafeCoerce t2
                in unsafeCoerce (kAnd k' h1 h2, go rest r1 r2)
          in go ls v1 v2
        TaggedUnion ls ->
          let (d1, t1) = unsafeCoerce v1 :: (Type, Prelude.Integer)
              (d2, t2) = unsafeCoerce v2 :: (Type, Prelude.Integer)
          in unsafeCoerce ((unsafeCoerce d1 :: Prelude.Integer) Data.Bits..&. (unsafeCoerce d2 :: Prelude.Integer),
                           (t1 Data.Bits..&. t2))

      kXor k v1 v2 = case k of
        Bool -> unsafeCoerce ((unsafeCoerce v1 :: Prelude.Bool) Prelude./= (unsafeCoerce v2 :: Prelude.Bool))
        Bit n -> let mask = Data.Bits.shiftL 1 (Prelude.fromIntegral n) Prelude.- 1
                 in unsafeCoerce (Data.Bits.xor (unsafeCoerce v1 :: Prelude.Integer) (unsafeCoerce v2 :: Prelude.Integer) Data.Bits..&. mask)
        Array n k' ->
          unsafeCoerce (Data.Vector.zipWith (kXor k') (unsafeCoerce v1) (unsafeCoerce v2))
        Struct ls ->
          let go [] _ _ = unsafeCoerce ()
              go ((_, k') : rest) t1 t2 =
                let (h1, r1) = unsafeCoerce t1
                    (h2, r2) = unsafeCoerce t2
                in unsafeCoerce (kXor k' h1 h2, go rest r1 r2)
          in go ls v1 v2
        TaggedUnion ls ->
          let (d1, t1) = unsafeCoerce v1 :: (Type, Prelude.Integer)
              (d2, t2) = unsafeCoerce v2 :: (Type, Prelude.Integer)
          in unsafeCoerce (Data.Bits.xor (unsafeCoerce d1 :: Prelude.Integer) (unsafeCoerce d2 :: Prelude.Integer),
                           Data.Bits.xor t1 t2)

      kReadStruct tup p =
        let go t 0 = case unsafeCoerce t of (a, _) -> a
            go t n = case unsafeCoerce t of (_, rest) -> go rest (n Prelude.- 1)
        in go tup (p :: Prelude.Integer)

      kUpdStruct tup p val =
        let go t 0 = case unsafeCoerce t of (_, rest) -> unsafeCoerce (val, rest)
            go t n = case unsafeCoerce t of (h, rest) -> unsafeCoerce (h, go rest (n Prelude.- 1))
        in go tup (p :: Prelude.Integer)

      kMapStruct f ls tup =
        let go [] _ = unsafeCoerce ()
            go (_ : rest) t =
              let (h, r) = unsafeCoerce t
              in unsafeCoerce (f h, go rest r)
        in go ls tup

      invDefault k = kNot k (getDefault k)

      nth_pf ls i = Data.List.genericIndex ls (i :: Prelude.Integer)

      evalE e = case e of
        Var _ v -> v
        Const _ v -> v
        Or k ls -> case k of
          Bool -> unsafeCoerce (Data.List.foldl' (\acc x -> acc Prelude.|| unsafeCoerce (evalE x)) Prelude.False ls)
          Bit n -> let mask = Data.Bits.shiftL 1 (Prelude.fromIntegral n) Prelude.- 1
                   in unsafeCoerce (Data.List.foldl' (\acc x -> acc Data.Bits..|. (unsafeCoerce (evalE x) :: Prelude.Integer)) 0 ls Data.Bits..&. mask)
          _ -> Data.List.foldl' (kOr k) (getDefault k) (Prelude.map evalE ls)
        And k ls -> case k of
          Bool -> unsafeCoerce (Data.List.foldl' (\acc x -> acc Prelude.&& unsafeCoerce (evalE x)) Prelude.True ls)
          Bit n -> let mask = Data.Bits.shiftL 1 (Prelude.fromIntegral n) Prelude.- 1
                   in unsafeCoerce (Data.List.foldl' (\acc x -> acc Data.Bits..&. (unsafeCoerce (evalE x) :: Prelude.Integer)) mask ls)
          _ -> Data.List.foldl' (kAnd k) (invDefault k) (Prelude.map evalE ls)
        Xor k ls -> case k of
          Bool -> unsafeCoerce (Data.List.foldl' (\acc x -> acc Prelude./= unsafeCoerce (evalE x)) Prelude.False ls)
          Bit n -> let mask = Data.Bits.shiftL 1 (Prelude.fromIntegral n) Prelude.- 1
                   in unsafeCoerce (Data.List.foldl' (\acc x -> Data.Bits.xor acc (unsafeCoerce (evalE x) :: Prelude.Integer)) 0 ls Data.Bits..&. mask)
          _ -> Data.List.foldl' (kXor k) (getDefault k) (Prelude.map evalE ls)
        Not k v -> case k of
          Bool -> unsafeCoerce (Prelude.not (unsafeCoerce (evalE v)))
          Bit n -> let mask = Data.Bits.shiftL 1 (Prelude.fromIntegral n) Prelude.- 1
                   in unsafeCoerce (Data.Bits.xor mask (unsafeCoerce (evalE v) :: Prelude.Integer))
          _ -> kNot k (evalE v)
        TruncLsb msb lsb v ->
          let mask = Data.Bits.shiftL 1 (Prelude.fromIntegral lsb) Prelude.- 1
              vVal = unsafeCoerce (evalE v) :: Prelude.Integer
          in unsafeCoerce (vVal Data.Bits..&. mask)
        TruncMsb msb lsb v ->
          let mask = Data.Bits.shiftL 1 (Prelude.fromIntegral msb) Prelude.- 1
              vVal = unsafeCoerce (evalE v) :: Prelude.Integer
          in unsafeCoerce (Data.Bits.shiftR vVal (Prelude.fromIntegral lsb) Data.Bits..&. mask)
        UXor n v ->
          let vVal = unsafeCoerce (evalE v) :: Prelude.Integer
          in unsafeCoerce (Prelude.odd (Data.Bits.popCount vVal))
        Add n ls ->
          let mask = Data.Bits.shiftL 1 (Prelude.fromIntegral n) Prelude.- 1
              s = Data.List.foldl' (\acc x -> acc Prelude.+ (unsafeCoerce (evalE x) :: Prelude.Integer)) 0 ls
          in unsafeCoerce (s Data.Bits..&. mask)
        Mul n ls ->
          let mask = Data.Bits.shiftL 1 (Prelude.fromIntegral n) Prelude.- 1
              p = Data.List.foldl' (\acc x -> acc Prelude.* (unsafeCoerce (evalE x) :: Prelude.Integer)) 1 ls
          in unsafeCoerce (p Data.Bits..&. mask)
        Div n a b ->
          let mask = Data.Bits.shiftL 1 (Prelude.fromIntegral n) Prelude.- 1
              va = unsafeCoerce (evalE a) :: Prelude.Integer
              vb = unsafeCoerce (evalE b) :: Prelude.Integer
          in unsafeCoerce (if vb Prelude.== 0 then mask else (va `Prelude.quot` vb) Data.Bits..&. mask)
        Rem n a b ->
          let va = unsafeCoerce (evalE a) :: Prelude.Integer
              vb = unsafeCoerce (evalE b) :: Prelude.Integer
          in unsafeCoerce (if vb Prelude.== 0 then va else va `Prelude.rem` vb)
        Sll n m a b ->
          let mask = Data.Bits.shiftL 1 (Prelude.fromIntegral n) Prelude.- 1
              va = unsafeCoerce (evalE a) :: Prelude.Integer
              shamt = unsafeCoerce (evalE b) :: Prelude.Integer
          in unsafeCoerce (Data.Bits.shiftL va (Prelude.fromIntegral shamt) Data.Bits..&. mask)
        Srl n m a b ->
          let va = unsafeCoerce (evalE a) :: Prelude.Integer
              shamt = unsafeCoerce (evalE b) :: Prelude.Integer
          in unsafeCoerce (Data.Bits.shiftR va (Prelude.fromIntegral shamt))
        Sra n m a b ->
          let nInt = Prelude.fromIntegral n
              mask = Data.Bits.shiftL 1 nInt Prelude.- 1
              half = Data.Bits.shiftL 1 (nInt Prelude.- 1)
              va = unsafeCoerce (evalE a) :: Prelude.Integer
              shamt = unsafeCoerce (evalE b) :: Prelude.Integer
              sva = if va Prelude.>= half then va Prelude.- Data.Bits.shiftL 1 nInt else va
          in unsafeCoerce (Data.Bits.shiftR sva (Prelude.fromIntegral shamt) Data.Bits..&. mask)
        Concat msb lsb a b ->
          let va = unsafeCoerce (evalE a) :: Prelude.Integer
              vb = unsafeCoerce (evalE b) :: Prelude.Integer
          in unsafeCoerce (Data.Bits.shiftL va (Prelude.fromIntegral lsb) Data.Bits..|. vb)
        ITE k p t f ->
          if unsafeCoerce (evalE p) then evalE t else evalE f
        Eq0 k a b ->
          case k of
            Bool -> unsafeCoerce ((unsafeCoerce (evalE a) :: Prelude.Bool) Prelude.== (unsafeCoerce (evalE b) :: Prelude.Bool))
            Bit _ -> unsafeCoerce ((unsafeCoerce (evalE a) :: Prelude.Integer) Prelude.== (unsafeCoerce (evalE b) :: Prelude.Integer))
            _ -> unsafeCoerce (kEq k (evalE a) (evalE b))
        Ult n a b ->
          let va = unsafeCoerce (evalE a) :: Prelude.Integer
              vb = unsafeCoerce (evalE b) :: Prelude.Integer
          in unsafeCoerce (va Prelude.< vb)
        ReadStruct ls v i -> kReadStruct (evalE v) (i :: Prelude.Integer)
        ReadArray n m k v i
          -- ArrayRotl
          | m Prelude.== (-1) ->
              let arr = unsafeCoerce (evalE v) :: Data.Vector.Vector Type
                  len = Data.Vector.length arr
                  sh = if len Prelude.> 0 then Prelude.fromIntegral (unsafeCoerce (evalE i) :: Prelude.Integer) `Prelude.mod` len else 0
              in if sh Prelude.== 0 then unsafeCoerce arr
                 else unsafeCoerce (Data.Vector.generate len (\idx ->
                        Data.Vector.unsafeIndex arr ((idx Prelude.+ len Prelude.- sh) `Prelude.mod` len)))
          -- ArrayRotr
          | m Prelude.== (-2) ->
              let arr = unsafeCoerce (evalE v) :: Data.Vector.Vector Type
                  len = Data.Vector.length arr
                  sh = if len Prelude.> 0 then Prelude.fromIntegral (unsafeCoerce (evalE i) :: Prelude.Integer) `Prelude.mod` len else 0
              in if sh Prelude.== 0 then unsafeCoerce arr
                 else unsafeCoerce (Data.Vector.generate len (\idx ->
                        Data.Vector.unsafeIndex arr ((idx Prelude.+ sh) `Prelude.mod` len)))
          | Prelude.otherwise ->
              let arr = unsafeCoerce (evalE v) :: Data.Vector.Vector Type
                  idx = unsafeCoerce (evalE i) :: Prelude.Integer
                  idxInt = Prelude.fromIntegral idx
              in if idxInt Prelude.>= 0 Prelude.&& idxInt Prelude.< Data.Vector.length arr
                 then Data.Vector.unsafeIndex arr idxInt
                 else getDefault k
        ReadArrayConst n k v i ->
          let arr = unsafeCoerce (evalE v) :: Data.Vector.Vector Type
          in Data.Vector.unsafeIndex arr (Prelude.fromIntegral (i :: Prelude.Integer))
        UpdateStruct ls vs p v ->
          kUpdStruct (evalE vs) (p :: Prelude.Integer) (evalE v)
        UpdateArray n k vs m i v ->
          let arr = unsafeCoerce (evalE vs) :: Data.Vector.Vector Type
              idx = unsafeCoerce (evalE i) :: Prelude.Integer
              idxInt = Prelude.fromIntegral idx
          in if idxInt Prelude.>= 0 Prelude.&& idxInt Prelude.< Data.Vector.length arr
             then unsafeCoerce (Data.Vector.modify (\mv -> Data.Vector.Mutable.unsafeWrite mv idxInt (evalE v)) arr)
             else unsafeCoerce arr
        UpdateArrayConst n k vs p v ->
          let arr = unsafeCoerce (evalE vs) :: Data.Vector.Vector Type
              idxInt = Prelude.fromIntegral (p :: Prelude.Integer)
          in if idxInt Prelude.>= 0 Prelude.&& idxInt Prelude.< Data.Vector.length arr
             then unsafeCoerce (Data.Vector.modify (\mv -> Data.Vector.Mutable.unsafeWrite mv idxInt (evalE v)) arr)
             else unsafeCoerce arr
        ToBit k v -> unsafeCoerce (toBit k (evalE v))
        FromBit k v -> fromBit k (unsafeCoerce (evalE v) :: Prelude.Integer)
        ReadUnionTag ls e i ->
          let (_, tag) = unsafeCoerce (evalE e) :: (Type, Prelude.Integer)
          in unsafeCoerce (tag Prelude.== (i :: Prelude.Integer))
        ReadUnionData ls e i ->
          let (dVal, _) = unsafeCoerce (evalE e) :: (Prelude.Integer, Prelude.Integer)
          in fromBit (snd (nth_pf ls i)) dVal
        BuildUnion ls i e ->
          let kField = snd (nth_pf ls i)
              dVal = toBit kField (evalE e)
          in unsafeCoerce (dVal, i :: Prelude.Integer)
        BuildStruct ls vs -> kMapStruct evalE ls vs
        BuildArray n k vs -> unsafeCoerce (Data.Vector.map evalE vs)
  in evalE e0)".
