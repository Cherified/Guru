From Stdlib Require Import String ZArith List Zmod Bool.
Require Import Guru.Library Guru.Syntax Guru.Semantics Guru.Extraction.

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

Fixpoint initSimStateIO (t: Tree Elem) : IO (TreeState SimElemState t) :=
  match t return IO (TreeState SimElemState t) with
  | Leaf _ e => initSimElemIO e
  | Node _ children =>
      (fix loop (ls: list (Tree Elem)) : IO (ListTreeState SimElemState ls) :=
         match ls return IO (ListTreeState SimElemState ls) with
         | nil => io_ret tt
         | x :: xs =>
             io_bind (initSimStateIO x) (fun sx =>
             io_bind (loop xs) (fun sxs =>
             io_ret (sx ,, sxs)))
         end) children
  end.

Parameter castSimReg : forall {t: Tree Elem} (x: RegPath t),
  SimElemState (getLeaf x.(regPath)) -> IoReg (type (regKind (getRegFromPath x))).

Parameter castSimMem : forall {t: Tree Elem} (x: MemPath t),
  SimElemState (getLeaf x.(memPath)) -> IoMem (type (getMemFromPath x).(memKind)) ** IoMem (type (getMemFromPath x).(memKind)).

Parameter io_putStr : string -> IO unit.
Parameter io_finish : IO unit.
Parameter io_dispVal : forall {k: Kind}, type k -> FullFormat k -> IO unit.

Section SimLoop.
  Variable t: Tree Elem.

  Fixpoint evalSysT (st: SysT type) : IO unit :=
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
  Fixpoint evalActionIO {k: Kind} (st: TreeState SimElemState t) (act: Action type t k) : IO (type k) :=
    match act with
    | ReadReg s path cont =>
        let reg := castSimReg path (readTreeState t st path.(regPath)) in
        io_bind (readReg reg) (fun val => evalActionIO st (cont val))
    | WriteReg path v cont =>
        let reg := castSimReg path (readTreeState t st path.(regPath)) in
        io_bind (writeReg reg (evalExpr v)) (fun _ => evalActionIO st cont)
    | ReadRqMem path idx p cont =>
        let mem := castSimMem path (readTreeState t st path.(memPath)) in
        io_bind (readRam mem.(Fst) (Zmod.to_Z (evalExpr idx))) (fun val =>
        io_bind (writeRam mem.(Snd) (Z.of_nat p.(finNum)) val) (fun _ =>
        evalActionIO st cont))
    | ReadRpMem s path p cont =>
        let mem := castSimMem path (readTreeState t st path.(memPath)) in
        io_bind (readRam mem.(Snd) (Z.of_nat p.(finNum))) (fun val =>
        evalActionIO st (cont val))
    | WriteMem path idx v cont =>
        let mem := castSimMem path (readTreeState t st path.(memPath)) in
        io_bind (writeRam mem.(Fst) (Zmod.to_Z (evalExpr idx)) (evalExpr v)) (fun _ => evalActionIO st cont)
    | Send path v cont =>
        evalActionIO st cont
    | Recv s path cont =>
        evalActionIO st (cont (getDefault _))
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
  Fixpoint stepSimIO (st: TreeState SimElemState t) (rules: list (Action type t (Bit 0))) : IO unit :=
    match rules with
    | nil => io_ret tt
    | r :: rs => io_bind (evalActionIO st r) (fun _ => stepSimIO st rs)
    end.

  (* Bounded Multi-Cycle Simulation Loop *)
  Fixpoint loopCyclesIO (n: nat) (st: TreeState SimElemState t) (rules: list (Action type t (Bit 0))) : IO unit :=
    match n with
    | 0 => io_ret tt
    | S k => io_bind (stepSimIO st rules) (fun _ => loopCyclesIO k st rules)
    end.

  Definition evalModCyclesIO (n: nat) (m: Mod t) : IO unit :=
    io_bind (initSimStateIO t) (fun st => loopCyclesIO n st (m type)).

  (* Top-Level Turnkey Simulation Entry Point (Single Cycle) *)
  Definition evalModIO (m: Mod t) : IO unit :=
    io_bind (initSimStateIO t) (fun st => stepSimIO st (m type)).
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
          FBool sz bf -> if unsafeCoerce val then ""1"" else ""0""
          FBit n sz bf ->
            let s = case bf of
                      Hex -> Numeric.showHex (unsafeCoerce val :: Prelude.Integer) """"
                      Decimal -> Prelude.show (unsafeCoerce val :: Prelude.Integer)
                      _ -> Numeric.showIntAtBase 2 Data.Char.intToDigit (unsafeCoerce val :: Prelude.Integer) """"
                p = case bf of { Decimal -> ' ' ; _ -> '0' }
            in Prelude.replicate (Prelude.fromInteger sz Prelude.- Prelude.length s) p Prelude.++ s
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
            in ""{data="" Prelude.++ simFormatVal dVal (FBit 0 0 dataBF) Prelude.++ "", tag="" Prelude.++ simFormatVal tVal (FBit 0 0 tagBF) Prelude.++ ""}""
  in Prelude.putStr (simFormatVal v ff))".

(* High-Speed SameTuple IntMap Extraction Mappings *)
Extract Inductive SameTuple => "Data.IntMap.Strict.IntMap" [ "(Data.IntMap.Strict.fromList Prelude.. Prelude.zip [0..])" ] "(\f st -> f (Data.IntMap.Strict.elems st))".
Extract Constant readSameTuple => "(\_ arr idx -> arr Data.IntMap.Strict.! Prelude.fromInteger idx)".
Extract Constant updSameTuple => "(\_ arr idx val -> Data.IntMap.Strict.insert (Prelude.fromInteger idx) val arr)".
Extract Constant updSameTupleNat => "(\_ arr idx val -> Data.IntMap.Strict.insert (Prelude.fromInteger idx) val arr)".
Extract Constant mapSameTuple => "(\f _ st -> Data.IntMap.Strict.map f st)".
