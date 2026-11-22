<!--
Copyright 2026 Google LLC

SPDX-License-Identifier: MIT
-->

# GuruCirct: a CIRCT backend for Guru

GuruCirct prints a Guru compiled module (the `compiledMod` extracted to `Compile.hs`) as MLIR in
the core dialects of [CIRCT](https://circt.llvm.org) (`hw`, `comb`, `seq` and `sv`). CIRCT
(`circt-opt`) then lowers the MLIR and exports it as SystemVerilog, which Verilator simulates.

It is a counterpart of Guru's `PrettyPrinter` (`Rtl.hs`, `ModPrinter.hs`, `CodePrinter.hs`): the
generated SystemVerilog has the same modules (`core_design`, `top` and `tb`), the same ports and
the same names for state elements, so the testbenches written for `Rtl.sv` and `SimRtl.sv` (such
as those of `cheriot`) work unchanged. Like `PrettyPrinter`, it has two modes:

| Mode | Command | Counterpart of | Sends, Recvs | Memories |
|---|---|---|---|---|
| RTL | `CirctGen` | `Rtl` (`Rtl.sv`) | ports of `top` | instances of `verilog_mem` |
| Simulation | `CirctGen s` | `Rtl s` (`SimRtl.sv`) | methods of `sim_io` | arrays in `core_design` |

The RTL mode needs a valid module (at most one Send and one request per memory port per cycle,
no read after a write of a memory, no `CallGallina`), as `Rtl` does.

## Files

| File | Contents |
|---|---|
| `CirctPrinter.hs` | the printer |
| `Circt.hs` | the main program (`CirctGen`); checks names and validity as `Rtl.hs` does |
| `Makefile` | extracted module to MLIR, to SystemVerilog, to Verilator simulators; comparison with Guru's simulators |
| `test_cheriot.sh` | builds the five CHERIoT simulators and runs the CHERIoT test suite on them |

The printer reuses `PrettyPrinter` (names, display formats, the `sim_io` and Gallina declarations,
the `tb` module) and `Verilog/GuruLibrary.sv` (`verilog_mem`, through an `hw.module.extern` with
`verilogName = "verilog_mem"`), and `Verilog/GallinaShim.cpp` with `PrettyPrinter/GallinaRuntime.hs`
for `CallGallina`, through `Gallina.mk`. No other library is needed.

## Requirements

- CIRCT's `circt-opt`, for instance from a release at https://github.com/llvm/circt/releases
  (tested with `firtool-1.164.0`, `circt-full-static-macos-arm64.tar.gz`). Put its `bin` in `PATH`
  or pass `CIRCT_OPT=<path>` to `make`.
- GHC (tested with 9.14.1) and Verilator (tested with 5.052), as needed for Guru without CIRCT.

## Usage

```
make -C .. coq        # extracts Example/*/Compile.hs
make                  # Example/*: build/<name>/{SimRtl,Rtl}.{mlir,sv} and their simulators
make check            # compare them with Guru's simulators (make -C .. simrtlexe first)
make DESIGNS="<dir>/ ..." sim    # simulation mode of other design directories
make RTL_DESIGNS="<dir>/ ..." rtl  # RTL mode of other design directories
./test_cheriot.sh     # the CHERIoT designs (needs ../../cheriot and ../../SpecCheriot built)
```

For each design, `make` generates these files in `build/<name>/`:

| File | What it is |
|---|---|
| `CirctGen` | the printer, compiled with the design's `Compile.hs` |
| `SimRtl.mlir`, `Rtl.mlir` | the MLIR of the simulation and RTL modes |
| `SimRtl.sv`, `Rtl.sv` | the SystemVerilog CIRCT exports from them |
| `sim_obj_dir/V<top>`, `obj_dir/V<top>` | the Verilator simulators of the two modes |

The SystemVerilog is made with

```
circt-opt <file>.mlir $(CIRCT_PASSES) -o /dev/null > <file>.sv
```

where the Makefile variable `CIRCT_PASSES` defaults to
`--canonicalize --cse --lower-seq-to-sv=disable-reg-randomization --export-verilog`.

By default the simulators use the `tb` module printed with the design. A design with its own
testbench sets these Makefile variables (see `test_cheriot.sh`):

| Variable | Meaning | Default |
|---|---|---|
| `SIM_TB`, `RTL_TB` | testbench file for the simulation and RTL modes; it is copied into `build/<name>/` and includes `SimRtl.sv` / `Rtl.sv` from there | none (use `tb`) |
| `TB_TOP` | top module of the testbench, passed to Verilator as `--top` | `tb` |
| `TB_INC` | extra include directories for the testbench, as `-I<dir>` flags | none |

## How a module is printed

The compiled action of a module is executed symbolically into SSA form. Every temporary is an SSA
value. The register shadows, the Send values and enables and the memory request ports, which the
Verilog of `PrettyPrinter` assigns in program order, are SSA values in an environment.

In both RTL and simulation modes, both branches of an if-then-else are evaluated, and the two
environments (and the returned values) are merged with `comb.mux` on the condition. Side effects
(displays, `Finish`, and in simulation mode Sends, Recvs, memory accesses and `CallGallina`) are
executed under their path conditions: the conjunction of the conditions of the enclosing
if-then-elses.

### RTL mode

`core_design` is pure `hw`/`comb`/`seq`, except for displays and `NonDet`:

- a register is a `seq.firreg` with an asynchronous reset to its initial value on `!rst_n` (the
  `always_ff` of `PrettyPrinter`); a register without an initial value has no reset;
- Sends, Recvs and the memory request and response ports are module ports, as in `Rtl.sv`;
- `top` instantiates `core_design` and, for each memory, the module `verilog_mem` of
  `Verilog/GuruLibrary.sv`, with the same parameters (size, element width, number of ports,
  initial contents) as in `Rtl.sv`, so memories behave exactly as in `Rtl.sv`. (CIRCT's own
  memory, `seq.firmem`, was tried and dropped, mainly because CIRCT's
  simulation model of it is wrong: it ignores read-under-write,
  https://github.com/llvm/circt/issues/11662. Also, CIRCT does not generate SRAMs: it turns a
  `seq.firmem` either into a behavioral Verilog model, as `verilog_mem` is, or into an empty
  module to be filled by an external SRAM generator, so it offers nothing over `verilog_mem` here.)
- displays and `Finish` are executed by an `always @(posedge clk)` block, out of reset. `Rtl.sv`
  executes them in its `always_comb` block, so it may print more often;
- `NonDet` is a register that gets `$urandom` values at every clock edge (in `Rtl.sv` it is a
  `$urandom` call in the `always_comb` block).

Generating `hw`/`comb`/`seq` is more complex than generating procedural `sv` code that mirrors
`Rtl.sv`. It was done for two reasons:
- CIRCT's ExportVerilog mishandles procedural code (see the end of Simulation mode).
- CIRCT's tools work on the core dialects: canonicalization and CSE do little with procedural
  `sv` code, and synthesis (`circt-synth`), equivalence checking (`circt-lec`) and simulation
  (`arcilator`) need `hw`/`comb`/`seq`.

### Simulation mode

The result of a side effect (a Recv, a memory read, `NonDet`, `CallGallina`) feeds the rest of the
clock cycle, and the CHERIoT specifications, for instance, send a memory request and receive the
response in the same cycle. So, as in `SimRtl.sv`, the whole cycle is one
`always @(posedge clk or negedge rst_n)` block in program order:

- a register is an `sv.reg`, read at the start of the cycle and written at the end with a
  non-blocking assignment, and reset as in `SimRtl.sv`;
- Sends and Recvs call `sim_io.send` and `sim_io.recv` (an `sv.verbatim` and an
  `sv.verbatim.expr.se`), with the `sim_io_t` class of `PrettyPrinter`;
- a memory is an `sv.reg` array, with one response variable per port, initialized by an
  `initial` block; a request or write outside the memory bounds reads 0 or does nothing;
- `NonDet` is `{$urandom(), ...}` and `CallGallina` is the DPI-C call `guru_gallina_call` of
  `PrettyPrinter`, with the same call-site and Gallina-register numbers, so `GallinaRuntime.hs`
  and `GallinaShim.cpp` are used as they are.

Each side effect with a result (for instance a Recv, whose result can depend on earlier Sends of
the same cycle) stores it in a separate variable for each place in the code where it occurs. If
not, a variable shared by two calls would be overwritten by the later call, and since ExportVerilog
replaces a value read from a variable by the variable itself at each use, the earlier call's uses
would see the later result.

### Kinds

| Guru kind | CIRCT type |
|---|---|
| `Bool`, `Bit n` | `i1`, `in` |
| `Struct ls` | `!hw.struct<...>` without the fields of size 0 |
| `Array n k` | `!hw.array<n x k>` (element 0 is the least significant) |
| `TaggedUnion ls` | `!hw.struct<data: iD, tag: iL>` without a part of size 0 |
| any kind of size 0 | no value; reads, writes and ports of it are left out, as in `PrettyPrinter` |

These are the packed layouts of `PrettyPrinter` (first struct field most significant). Struct and
array types get MLIR type aliases (`!gk<n>`).

### Expressions

Expressions follow `evalExpr` of `Semantics.v` and the Verilog of `CodePrinter.ppCExpr`:
`Or`/`And`/`Xor`/`Not` act on the bits (through `hw.bitcast` for structs and arrays), `Add`, `Mul`,
`Div`, `Rem` are `comb.add`, `comb.mul`, `comb.divu`, `comb.modu`; shifts by the width or more give 0
(or the sign bits for `Sra`), as in Verilog; `ReadArray` and `UpdateArray` with an index outside the
array give 0 and leave the array unchanged; `ToBit`/`FromBit` are `hw.bitcast`.

## Checked against the Verilog of PrettyPrinter

`make check` compares the output of the simulators of the Guru examples with that of Guru's
simulation-mode simulators (`+gallina_oracle_zero` on both sides):

| Example | Simulation mode | RTL mode |
|---|---|---|
| Test | the same 100 lines | the same 100 lines |
| Gallina | the same 10 lines (also with `+gallina_seed=7` on both sides) | (no RTL) |
| Fifo, SimpleProcessor | run; neither prints anything | run; neither prints anything |

`test_cheriot.sh` runs the CHERIoT test suite (`cheriot/run_all_tests.sh`: 50 basic tests and the
CHERIoT RTOS `test-suite`) on the CIRCT simulators of the specification, the forwarding and the
pipelined implementations of `cheriot`, and `simpleSpec` and `nondetSpec` of `SpecCheriot`. With
cheriot `5595634` and SpecCheriot `e00d067`, every simulator passes all 51 tests with exactly the
cycle counts of the simulators built from `PrettyPrinter`'s Verilog:

| Design | Mode | Final `[Cycle ...]` of test-suite | "All tests finished in" | test-suite walltime: PrettyPrinter / GuruCirct |
|---|---|---|---|---|
| cheriot spec | simulation | 7218435 | 6846144 | 16.7 s / 34.5 s |
| cheriot Impl/Fwd | simulation | 8492414 | 6773068 | 122.6 s / 160.4 s |
| cheriot Impl (pipelined) | RTL | 10466326 | 6551660 | 77.8 s / 68.4 s |
| SpecCheriot SimpleSim | simulation | 7218435 | 6846144 | 13.6 s / 40.9 s |
| SpecCheriot NondetSim | simulation | 7218435 | 6846144 | 14.1 s / 41.3 s |

(Verilator 5.052 on an Apple M-series machine, several simulators running in parallel.) The
simulation mode is slower than `PrettyPrinter`'s because it evaluates both branches of every
if-then-else, as the RTL mode does, to share that code.

## Known gaps

- Only `circt-opt` has been used. Other CIRCT tools, such as `arcilator`, have not been tried.
  RTL mode could work with them, since its `core_design` is plain `hw`/`comb`/`seq`, apart from
  the displays and `NonDet`.
- In simulation mode the whole cycle is behavioral SystemVerilog (`sv` dialect), since side effects
  happen in program order within the cycle; it is not synthesizable, like `SimRtl.sv`.
- Generated names of intermediate values are CIRCT's (`_GEN_<n>`), not the `let_<name>_<n>` of
  `PrettyPrinter`.

## Reason for complicated code generation for CIRCT

`PrettyPrinter` can print Verilog almost directly from the compiled module: Verilog has nested
expressions, mutable variables assigned in program order, and if-then-else statements, so each
compiled statement becomes one Verilog statement. CIRCT's dialects are lower level, and the
printer has to make up for it:

- No nested expressions: in MLIR every operation is its own line and defines a new, uniquely named
  SSA value, so even a small expression becomes a sequence of lines whose names must be generated.
- No mutable variables in `hw`/`comb`/`seq`: a register, a Send or a memory port written several
  times in a cycle, possibly inside if-then-elses, cannot be assigned like the shadow variables of
  `PrettyPrinter`. The printer keeps the current value of each one while it walks the compiled
  module, and merges the values of the two branches of an if-then-else with `comb.mux`.
- Declarations and statements end up in different places than where they are found: registers
  and other variables are declared at module level, and in RTL mode displays, `Finish` and `NonDet`
  go into a separate `always` block.
- Every operation spells out the types of its operands, so struct and array types would be
  repeated in full; to keep the output a manageable size, they need to get short aliases.
- In simulation mode, ExportVerilog re-reads variables at each use, so values that later code
  needs are kept in variables that are written only once per cycle.

All of this needs state carried along while printing (the lines printed so far, the next fresh
name, the aliases, the collected declarations), hence a state monad in `CirctPrinter.hs`, and an
environment of current symbolic values passed through the translation of each compiled statement.

## Use of AI

AI was used to write `CirctPrinter.hs`, `Circt.hs`, the `Makefile` and `test_cheriot.sh`.
`CirctPrinter.hs` has been reviewed and fixed by humans, but its reviewers have
only cursory knowledge of the syntax and semantics of the CIRCT dialects it
uses (`hw`, `comb`, `seq` and `sv`). `Circt.hs`, the `Makefile` and
`test_cheriot.sh` have also been reviewed by humans.
