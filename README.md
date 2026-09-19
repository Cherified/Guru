# Super Kami Guru: The next version of Kami

This will be a rewrite of the second version of the Kami infrastucture for formal verification of hardware and software systems using Rocq/Coq.
In some sense that makes it the third version of Kami.
For those curious, the first version of Kami was developed when I was a grad student at MIT (see [this](http://plv.csail.mit.edu/kami/) for the project page, publications and the github repository for the first version).
The second version of Kami was developed when I was at SiFive (see [this](https://github.com/SiFive/Kami)) and subsequently ported to my personal github (see [this](https://github.com/vmurali/Kami)).

The reason for the complete rewrite of Kami into Guru is because of the lessons learnt in the last decade using Kami.
## Motivation and Key Implications

The goal of Guru is to simplify hardware semantics and verification considerably. In Guru, modules are a **shallow embedding** (used purely for modular organization and reasoning) rather than a deep embedding with method invocations in the core semantics. This design has several major implications:

1. **Pure Atomic Actions and Local Reasoning (Like Single-Threaded Software)**
   Guru's semantics is built entirely on pure atomic actions, without needing constructs like Bluespec's Ephemeral History Registers (EHRs, which violate reasoning about actions as if they executed in an arbitrary order one at a time). When reasoning about an atomic action, the entire system state outside that action is fixed. This allows us to reason about hardware in the exact same way we reason about single-threaded software: only the current statement (action) matters, and the state is fixed when it executes.

2. **Schedule-Independent Proofs and Automatic Bypass Networks (Single-Cycle, Pipelined, and Superscalar)**
   Because correctness is proved at the granularity of individual atomic actions, **the formal proof is completely independent of how those actions are scheduled into hardware clock cycles**.
   When atomic actions are sequenced within the same clock cycle, the compiler threads the updated state combinationally from one action to the next—**automatically creating the hardware bypass/forwarding network**:
   - **Single-cycle processor**: Scheduling `Fetch, Decode, Execute, Memory, Writeback` in that order threads the state through all stages in a single clock cycle.
   - **Pipelined processor**: Scheduling the exact same actions in reverse order (`Writeback, Memory, Execute, Decode, Fetch`) produces a 5-stage pipeline and **automatically generates the bypass paths** from later pipeline stages (`Writeback`, `Memory`) back to earlier stages (`Execute`, `Decode`) within the same cycle.
   - **Superscalar processor**: Scheduling multiple instances of the stage actions within the same cycle (`Writeback_1, Writeback_2, ..., Fetch_1, Fetch_2`) produces a superscalar processor with all inter-stage and intra-cycle forwarding/bypass paths generated automatically—all while preserving the exact same formal proof.

3. **Clock-Domain Crossing (CDC) Without Changing the Formal Proof**
   Because correctness in Guru is defined over atomic actions and is independent of the cycle latency between when a register is written and when it is read (as long as there is no other path informing another action of the write), placing actions in different clock domains requires **zero changes to the formal proof**. Guru enforces the CDC constraints statically at compile time and automatically inserts the hardware synchronizers.

Please add `(setq coq-smie-user-tokens '((";" . "; equations")))` and `(setq coq-smie-monadic-tokens nil)` in your `$HOME/.emacs` to speed up proofgeneral's indentation.

To build the Coq proofs, generate the SystemVerilog RTL (`Example/*/Rtl.sv`), compile the Verilator testbenches (`Example/*/obj_dir/Vtb`), and build the native Haskell simulators (`Example/*/Simulate`) from the `Guru` directory:

```
make          # Compile Coq files and extract Haskell
make rtl      # Generate Example/*/Rtl.sv
make rtlsim   # Build Verilator binaries Example/*/obj_dir/Vtb
make sim      # Build native simulator binaries Example/*/Simulate
```

Please pin the latest version of Rocq stdlib to get Zmod library (as of June 1 2025; I used opam pin to pin rocq-stdlib to https://github.com/rocq-prover/stdlib master branch).

[Here](https://www.youtube.com/watch?v=hcL46NjFDJU&list=PL6EC7B047181AD013&t=525s) is a fun trivia about the name **Guru**.
