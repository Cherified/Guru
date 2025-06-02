# Super Kami Guru: The next version of Kami

This will be a rewrite of the second version of the Kami infrastucture for formal verification of hardware and software systems using Rocq/Coq.
In some sense that makes it the third version of Kami.
For those curious, the first version of Kami was developed when I was a grad student at MIT (see [this](http://plv.csail.mit.edu/kami/) for the project page, publications and the github repository for the first version).
The second version of Kami was developed when I was at SiFive (see [this](https://github.com/SiFive/Kami)) and subsequently ported to my personal github (see [this](https://github.com/vmurali/Kami)).

The reason for the complete rewrite of Kami into Guru is because of the lessons learnt in the last decade using Kami.
The goal is to simplify the semantics considerably; the crux of the simplification involves removing support for modules and method invocations, which leads to a bunch of other simplifications which will be listed on this page shortly.

Please add `(setq coq-smie-user-tokens '((";" . "; equations")))` and `(setq coq-smie-monadic-tokens nil)` in your `$HOME/.emacs` to speed up proofgeneral's indentation.

Right now I create a single verilog file that can be generated (starting from the Guru directory) and compiled using verilator as follows (more for my own notes):

```
export CWD=`pwd` && make && cd PrettyPrinter/ && ./Main > test/test.sv && cd test && verilator --binary --timing -I../../Verilog test.sv; cd $CWD
```

The idea is to create different verilog files for the design, the top level and the test bench, along with command line specifications for where to put these files. All this will come later.

Please pin the latest version of Rocq stdlib to get Zmod library (as of June 1 2025; I used opam pin to pin rocq-stdlib to https://github.com/rocq-prover/stdlib master branch).

[Here](https://www.youtube.com/watch?v=hcL46NjFDJU&list=PL6EC7B047181AD013&t=525s) is a fun trivia about the name **Guru**.
