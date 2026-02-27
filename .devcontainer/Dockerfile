FROM rocq/rocq-prover:9.1

USER root

# Install system dependencies
RUN apt-get update && apt-get install -y \
    curl \
    git \
    make \
    ghc \
    cabal-install \
    verilator \
    && rm -rf /var/lib/apt/lists/*

USER rocq

# Pin rocq-stdlib to latest master for Zmod library support
RUN eval $(opam env) && opam pin remove rocq-stdlib --yes && opam pin add rocq-stdlib https://github.com/rocq-prover/stdlib.git#master --yes

