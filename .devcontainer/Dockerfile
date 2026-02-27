FROM rocq/rocq-prover:9.1

USER root

# Install system dependencies
RUN apt-get update && apt-get install -y \
    curl \
    git \
    make \
    ghc \
    cabal-install \
    autoconf \
    flex \
    bison \
    g++ \
    libfl-dev \
    perl \
    python3 \
    help2man \
    && rm -rf /var/lib/apt/lists/*

# Build verilator 5.038 from source
RUN cd /tmp && \
    git clone https://github.com/verilator/verilator.git && \
    cd verilator && \
    git checkout v5.038 && \
    autoconf && \
    ./configure && \
    make -j$(nproc) && \
    make install && \
    cd / && rm -rf /tmp/verilator

USER rocq

# Pin rocq-stdlib to latest master for Zmod library support
RUN eval $(opam env) && opam pin remove rocq-stdlib --yes && opam pin add rocq-stdlib https://github.com/rocq-prover/stdlib.git#master --yes
