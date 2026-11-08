// Copyright (c) 2025-2026 Cherified Systems LLC
//
// SPDX-License-Identifier: MIT

// DPI-C entry points for simulating CallGallina (see PrettyPrinter/GallinaRuntime.hs).
// Compiled by Verilator (as C++) only for simulators whose SimRtl.sv contains Gallina calls.
//
// Plusargs, read once at the first call:
//   +gallina_seed=N       seed of the CallGallina oracles (default: Verilator's seed,
//                         i.e. +verilator+seed+N)
//   +gallina_oracle_zero  every oracle is fun _ => 0

#include "HsFFI.h"
#include "svdpi.h"
#include "verilated.h"
#include <cstdint>
#include <cstdlib>
#include <cstring>

extern "C" {
void hs_guru_gallina_call(int site, int leaf, long long cycle, const uint32_t* in, uint32_t* out);
void hs_guru_gallina_reset(void);
void hs_guru_gallina_config(unsigned long long seed, int zero);
}

static void guru_gallina_ensure_init() {
  static bool inited = false;
  if (inited) return;
  inited = true;
  hs_init(nullptr, nullptr);
  VerilatedContext* ctx = Verilated::threadContextp();
  unsigned long long seed = static_cast<unsigned int>(ctx->randSeed());
  const char* s = ctx->commandArgsPlusMatch("gallina_seed=");
  if (s && *s) seed = std::strtoull(s + std::strlen("+gallina_seed="), nullptr, 0);
  const char* z = ctx->commandArgsPlusMatch("gallina_oracle_zero");
  int zero = (z && *z) ? 1 : 0;
  hs_guru_gallina_config(seed, zero);
}

extern "C" void guru_gallina_call(int site, int leaf, long long cycle, const svBitVecVal* in, svBitVecVal* out) {
  guru_gallina_ensure_init();
  hs_guru_gallina_call(site, leaf, cycle, reinterpret_cast<const uint32_t*>(in), reinterpret_cast<uint32_t*>(out));
}

extern "C" void guru_gallina_reset() {
  guru_gallina_ensure_init();
  hs_guru_gallina_reset();
}
