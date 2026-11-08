# Copyright (c) 2025-2026 Cherified Systems LLC
#
# SPDX-License-Identifier: MIT

# Simulating CallGallina through DPI-C: GallinaShim.cpp plus a GHC static library built from
# PrettyPrinter/GallinaRuntime.hs and the target's Compile.hs. Included by Makefile.basic and
# by client Makefiles (e.g. cheriot/Makefile). Everything below is lazy and expands to nothing
# (a no-op recipe line) when the SimRtl.sv has no Gallina calls.
#
# Usage in a recipe, after SimRtl.sv is built ($(1) = target dir, $(2) = its SimRtl.sv):
#   $(call gallina_lib,<dir>,<SimRtl.sv>)
#   verilator ... $(call gallina_args,<dir>,<SimRtl.sv>)

GURU_DIR := $(abspath $(dir $(lastword $(MAKEFILE_LIST))))

GALLINA_HSINC = $(shell ls -d $$(ghc --print-libdir)/*/rts-*/include | head -n 1)

gallina_used = $(shell grep -l guru_gallina_call $(2) 2>/dev/null)

# Builds <dir>/libgallina.a, reusing the Compile/CodePrinter/ModPrinter objects of the Rtl build
gallina_lib = $(if $(call gallina_used,$(1),$(2)),cd $(GURU_DIR) && ghc --make -staticlib -i./PrettyPrinter -i$(abspath $(1)) ./PrettyPrinter/GallinaRuntime.hs -odir $(abspath $(1)) -hidir $(abspath $(1)) -o $(abspath $(1))/libgallina.a,@true)

gallina_args = $(if $(call gallina_used,$(1),$(2)),$(GURU_DIR)/Verilog/GallinaShim.cpp -CFLAGS -I$(GALLINA_HSINC) -LDFLAGS $(abspath $(1))/libgallina.a -LDFLAGS -liconv -LDFLAGS -lffi)
