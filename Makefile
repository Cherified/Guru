# Copyright (c) 2025-2026 Cherified Systems LLC
#
# SPDX-License-Identifier: MIT

include Makefile.basic

.PHONY: all rtl rtlexe simrtl simrtlexe

.DEFAULT_GOAL = all

TARGETS := $(wildcard Example/*/)

$(foreach dir,$(TARGETS),$(eval $(call Main_rule,$(dir))))

# Example/Gallina uses the specification-only CallGallina, so it has no synthesizable RTL
SYNTH_TARGETS := $(filter-out Example/Gallina/,$(TARGETS))

RTLS := $(patsubst %/,%/Rtl.sv,$(SYNTH_TARGETS))
RTLEXES := $(patsubst %/,%/obj_dir/Vtb,$(SYNTH_TARGETS))
SIMRTLS := $(patsubst %/,%/SimRtl.sv,$(TARGETS))
SIMRTLEXES := $(patsubst %/,%/sim_obj_dir/Vtb,$(TARGETS))

all: coq
rtl: $(RTLS)
rtlexe: $(RTLEXES)
simrtl: $(SIMRTLS)
simrtlexe: $(SIMRTLEXES)
