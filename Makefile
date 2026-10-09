# Copyright (c) 2025-2026 Cherified Systems LLC
#
# SPDX-License-Identifier: MIT

include Makefile.basic

.PHONY: all rtl rtlexe simrtl simrtlexe

.DEFAULT_GOAL = all

TARGETS := $(wildcard Example/*/)

$(foreach dir,$(TARGETS),$(eval $(call Main_rule,$(dir))))

RTLS := $(patsubst %/,%/Rtl.sv,$(TARGETS))
RTLEXES := $(patsubst %/,%/obj_dir/Vtb,$(TARGETS))
SIMRTLS := $(patsubst %/,%/SimRtl.sv,$(TARGETS))
SIMRTLEXES := $(patsubst %/,%/sim_obj_dir/Vtb,$(TARGETS))

all: coq
rtl: $(RTLS)
rtlexe: $(RTLEXES)
simrtl: $(SIMRTLS)
simrtlexe: $(SIMRTLEXES)
