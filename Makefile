# Copyright (c) 2025-2026 Cherified Systems LLC
#
# SPDX-License-Identifier: MIT

include Makefile.basic

.PHONY: all rtl rtlexe haskellexe

.DEFAULT_GOAL = all

TARGETS := $(wildcard Example/*/)

$(foreach dir,$(TARGETS),$(eval $(call Main_rule,$(dir))))

RTLS := $(patsubst %/,%/Rtl.sv,$(TARGETS))
RTLEXES := $(patsubst %/,%/obj_dir/Vtb,$(TARGETS))
HASKELLEXES := $(patsubst %/,%/Simulate,$(TARGETS))

all: coq
rtl: $(RTLS)
rtlexe: $(RTLEXES)
haskellexe: $(HASKELLEXES)
