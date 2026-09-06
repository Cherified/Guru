# Copyright (c) 2025-2026 Cherified Systems LLC
#
# SPDX-License-Identifier: MIT

include Makefile.basic

.PHONY: all rtl rtlsim sim

.DEFAULT_GOAL = all

TARGETS := $(wildcard Example/*/)

$(foreach dir,$(TARGETS),$(eval $(call Main_rule,$(dir))))

RTLS := $(patsubst %/,%/Rtl,$(TARGETS))
VTBS := $(patsubst %/,%/obj_dir/Vtb,$(TARGETS))
SIMS := $(patsubst %/,%/Simulate,$(TARGETS))

all: coq
rtl: $(RTLS)
rtlsim: $(VTBS)
sim: $(SIMS)
