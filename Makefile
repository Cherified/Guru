include Makefile.basic

.PHONY: all verilog sim

.DEFAULT_GOAL = all

TARGETS := $(wildcard Example/*/)

$(foreach dir,$(TARGETS),$(eval $(call Main_rule,$(dir))))

VTBS := $(patsubst %/,%/obj_dir/Vtb,$(TARGETS))
SIMS := $(patsubst %/,%/Simulate,$(TARGETS))

all: coq
verilog: $(VTBS)
sim: $(SIMS)
