include Makefile.basic

.PHONY: all verilog

.DEFAULT_GOAL = all

TARGETS := $(wildcard Example/*/)

$(foreach dir,$(TARGETS),$(eval $(call Main_rule,$(dir))))

VTBS := $(patsubst %/,%/obj_dir/Vtb,$(TARGETS))

all: coq
verilog: $(VTBS)
