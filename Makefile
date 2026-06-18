include Makefile.basic

.PHONY: all

.DEFAULT_GOAL = all

TARGETS := $(wildcard Example/*/)

$(foreach dir,$(TARGETS),$(eval $(call Main_rule,$(dir))))

VTBS := $(patsubst %/,%/obj_dir/Vtb,$(TARGETS))

all: $(VTBS)
