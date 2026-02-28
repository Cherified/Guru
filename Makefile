include Makefile.basic

.PHONY: all

.DEFAULT_GOAL = all

TARGETS := $(wildcard Example/*/)

$(foreach dir,$(TARGETS),$(eval $(call Main_rule,$(dir))))
$(foreach dir,$(TARGETS),$(eval $(call Main_sv_rule,$(dir))))

MAINSVS := $(patsubst %/,%/Main.sv,$(TARGETS))

all: $(MAINSVS)
