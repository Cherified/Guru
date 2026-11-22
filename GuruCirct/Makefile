# Copyright 2026 Google LLC
#
# SPDX-License-Identifier: MIT

# CIRCT (MLIR) versions of Guru designs, the SystemVerilog CIRCT makes of them, and
# Verilator simulators of that SystemVerilog. The Guru tree is only read: every generated
# file goes to build/<design name>/.
#
#   make                          simulation and RTL simulators of the Guru examples
#   make check                    compare their output with Guru's Verilator simulators
#   make DESIGNS=<dirs> sim       simulation-mode simulators of other design directories
#   make DESIGNS=<dirs> rtl       RTL-mode simulators of other design directories
#   make CIRCT_OPT=<path>         circt-opt to use (default: circt-opt in PATH)
#
# Each design directory has an extracted Compile.hs (for the Guru examples: make -C .. coq).
# By default the simulators use the tb module printed with the design. A design written for
# another testbench uses (see test_cheriot.sh):
#   SIM_TB=<file> / RTL_TB=<file>  testbench including SimRtl.sv / Rtl.sv (copied next to it)
#   TB_TOP=<module>                its top module (default tb)
#   TB_INC=<-I flags>              include directories of the testbench

GURU_DIR ?= ..

# Sets GURU_DIR to an absolute path; provides gallina_used, gallina_lib and gallina_args
include $(GURU_DIR)/Gallina.mk

DESIGNS ?= $(wildcard $(GURU_DIR)/Example/*/)
# Example/Gallina uses the specification-only CallGallina, so it has no RTL
RTL_DESIGNS ?= $(filter-out %/Gallina/,$(DESIGNS))

CIRCT_OPT ?= circt-opt
CIRCT_PASSES ?= --canonicalize --cse --lower-seq-to-sv=disable-reg-randomization --export-verilog

SIM_TB ?=
RTL_TB ?=
TB_TOP ?= tb
TB_INC ?=
VERILATOR_FLAGS ?= -Wno-CMPCONST

HASKELLS := Circt.hs CirctPrinter.hs $(wildcard $(GURU_DIR)/PrettyPrinter/*.hs)
FIXLITS := build/tools/FixLits

.PHONY: all sim rtl mlir check clean
.DEFAULT_GOAL = all

$(FIXLITS): $(GURU_DIR)/PrettyPrinter/FixLits.hs
	mkdir -p build/tools
	ghc --make -package text $< -outputdir build/tools -o $@

# $(1) = design directory (with a trailing /), $(2) = its name
define Circt_rule
$(1)Compile.hs:
	@echo "$(1)Compile.hs is missing: extract it first (for the Guru examples: make -C $(GURU_DIR) coq)"
	@false

# A copy of the extracted module, with the fix-ups of Guru's Main_rule
build/$(2)/Compile.hs: $(1)Compile.hs $(FIXLITS)
	mkdir -p build/$(2)
	cp $(1)Compile.hs $$@
	grep -q "import qualified Data" $$@ || $(FIXLITS) $$@
	grep -q "import qualified Data" $$@ || sed -i "/import qualified Prelude/aimport qualified Data.Bits\nimport qualified Data.Char" $$@

build/$(2)/CirctGen: build/$(2)/Compile.hs $(HASKELLS)
	ghc --make -j -i. -i$(GURU_DIR)/PrettyPrinter -ibuild/$(2) -main-is Circt Circt.hs -odir build/$(2) -hidir build/$(2) -o $$@

build/$(2)/SimRtl.mlir: build/$(2)/CirctGen
	build/$(2)/CirctGen s > $$@.tmp && mv $$@.tmp $$@

build/$(2)/Rtl.mlir: build/$(2)/CirctGen
	build/$(2)/CirctGen > $$@.tmp && mv $$@.tmp $$@

build/$(2)/SimRtl.sv: build/$(2)/SimRtl.mlir
	$(CIRCT_OPT) $$< $(CIRCT_PASSES) -o /dev/null > $$@.tmp && mv $$@.tmp $$@

build/$(2)/Rtl.sv: build/$(2)/Rtl.mlir
	$(CIRCT_OPT) $$< $(CIRCT_PASSES) -o /dev/null > $$@.tmp && mv $$@.tmp $$@

build/$(2)/sim_obj_dir/V$(TB_TOP): build/$(2)/SimRtl.sv $(SIM_TB)
	$$(call gallina_lib,build/$(2)/,build/$(2)/SimRtl.sv)
	$(if $(SIM_TB),cp $(SIM_TB) build/$(2)/)
	verilator $(VERILATOR_FLAGS) --top $(TB_TOP) --binary -Ibuild/$(2) -I$(GURU_DIR)/Verilog $(TB_INC) --Mdir build/$(2)/sim_obj_dir build/$(2)/$(if $(SIM_TB),$(notdir $(SIM_TB)),SimRtl.sv) $$(call gallina_args,build/$(2)/,build/$(2)/SimRtl.sv)

build/$(2)/obj_dir/V$(TB_TOP): build/$(2)/Rtl.sv $(RTL_TB)
	$(if $(RTL_TB),cp $(RTL_TB) build/$(2)/)
	verilator $(VERILATOR_FLAGS) --top $(TB_TOP) --binary -Ibuild/$(2) -I$(GURU_DIR)/Verilog $(TB_INC) --Mdir build/$(2)/obj_dir build/$(2)/$(if $(RTL_TB),$(notdir $(RTL_TB)),Rtl.sv)

# The display output of the simulation-mode simulator against that of Guru's SimRtl.sv
# simulator (with every CallGallina oracle set to zero on both sides), and the output of the
# RTL-mode simulator against the same. The RTL-mode simulator prints once per clock cycle,
# out of reset, like the simulation-mode one; Guru's RTL prints from an always_comb block.
check-sim-$(2): build/$(2)/sim_obj_dir/Vtb
	@test -x $(1)sim_obj_dir/Vtb || { echo "$(1)sim_obj_dir/Vtb is missing: build Guru's simulator first"; false; }
	$(1)sim_obj_dir/Vtb +gallina_oracle_zero | grep -v '^- ' > build/$(2)/guru_sim.out || true
	build/$(2)/sim_obj_dir/Vtb +gallina_oracle_zero | grep -v '^- ' > build/$(2)/circt_sim.out || true
	diff build/$(2)/guru_sim.out build/$(2)/circt_sim.out
	@echo "$(2): CIRCT and Guru simulation-mode simulators print the same ($$$$(wc -l < build/$(2)/circt_sim.out) lines)"

check-rtl-$(2): build/$(2)/obj_dir/Vtb
	@test -x $(1)sim_obj_dir/Vtb || { echo "$(1)sim_obj_dir/Vtb is missing: build Guru's simulator first"; false; }
	$(1)sim_obj_dir/Vtb | grep -v '^- ' > build/$(2)/guru_sim.out || true
	build/$(2)/obj_dir/Vtb | grep -v '^- ' > build/$(2)/circt_rtl.out || true
	diff build/$(2)/guru_sim.out build/$(2)/circt_rtl.out
	@echo "$(2): CIRCT RTL-mode and Guru simulation-mode simulators print the same ($$$$(wc -l < build/$(2)/circt_rtl.out) lines)"

.PHONY: check-sim-$(2) check-rtl-$(2)
endef

name_of = $(notdir $(patsubst %/,%,$(1)))

$(foreach dir,$(sort $(DESIGNS) $(RTL_DESIGNS)),$(eval $(call Circt_rule,$(dir),$(call name_of,$(dir)))))

NAMES := $(foreach dir,$(DESIGNS),$(call name_of,$(dir)))
RTL_NAMES := $(foreach dir,$(RTL_DESIGNS),$(call name_of,$(dir)))

mlir: $(patsubst %,build/%/SimRtl.mlir,$(NAMES)) $(patsubst %,build/%/Rtl.mlir,$(RTL_NAMES))
sim: $(patsubst %,build/%/sim_obj_dir/V$(TB_TOP),$(NAMES))
rtl: $(patsubst %,build/%/obj_dir/V$(TB_TOP),$(RTL_NAMES))
all: sim rtl
check: $(patsubst %,check-sim-%,$(NAMES)) $(patsubst %,check-rtl-%,$(RTL_NAMES))

clean:
	rm -rf build
