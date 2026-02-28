.PHONY: coq clean all force

.DEFAULT_GOAL = all

TARGETS := $(wildcard Example/*/)
MAINSVS := $(patsubst %/,%/Main.sv,$(TARGETS))

coq: Makefile.coq.all $(VS)
	$(MAKE) -f Makefile.coq.all

./PrettyPrinter/FixLits: ./PrettyPrinter/FixLits.hs
	ghc --make ./PrettyPrinter/FixLits.hs -o ./PrettyPrinter/FixLits

define Main_rule
$(1)Main: coq ./PrettyPrinter/FixLits ./PrettyPrinter/Main.hs $(1)Compile.hs
	grep -q "import qualified Data" $(1)Compile.hs || ./PrettyPrinter/FixLits $(1)Compile.hs
	grep -q "import qualified Data" $(1)Compile.hs || sed -i "/import qualified Prelude/aimport qualified Data.Bits\nimport qualified Data.Char" $(1)Compile.hs
	ghc --make -j -i./PrettyPrinter -i$(1) ./PrettyPrinter/Main.hs -o $(1)Main
endef

define Main_sv_rule
$(1)Main.sv: $(1)Main
	$(1)Main > $(1)Main.sv
endef

$(foreach dir,$(TARGETS),$(eval $(call Main_rule,$(dir))))
$(foreach dir,$(TARGETS),$(eval $(call Main_sv_rule,$(dir))))

all: $(MAINSVS)

force:

Makefile.coq.all: force
	$(COQBIN)rocq makefile -f _CoqProject -o Makefile.coq.all

clean:: Makefile.coq.all
	$(MAKE) -f Makefile.coq.all clean
	find . -type f -name '*.v.d' -exec rm {} \;
	find . -type f -name '*.glob' -exec rm {} \;
	find . -type f -name '*.vo' -exec rm {} \;
	find . -type f -name '*.vos' -exec rm {} \;
	find . -type f -name '*.vok' -exec rm {} \;
	find . -type f -name '*.~' -exec rm {} \;
	find . -type f -name '*.hi' -exec rm {} \;
	find . -type f -name '*.o' -exec rm {} \;
	find . -type f -name '*.aux' -exec rm {} \;
	find . -type f -name 'Compile.hs' -exec rm {} \;
	find . -type f -name 'Main' -exec rm {} \;
	find . -type f -name 'Main.sv' -exec rm {} \;
	rm -f PrettyPrinter/FixLits
	rm -f Makefile.coq.all Makefile.coq.all.conf .Makefile.coq.all.d
	rm -f .nia.cache .lia.cache

