.PHONY: clean all

.DEFAULT_GOAL = all

PP = ../../PrettyPrinter

all: $(PP)/FixLits
	grep -q "import qualified Data" ./Compile.hs || $(PP)/FixLits ./Compile.hs
	grep -q "import qualified Data" ./Compile.hs || sed -i "/import qualified Prelude/aimport qualified Data.Bits\nimport qualified Data.Char" ./Compile.hs
	ghc --make -j -i$(PP) $(PP)/Main.hs -o Main
	./Main > simpleprocessor.sv

clean:
	rm -f *.hi *.o Main simpleprocessor.sv
