.PHONY: clean all

.DEFAULT_GOAL = all

all: FixLits
	grep -q "import qualified Data" ./Compile.hs || ./FixLits ./Compile.hs
	grep -q "import qualified Data" ./Compile.hs || sed -i "/import qualified Prelude/aimport qualified Data.Bits\nimport qualified Data.Char" ./Compile.hs
	ghc --make -j Main.hs

FixLits: FixLits.hs
	ghc --make FixLits.hs

clean:
	rm *.hi
	rm *.o
