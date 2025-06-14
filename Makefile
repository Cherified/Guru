.PHONY: coq clean force haskell

.DEFAULT_GOAL = coq #haskell

coq: Makefile.coq.all $(VS)
	$(MAKE) -f Makefile.coq.all

haskell: coq
	$(MAKE) -C ./PrettyPrinter

Makefile.coq.all: force
	$(COQBIN)rocq makefile -f _CoqProject -o Makefile.coq.all

force:

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
	rm -f Makefile.coq.all Makefile.coq.all.conf .Makefile.coq.all.d
	rm -f .nia.cache .lia.cache

