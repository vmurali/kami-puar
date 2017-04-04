PROCVS:=$(wildcard processors/*.v)
REFVS:=$(wildcard refinements/*.v)

.PHONY: all clean

all: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(PROCVS) $(REFVS)
	coq_makefile -f _CoqProject $(PROCVS) $(REFVS) -o Makefile.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f */*.v.d */*.glob */*.vo */*~ *~
	rm -f Makefile.coq
