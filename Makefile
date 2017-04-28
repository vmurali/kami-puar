PUARS:=$(wildcard puar/*.v)
PROCVS:=$(wildcard processors/*.v)
REFVS:=$(wildcard refinements/*.v)

.PHONY: all clean

all: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(PUARS) $(PROCVS) $(REFVS)
	coq_makefile -f _CoqProject $(PUARS) $(PROCVS) $(REFVS) -o Makefile.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f */*.v.d */*.glob */*.vo */*~ *~
	rm -f Makefile.coq
