PROCVS:=$(wildcard processors/*.v)
PROOFVS:=$(wildcard proofs/*.v)

.PHONY: all clean

all: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(PROCVS) $(PROOFVS)
	coq_makefile -f _CoqProject $(PROCVS) $(PROOFVS) -o Makefile.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f */*.v.d */*.glob */*.vo */*~ *~
	rm -f Makefile.coq
