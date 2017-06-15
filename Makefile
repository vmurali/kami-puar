PUARS:=$(wildcard Puar/*.v)

.PHONY: all clean

all: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(PUARS)
	coq_makefile -f _CoqProject $(PUARS) -o Makefile.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f */*.v.d */*.glob */*.vo */*~ *~
	rm -f Makefile.coq
