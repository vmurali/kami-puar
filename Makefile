PROCVS:=$(wildcard processors/*.v)

.PHONY: coq src clean

LIBARGS := -R kami/lib Lib
ARGS := -R kami/src Kami
EXARGS := -R kami/examples Ex
EXTARGS := -R kami/extraction Ext
PROCARGS := -R processors Proc

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(PROCVS)
	coq_makefile $(LIBARGS) $(ARGS) $(EXARGS) $(EXTARGS) $(PROCARGS) $(PROCVS) -o Makefile.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f */*.v.d */*.glob */*.vo */*~ *~
	rm -f Makefile.coq
