default: Makefile.coq
	make -f Makefile.coq

clean: Makefile.coq
	make -f Makefile.coq cleanall
	rm -f Makefile.coq

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

.PHONY: default clean
