-include Makefile.coq

V_FILES := $(wildcard *.v)

Makefile.coq:
	coq_makefile -f _CoqProject $(V_FILES) -o $@
