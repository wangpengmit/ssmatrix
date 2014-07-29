MODULES := \
	mxutil \
	bimodule \
	derivation \
	mxmodule \
	mxdiff \
	nfun \
	eccv_paper_appendix \
	eccv_paper \
	prelude \

VS      := $(MODULES:%=%.v)

.PHONY: coq clean

coq: Makefile.coq
	COQC='coqc' $(MAKE) -f Makefile.coq

COQARGS := 
COQC    := coqc $(COQARGS)

Makefile.coq: Makefile $(VS)
	coq_makefile $(COQARGS) $(VS) -o Makefile.coq

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq .depend




# Example eccv_paper.pdf paper generating

.PHONY: paper clean_paper

paper: eccv_paper.pdf

eccv_paper.pdf: eccv_paper.v.tex
	pdflatex -job-name=eccv_paper eccv_paper.v.tex

eccv_paper.v.tex: eccv_paper.tex eccv_paper.coq.txt eccv_paper.style.coq.txt
	./PostCoq eccv_paper.tex eccv_paper.v.tex

eccv_paper.coq.txt: eccv_paper_tex.v
	./RunCoq eccv_paper_tex.v eccv_paper.coq.txt

eccv_paper.style.coq.txt: eccv_paper_style.v
	./RunCoq eccv_paper_style.v eccv_paper.style.coq.txt

clean_paper:
	rm -f *.coq.txt 
	rm -f eccv_paper.v.tex
	rm -f eccv_paper.aux
	rm -f eccv_paper.log
	rm -f eccv_paper.pdf
