# Example example.pdf paper generating

.PHONY: paper clean_paper

TOOLS := ..
THEORIES := ../../theories
THEORY := $(THEORIES)/example.vo
RUNCOQ := $(TOOLS)/RunCoq -f "-I $(THEORIES)"
POSTCOQ := $(TOOLS)/PostCoq

paper: example.pdf

example.pdf: example.v.tex
	pdflatex -jobname=example example.v.tex
	bibtex example
	pdflatex -jobname=example example.v.tex
	pdflatex -jobname=example example.v.tex

example.v.tex: example.tex example.coq.txt example_appendix.coq.txt
	$(RUNCOQ) example.tex | $(POSTCOQ) > example.v.tex

example.coq.txt: example_tex.v $(THEORY)
	$(RUNCOQ) -v example_tex.v example.coq.txt

example_appendix.coq.txt: example_appendix_tex.v $(THEORY)
	$(RUNCOQ) -v example_appendix_tex.v example_appendix.coq.txt

clean:
	rm -f *.coq.txt 
	rm -f example.v.tex
	rm -f example.aux
	rm -f example.log
	rm -f example.pdf
