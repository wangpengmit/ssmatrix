# Example eccv_paper.pdf paper generating

.PHONY: paper clean_paper

TOOLS := ../tools
THEORIES := ..
THEORY := $(THEORIES)/eccv_paper.vo
RUNCOQ := $(TOOLS)/RunCoq -f "-I $(THEORIES)"
POSTCOQ := $(TOOLS)/PostCoq

paper: eccv_paper.pdf

eccv_paper.pdf: eccv_paper.v.tex
	pdflatex -jobname=eccv_paper eccv_paper.v.tex
	bibtex eccv_paper
	pdflatex -jobname=eccv_paper eccv_paper.v.tex
	pdflatex -jobname=eccv_paper eccv_paper.v.tex

eccv_paper.v.tex: eccv_paper.tex eccv_paper.coq.txt eccv_paper_appendix.coq.txt
	$(RUNCOQ) eccv_paper.tex | $(POSTCOQ) > eccv_paper.v.tex

eccv_paper.coq.txt: eccv_paper_tex.v $(THEORY)
	$(RUNCOQ) -v eccv_paper_tex.v eccv_paper.coq.txt

eccv_paper_appendix.coq.txt: eccv_paper_appendix_tex.v $(THEORY)
	$(RUNCOQ) -v eccv_paper_appendix_tex.v eccv_paper_appendix.coq.txt

clean:
	rm -f *.coq.txt 
	rm -f eccv_paper.v.tex
	rm -f eccv_paper.aux
	rm -f eccv_paper.log
	rm -f eccv_paper.pdf
