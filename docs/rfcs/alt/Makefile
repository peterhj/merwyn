LATEX := xelatex
BIBTEX := bibtex

.PHONY: all clean cleantmp

all: alt.pdf

clean:
	rm -f alt.{aux,log,pdf}

cleantmp:
	rm -f alt.{aux,log}

alt.pdf: alt.tex alt.bib
	$(LATEX) $<
	$(BIBTEX) $(basename $<)
	$(LATEX) $<
	$(LATEX) $<
