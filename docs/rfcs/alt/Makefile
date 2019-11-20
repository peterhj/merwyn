LATEXMK := latexmk -xelatex -pdf

.PHONY: all clean cleantmp

all: alt.pdf

clean:
	rm -f alt.{aux,bbl,log,pdf}

cleantmp:
	rm -f alt.{aux,log}

alt.pdf: alt.tex alt.bib
	$(LATEXMK) $<
