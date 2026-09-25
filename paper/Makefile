# Build the paper: make (requires a TeX distribution with latexmk or pdflatex + bibtex)
MAIN = main
OUT  = kronecker-fri.pdf

all: $(OUT)

$(OUT): $(MAIN).tex refs.bib sections/*.tex
	pdflatex -interaction=nonstopmode $(MAIN)
	bibtex $(MAIN)
	pdflatex -interaction=nonstopmode $(MAIN)
	pdflatex -interaction=nonstopmode $(MAIN)
	pdflatex -interaction=nonstopmode $(MAIN)
	cp $(MAIN).pdf $(OUT)

clean:
	rm -f *.aux *.bbl *.blg *.log *.out *.toc $(MAIN).pdf

.PHONY: all clean
