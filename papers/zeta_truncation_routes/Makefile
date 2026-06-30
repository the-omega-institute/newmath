LATEX=pdflatex

.PHONY: all clean

all: main.pdf

main.pdf: main.tex
	$(LATEX) -interaction=nonstopmode -halt-on-error main.tex
	$(LATEX) -interaction=nonstopmode -halt-on-error main.tex

clean:
	rm -f main.aux main.log main.out main.pdf
