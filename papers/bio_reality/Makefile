PDF=main.pdf

.PHONY: all check clean

all: $(PDF)

$(PDF): main.tex parts/codon_window_reality_boundary.tex
	pdflatex -interaction=nonstopmode -halt-on-error main.tex
	pdflatex -interaction=nonstopmode -halt-on-error main.tex

check: main.tex parts/codon_window_reality_boundary.tex
	pdflatex -draftmode -interaction=nonstopmode -halt-on-error main.tex

clean:
	rm -f main.aux main.log main.out main.pdf main.toc
