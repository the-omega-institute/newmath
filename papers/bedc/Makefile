.PHONY: all clean
all: main.pdf
main.pdf: main.tex preamble.tex $(wildcard frontmatter/*.tex parts/**/*.tex appendices/*.tex)
	pdflatex -interaction=nonstopmode main.tex
	pdflatex -interaction=nonstopmode main.tex
clean:
	rm -f main.pdf main.log main.aux main.toc main.out *.bbl *.blg
