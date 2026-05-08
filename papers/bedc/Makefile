.PHONY: all clean precheck check
all: main.pdf
precheck:
	@bash scripts/check_tex_size.sh
	@bash scripts/check_math_env.sh
main.pdf: precheck main.tex preamble.tex $(wildcard frontmatter/*.tex parts/**/*.tex appendices/*.tex)
	pdflatex -interaction=nonstopmode main.tex
	pdflatex -interaction=nonstopmode main.tex
# Fast syntax / compile sanity check: single pdflatex pass in draftmode.
# Catches every real error (Undefined control sequence, Missing $, Extra },
# unresolved \input{...}, package errors). Skips the second pass and PDF
# output, so \autoref / TOC page numbers print as "?? on page ??" — fine
# for development sanity. Roughly half the wall time of `make`.
check: precheck
	pdflatex -draftmode -interaction=nonstopmode main.tex
clean:
	rm -f main.pdf main.log main.aux main.toc main.out *.bbl *.blg
