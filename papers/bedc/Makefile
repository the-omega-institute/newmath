.PHONY: all clean precheck check
all: main.pdf
precheck:
	@bash scripts/check_tex_size.sh
	@bash scripts/check_math_env.sh
	@python3 scripts/check_marker_uniqueness.py
	@python3 scripts/check_naming.py
# The pdflatex calls go through scripts/with_pdf_slot.py, a flock-protected
# semaphore over .git/.pdf-build-gate/slotN.lock files. Permit count is read
# from .pipeline_parallel.json key "pdf_build" (default 2). This caps
# concurrent pdflatex invocations across every worktree and the main checkout
# so parallel paper rounds don't dogpile the CPU and start timing out.
main.pdf: precheck main.tex preamble.tex $(wildcard frontmatter/*.tex parts/**/*.tex appendices/*.tex)
	python3 scripts/with_pdf_slot.py -- bash -c 'pdflatex -interaction=nonstopmode main.tex && pdflatex -interaction=nonstopmode main.tex'
# Fast syntax / compile sanity check: single pdflatex pass in draftmode.
# Catches every real error (Undefined control sequence, Missing $, Extra },
# unresolved \input{...}, package errors). Skips the second pass and PDF
# output, so \autoref / TOC page numbers print as "?? on page ??" — fine
# for development sanity. Roughly half the wall time of `make`.
check: precheck
	python3 scripts/with_pdf_slot.py -- pdflatex -draftmode -interaction=nonstopmode main.tex
clean:
	rm -f main.pdf main.log main.aux main.toc main.out *.bbl *.blg
