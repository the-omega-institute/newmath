.PHONY: all clean precheck check
all: main.pdf
precheck:
	@bash scripts/check_tex_size.sh
	@bash scripts/check_math_env.sh
	@python3 scripts/check_marker_uniqueness.py
	@python3 scripts/check_naming.py
	@python3 scripts/check_external_provenance.py
# The pdflatex calls go through scripts/with_pdf_slot.py, a flock-protected
# semaphore over .git/.pdf-build-gate/slotN.lock files. Permit count is read
# from .pipeline_parallel.json key "pdf_build" (default 2). This caps
# concurrent pdflatex invocations across every worktree and the main checkout
# so parallel paper rounds don't dogpile the CPU and start timing out.
main.pdf: precheck main.tex preamble.tex $(wildcard frontmatter/*.tex parts/**/*.tex appendices/*.tex)
	python3 scripts/with_pdf_slot.py -- bash -c 'pdflatex -draftmode -interaction=batchmode main.tex; pdflatex -interaction=batchmode main.tex'
# Round-local sanity: pure-text static checks only, no pdflatex invocation.
# The precheck dependency runs four python/bash gates: file size,
# forbidden math env, marker uniqueness, NAMING.md compliance. The
# canonical PDF build (`make` / main.pdf) is the daemon's job —
# paper_builder_daemon.py polls the merged codex-auto-dev tip and runs
# the full double-pass in `_paper_builder`. Removing pdflatex from
# `make check` keeps round wall time low (~1s precheck vs ~127s
# pdflatex draftmode) and frees the pdf-build slot gate for the daemon.
check: precheck
clean:
	rm -f main.pdf main.log main.aux main.toc main.out *.bbl *.blg
