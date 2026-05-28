.PHONY: all clean precheck check warn
CONCRETE_PDFS := concrete_instances_opening.pdf concrete_instances_middle.pdf concrete_instances_analysis.pdf concrete_instances_completion.pdf
all: main.pdf $(CONCRETE_PDFS)
precheck: warn
	@bash scripts/check_tex_size.sh
	@bash scripts/check_math_env.sh
	@python3 scripts/check_marker_uniqueness.py
	@python3 scripts/check_naming.py
	@python3 scripts/check_up_macros.py
	@python3 scripts/check_text_macro_underscores.py
	@python3 scripts/check_external_provenance.py
	@python3 ../../lean4/scripts/bedc_ci.py audit
# Hard gate (was warn-only): convention checks for parts/concrete_instances/.
# Promoted from advisory to blocking once the dashboard cleared to 0
# violations across all 13 checks (A/C/D/E/F/G/H/I/J/K/L/M/N). Any new
# violation now fails precheck. Loop callers that want machine-readable
# output: `python3 scripts/warn_concrete_instances.py --json`. The check
# IDs and semantics live in the script's module docstring.
warn:
	@python3 scripts/warn_concrete_instances.py --strict
# The pdflatex calls go through scripts/with_pdf_slot.py, a flock-protected
# semaphore over .git/.pdf-build-gate/slotN.lock files. Permit count is read
# from .pipeline_parallel.json key "pdf_build" (default 2). This caps
# concurrent pdflatex invocations across every worktree and the main checkout
# so parallel paper rounds don't dogpile the CPU and start timing out.
main.pdf: precheck main.tex preamble.tex $(wildcard frontmatter/*.tex parts/**/*.tex appendices/*.tex)
	python3 scripts/with_pdf_slot.py -- bash -c 'pdflatex -draftmode -interaction=batchmode main.tex; pdflatex -interaction=batchmode main.tex'
concrete_instances_opening.pdf: precheck concrete_instances_opening.tex preamble.tex parts/concrete_instances/00001_concrete_instance_catalog_opening.tex $(wildcard parts/concrete_instances/**/*.tex parts/concrete_instances/*.tex)
	python3 scripts/with_pdf_slot.py -- bash -c 'pdflatex -draftmode -interaction=batchmode concrete_instances_opening.tex; pdflatex -interaction=batchmode concrete_instances_opening.tex'
concrete_instances_middle.pdf: precheck concrete_instances_middle.tex preamble.tex parts/concrete_instances/00002_concrete_instance_catalog_middle.tex $(wildcard parts/concrete_instances/**/*.tex parts/concrete_instances/*.tex)
	python3 scripts/with_pdf_slot.py -- bash -c 'pdflatex -draftmode -interaction=batchmode concrete_instances_middle.tex; pdflatex -interaction=batchmode concrete_instances_middle.tex'
concrete_instances_analysis.pdf: precheck concrete_instances_analysis.tex preamble.tex parts/concrete_instances/00003_concrete_instance_catalog_analysis.tex $(wildcard parts/concrete_instances/**/*.tex parts/concrete_instances/*.tex)
	python3 scripts/with_pdf_slot.py -- bash -c 'pdflatex -draftmode -interaction=batchmode concrete_instances_analysis.tex; pdflatex -interaction=batchmode concrete_instances_analysis.tex'
concrete_instances_completion.pdf: precheck concrete_instances_completion.tex preamble.tex parts/concrete_instances/00004_concrete_instance_catalog_completion.tex $(wildcard parts/concrete_instances/**/*.tex parts/concrete_instances/*.tex)
	python3 scripts/with_pdf_slot.py -- bash -c 'pdflatex -draftmode -interaction=batchmode concrete_instances_completion.tex; pdflatex -interaction=batchmode concrete_instances_completion.tex'
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
	rm -f main.pdf main.log main.aux main.toc main.out $(CONCRETE_PDFS) concrete_instances_opening.log concrete_instances_opening.aux concrete_instances_opening.toc concrete_instances_opening.out concrete_instances_middle.log concrete_instances_middle.aux concrete_instances_middle.toc concrete_instances_middle.out concrete_instances_analysis.log concrete_instances_analysis.aux concrete_instances_analysis.toc concrete_instances_analysis.out concrete_instances_completion.log concrete_instances_completion.aux concrete_instances_completion.toc concrete_instances_completion.out *.bbl *.blg
