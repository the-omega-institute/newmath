.PHONY: all clean precheck check warn
all: main.pdf
precheck: warn
	@bash scripts/check_tex_size.sh
	@bash scripts/check_math_env.sh
	@bash scripts/check_codon_native_binary.sh
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
	python3 scripts/with_pdf_slot.py -- bash -c 'export pool_size=300000000 max_strings=12000000 hash_extra=4000000 string_vacancies=200000 pool_free=200000; pdflatex -draftmode -interaction=batchmode main.tex; pdflatex -interaction=batchmode main.tex'
# Compatibility alias: `check` is `precheck`. Worker-premerge uses the
# static gate and records full PDF verification as a deferred envelope;
# `make` / main.pdf remains the full PDF build.
check: precheck
clean:
	rm -f main.pdf main.log main.aux main.toc main.out *.bbl *.blg
