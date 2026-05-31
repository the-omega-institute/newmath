.PHONY: all clean precheck check warn core derived
all: main.pdf
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
# so parallel paper jobs don't dogpile the CPU and start timing out.
main.pdf: precheck main.tex preamble.tex $(wildcard frontmatter/*.tex parts/**/*.tex appendices/*.tex)
	python3 scripts/with_pdf_slot.py -- bash -c 'export pool_size=300000000 max_strings=12000000 hash_extra=4000000 string_vacancies=200000 pool_free=200000; pdflatex -draftmode -interaction=batchmode main.tex; pdflatex -interaction=batchmode main.tex'
main_core.tex derived/concrete_instances.tex derived/concrete_instances_inputs_01.tex derived/concrete_instances_inputs_02.tex: scripts/gen_core_root.py main.tex
	python3 scripts/gen_core_root.py
core: main_core.pdf
main_core.pdf: precheck main_core.tex preamble.tex $(wildcard frontmatter/*.tex parts/**/*.tex appendices/*.tex)
	python3 scripts/with_pdf_slot.py -- bash -c 'export pool_size=300000000 max_strings=12000000 hash_extra=4000000 string_vacancies=200000 pool_free=200000 buf_size=1000000; pdflatex -draftmode -interaction=batchmode main_core.tex; pdflatex -interaction=batchmode main_core.tex'
derived: derived/concrete_instances.pdf
derived/concrete_instances.pdf: precheck derived/concrete_instances.tex derived/concrete_instances_inputs_01.tex derived/concrete_instances_inputs_02.tex main_core.pdf preamble.tex $(wildcard parts/concrete_instances/**/*.tex parts/concrete_instances/*.tex)
	python3 scripts/with_pdf_slot.py -- bash -c 'export TEXINPUTS=.:..: pool_size=300000000 max_strings=12000000 hash_extra=4000000 string_vacancies=200000 pool_free=200000 buf_size=1000000; pdflatex -draftmode -interaction=batchmode -output-directory=derived derived/concrete_instances.tex; pdflatex -interaction=batchmode -output-directory=derived derived/concrete_instances.tex'
# Compatibility alias: `check` is `precheck`. Worker-premerge uses the
# static gate and records full PDF verification as a deferred envelope;
# `make` / main.pdf remains the full PDF build.
check: precheck
clean:
	rm -f main.pdf main.log main.aux main.toc main.out main_core.pdf main_core.log main_core.aux main_core.toc main_core.out derived/concrete_instances.pdf derived/concrete_instances.log derived/concrete_instances.aux derived/concrete_instances.toc derived/concrete_instances.out *.bbl *.blg
