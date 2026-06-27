PDF=main.pdf

.PHONY: all check clean sanitize

all: $(PDF)

# Repair invalid LaTeX that the codex-driven namecert writer occasionally emits
# (bare "^\*" -> "^{*}", and literal Unicode math/Greek like Δ, ρ, ², ≈, → that
# pdflatex rejects). See scripts/sanitize_tex.py. Idempotent; runs before every
# build so it survives the per-cycle regeneration of the namecert .tex files.
sanitize:
	@python3 scripts/sanitize_tex.py 2>/dev/null || true

$(PDF): sanitize main.tex parts/codon_window_reality_boundary.tex
	pdflatex -interaction=nonstopmode -halt-on-error main.tex
	pdflatex -interaction=nonstopmode -halt-on-error main.tex

check: sanitize main.tex parts/codon_window_reality_boundary.tex
	pdflatex -draftmode -interaction=nonstopmode -halt-on-error main.tex

clean:
	rm -f main.aux main.log main.out main.pdf main.toc
