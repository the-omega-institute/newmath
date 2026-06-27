PDF=main.pdf

.PHONY: all check clean sanitize

all: $(PDF)

# Repair invalid LaTeX that the codex-driven namecert writer occasionally emits
# for plain-text tokens like "B*_Q6": the bare "^\*" (superscript of the
# discretionary-times macro) makes pdflatex fail with "Missing { inserted".
# Rewrite it to a well-formed "^{*}". Idempotent; runs before every build so it
# survives the per-cycle regeneration of the namecert .tex files.
sanitize:
	@find parts -name '*.tex' -print0 2>/dev/null | xargs -0 perl -i -pe 's/\^\\\*/^{*}/g' 2>/dev/null || true

$(PDF): sanitize main.tex parts/codon_window_reality_boundary.tex
	pdflatex -interaction=nonstopmode -halt-on-error main.tex
	pdflatex -interaction=nonstopmode -halt-on-error main.tex

check: sanitize main.tex parts/codon_window_reality_boundary.tex
	pdflatex -draftmode -interaction=nonstopmode -halt-on-error main.tex

clean:
	rm -f main.aux main.log main.out main.pdf main.toc
