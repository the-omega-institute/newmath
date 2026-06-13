PDF=main.pdf
PYTHON=python3
PARTS=parts/scope.tex parts/correspondences.tex parts/bio_inputs.tex parts/synthesis.tex

.PHONY: all check gate generate clean

all: generate $(PDF) gate

generate:
	$(PYTHON) ../../tools/window_codon_bridge/paper_gen.py

$(PDF): main.tex $(PARTS)
	pdflatex -interaction=nonstopmode -halt-on-error main.tex
	pdflatex -interaction=nonstopmode -halt-on-error main.tex

check: generate main.tex $(PARTS)
	pdflatex -draftmode -interaction=nonstopmode -halt-on-error main.tex

gate: generate
	$(PYTHON) ../../tools/window_codon_bridge/paper_gate.py

clean:
	rm -f main.aux main.log main.out main.pdf main.toc
