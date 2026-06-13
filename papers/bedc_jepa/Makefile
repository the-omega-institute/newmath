PDF=main.pdf
PARTS=parts/reality_boundary.tex \
	parts/relation_to_jepa.tex \
	parts/model_principle.tex \
	parts/latent_claim_certificate.tex \
	parts/boundary_gated_world.tex \
	parts/evaluation_contract.tex \
	parts/gap_aware_planning.tex \
	parts/evidence_packet.tex \
	parts/lewm_instantiation.tex \
	parts/cannot_claim_boundary.tex

.PHONY: all precheck check clean

all: $(PDF)

precheck: main.tex $(PARTS) scripts/precheck_bedc_jepa.py
	python3 scripts/precheck_bedc_jepa.py

$(PDF): precheck main.tex $(PARTS)
	pdflatex -interaction=nonstopmode -halt-on-error -file-line-error main.tex
	pdflatex -interaction=nonstopmode -halt-on-error -file-line-error main.tex

check: precheck
	pdflatex -draftmode -interaction=nonstopmode -halt-on-error -file-line-error main.tex

clean:
	rm -f main.aux main.log main.out main.pdf main.toc
