PDF=main.pdf

.PHONY: all check clean

all: $(PDF)

$(PDF): main.tex parts/reality_boundary.tex parts/relation_to_jepa.tex parts/model_principle.tex parts/boundary_gated_world.tex parts/evaluation_contract.tex parts/gap_aware_planning.tex parts/evidence_packet.tex parts/cannot_claim_boundary.tex
	pdflatex -interaction=nonstopmode -halt-on-error main.tex
	pdflatex -interaction=nonstopmode -halt-on-error main.tex

check: main.tex parts/reality_boundary.tex parts/relation_to_jepa.tex parts/model_principle.tex parts/boundary_gated_world.tex parts/evaluation_contract.tex parts/gap_aware_planning.tex parts/evidence_packet.tex parts/cannot_claim_boundary.tex
	pdflatex -draftmode -interaction=nonstopmode -halt-on-error main.tex

clean:
	rm -f main.aux main.log main.out main.pdf main.toc
