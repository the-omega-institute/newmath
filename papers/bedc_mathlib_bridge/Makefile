SHELL := /bin/bash

.PHONY: check bedc-core

check:
	cd lean4 && lake build
	cd lean4 && lake build BedcMathlibBridge.Audit.ThinLayerGuard
	cd lean4 && lake build BedcMathlibBridge.CI.Audit
	cd lean4 && lake build BedcMathlibBridge.CI.ExportAudit
	cd lean4 && lake build BedcMathlibBridge.CI.MathlibCorrespondence
	cd lean4 && lake build BedcMathlibBridge.Audit.BoundaryFactAxiomGuard
	python3 scripts/check_bridge_axioms.py
	python3 scripts/check_gap_sync.py MISSING_IN_BEDC.md MATRIX.md
	python3 scripts/check_export_matrix.py MATRIX.md
	python3 scripts/check_mathlib_correspondence.py MATRIX.md
	python3 scripts/check_no_hollow.py MATRIX.md
	python3 scripts/check_value_anchor.py MATRIX.md  # shadow: reports Nat-shadow laundering (dead natToUnary/bwordLength anchor); exit 0 until existing rows are cleaned + the authoritative Lean-env gate (BridgeAudit.lean) lands, then promote with --gate
	python3 scripts/check_canonical_int_law.py
	python3 scripts/check_ring_bundle.py
	python3 scripts/check_statement_shape_dup.py
	python3 scripts/check_boundary_axioms.py MATRIX.md
	python3 scripts/check_no_back_edge.py
	bash scripts/run_negative_tests.sh

bedc-core:
	cd ../../lean4 && lake build
	python3 ../../tools/check-axioms.py
	python3 ../../lean4/scripts/bedc_ci.py axiom-purity
	python3 ../../lean4/scripts/triangle_coverage.py
	python3 ../../lean4/scripts/no_fake_rh_audit.py
