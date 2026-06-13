.PHONY: check test metric-purity canonical-consistency canonical-reports canonical-reports-cold claim-artifact-consistency cold-check run-example run-bedc-jepa run-bedc-jepa-experiment run-torch-bedc-jepa build-bedc-jepa-manifest build-bedc-jepa-quality-backend build-public-minigrid-debt-closure probe-public-minigrid clean-reports

check: metric-purity canonical-consistency test

test:
	python3 -m pytest -q

metric-purity:
	python3 scripts/check_metric_purity.py

canonical-consistency:
	python3 scripts/run_canonical_reports.py --verify-fingerprints

canonical-reports:
	python3 scripts/run_canonical_reports.py

canonical-reports-cold:
	python3 scripts/run_canonical_reports.py --cold

claim-artifact-consistency:
	python3 scripts/run_claim_artifact_consistency.py --check

cold-check: test canonical-reports-cold

run-example:
	python3 scripts/run_gaussian_ou_lejepa.py

run-bedc-jepa:
	python3 scripts/run_bedc_jepa_boundary_world.py

run-bedc-jepa-experiment:
	python3 scripts/run_bedc_jepa_experiment.py

run-torch-bedc-jepa:
	python3 scripts/run_torch_bedc_jepa.py

build-bedc-jepa-manifest:
	python3 scripts/build_bedc_jepa_artifact_manifest.py

build-bedc-jepa-quality-backend:
	python3 scripts/build_bedc_jepa_quality_backend_candidate.py

build-public-minigrid-debt-closure:
	python3 scripts/build_public_minigrid_debt_closure.py

probe-public-minigrid:
	python3 scripts/probe_public_minigrid.py

clean-reports:
	rm -f reports/example_envelope.json reports/quality_report.md
	rm -f reports/bedc_jepa_boundary_envelope.json reports/bedc_jepa_boundary_report.md
	rm -f reports/bedc_jepa_four_system_experiment.json reports/bedc_jepa_artifact_manifest.json
	rm -f reports/bedc_jepa_quality_backend_candidate.json reports/bedc_jepa_public_minigrid_probe.json
	rm -f reports/bedc_jepa_torch_objective.json
	rm -f reports/bedc_jepa_public_debt_decomposition.json reports/bedc_jepa_certified_coverage_curve.json
	rm -f reports/bedc_jepa_risk_constrained_planning.json reports/bedc_jepa_public_debt_closure_report.md
	rm -rf reports/canonical
