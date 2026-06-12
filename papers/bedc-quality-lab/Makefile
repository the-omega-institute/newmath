.PHONY: check test metric-purity canonical-consistency canonical-reports canonical-reports-cold claim-artifact-consistency cold-check run-example clean-reports

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

clean-reports:
	rm -f reports/example_envelope.json reports/quality_report.md
	rm -rf reports/canonical
