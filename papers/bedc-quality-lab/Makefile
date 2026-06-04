.PHONY: check test canonical-consistency canonical-reports canonical-reports-cold cold-check run-example clean-reports

check: canonical-consistency test

test:
	python3 -m pytest -q

canonical-consistency:
	python3 scripts/run_canonical_reports.py --verify-fingerprints

canonical-reports:
	python3 scripts/run_canonical_reports.py

canonical-reports-cold:
	python3 scripts/run_canonical_reports.py --cold

cold-check: test canonical-reports-cold

run-example:
	python3 scripts/run_gaussian_ou_lejepa.py

clean-reports:
	rm -f reports/example_envelope.json reports/quality_report.md
	rm -rf reports/canonical
