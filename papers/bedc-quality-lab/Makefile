.PHONY: check test canonical-reports run-example clean-reports

check: test canonical-reports

test:
	python3 -m pytest -q

canonical-reports:
	python3 scripts/run_canonical_reports.py

run-example:
	python3 scripts/run_gaussian_ou_lejepa.py

clean-reports:
	rm -f reports/example_envelope.json reports/quality_report.md
	rm -rf reports/canonical
