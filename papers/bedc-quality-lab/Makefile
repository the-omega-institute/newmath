.PHONY: test run-example run-bedc-jepa clean-reports

test:
	python3 -m pytest -q

run-example:
	python3 scripts/run_gaussian_ou_lejepa.py

run-bedc-jepa:
	python3 scripts/run_bedc_jepa_boundary_world.py

clean-reports:
	rm -f reports/example_envelope.json reports/quality_report.md reports/bedc_jepa_boundary_envelope.json reports/bedc_jepa_boundary_report.md
