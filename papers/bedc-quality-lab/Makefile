.PHONY: test run-example run-bedc-jepa run-bedc-jepa-experiment run-torch-bedc-jepa build-bedc-jepa-manifest probe-public-minigrid clean-reports

test:
	python3 -m pytest -q

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

probe-public-minigrid:
	python3 scripts/probe_public_minigrid.py

clean-reports:
	rm -f reports/example_envelope.json reports/quality_report.md reports/bedc_jepa_boundary_envelope.json reports/bedc_jepa_boundary_report.md reports/bedc_jepa_four_system_experiment.json reports/bedc_jepa_artifact_manifest.json reports/bedc_jepa_public_minigrid_probe.json reports/bedc_jepa_torch_objective.json
