.PHONY: test run-example run-bedc-jepa run-bedc-jepa-experiment run-torch-bedc-jepa run-torch-retraining-loss-ablation run-lccp run-vjepa2-lccp run-vjepa2-latent-prediction build-public-jepa-registry build-bedc-jepa-manifest build-bedc-jepa-run-kit build-bedc-jepa-readiness build-bedc-jepa-review-bundle build-bedc-jepa-quality-backend build-bedc-jepa-rollup probe-public-minigrid clean-reports

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

run-torch-retraining-loss-ablation:
	python3 scripts/run_torch_retraining_loss_ablation.py

run-lccp:
	python3 scripts/run_bedc_latent_claim_certificate.py

run-vjepa2-lccp:
	python3 scripts/run_vjepa2_ac_minigrid_claim_certificate.py

run-vjepa2-latent-prediction:
	python3 scripts/run_vjepa2_ac_minigrid_latent_prediction.py

build-public-jepa-registry:
	python3 scripts/build_public_jepa_baseline_registry.py

build-bedc-jepa-manifest:
	python3 scripts/build_bedc_jepa_artifact_manifest.py

build-bedc-jepa-run-kit:
	python3 scripts/build_bedc_jepa_external_run_kit.py

build-bedc-jepa-readiness:
	python3 scripts/build_bedc_jepa_readiness.py

build-bedc-jepa-review-bundle:
	python3 scripts/build_bedc_jepa_review_bundle.py

build-bedc-jepa-quality-backend:
	python3 scripts/build_bedc_jepa_quality_backend_candidate.py

build-bedc-jepa-rollup: build-public-jepa-registry build-bedc-jepa-run-kit build-bedc-jepa-manifest build-bedc-jepa-readiness build-bedc-jepa-review-bundle build-bedc-jepa-quality-backend

probe-public-minigrid:
	python3 scripts/probe_public_minigrid.py

clean-reports:
	rm -f reports/example_envelope.json reports/quality_report.md reports/bedc_jepa_boundary_envelope.json reports/bedc_jepa_boundary_report.md reports/bedc_jepa_four_system_experiment.json reports/bedc_jepa_artifact_manifest.json reports/bedc_jepa_quality_backend_candidate.json reports/bedc_jepa_public_minigrid_probe.json reports/bedc_jepa_torch_objective.json
