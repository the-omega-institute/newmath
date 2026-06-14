.PHONY: test run-example run-bedc-jepa run-bedc-jepa-experiment run-torch-bedc-jepa run-torch-retraining-loss-ablation run-lccp run-vjepa2-lccp run-vjepa2-latent-prediction build-vjepa2-native-boundary build-vjepa2-near-native-reproduction run-public-minigrid-native run-public-minigrid-native-seed-sweep build-public-minigrid-debt-closure build-public-minigrid-calibration-extension build-public-benchmark-scope-contracts export-public-minigrid-result import-public-minigrid-result probe-public-jepa-baseline run-public-jepa-structure-adapter run-public-jepa-ac-giant-adapter build-public-jepa-adapter-comparison build-public-jepa-cuda-comparison export-public-jepa-baseline-result import-public-jepa-baseline-result build-public-jepa-registry build-public-baseline-native-metric-contract build-public-baseline-native-metric-template build-bedc-jepa-manifest build-bedc-jepa-run-kit build-bedc-jepa-readiness build-bedc-jepa-review-bundle build-bedc-jepa-quality-backend build-bedc-jepa-quality-lab-export build-bedc-jepa-paper-writeback-packet build-bedc-jepa-rollup probe-public-minigrid clean-reports

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

build-vjepa2-native-boundary:
	python3 scripts/build_vjepa2_ac_native_boundary.py

build-vjepa2-near-native-reproduction:
	python3 scripts/build_vjepa2_ac_near_native_reproduction.py

run-public-minigrid-native:
	python3 scripts/run_public_minigrid_native_benchmark.py

run-public-minigrid-native-seed-sweep:
	python3 scripts/run_public_minigrid_native_seed_sweep.py

build-public-minigrid-debt-closure:
	python3 scripts/build_public_minigrid_debt_closure.py

build-public-minigrid-calibration-extension:
	python3 scripts/build_public_minigrid_calibration_extension.py

build-public-benchmark-scope-contracts:
	python3 scripts/build_public_benchmark_scope_contracts.py

export-public-minigrid-result:
	python3 scripts/export_public_minigrid_benchmark_result.py

import-public-minigrid-result:
	python3 scripts/import_public_minigrid_benchmark_metrics.py $(MINIGRID_RESULT)

probe-public-jepa-baseline:
	python3 scripts/probe_public_jepa_baseline.py

run-public-jepa-structure-adapter:
	python3 scripts/run_public_jepa_structure_adapter.py

run-public-jepa-ac-giant-adapter:
	python3 scripts/run_public_jepa_ac_giant_adapter.py

build-public-jepa-adapter-comparison:
	python3 scripts/build_public_jepa_adapter_comparison.py

build-public-jepa-cuda-comparison:
	python3 scripts/build_public_jepa_cuda_comparison.py

export-public-jepa-baseline-result:
	python3 scripts/export_public_jepa_baseline_result.py

import-public-jepa-baseline-result:
	python3 scripts/import_public_jepa_baseline_metrics.py $(BASELINE_RESULT)

build-public-jepa-registry:
	python3 scripts/build_public_jepa_baseline_registry.py

build-public-baseline-native-metric-contract:
	python3 scripts/build_public_baseline_native_metric_contract.py

build-public-baseline-native-metric-template:
	python3 scripts/build_public_baseline_native_metric_template.py

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

build-bedc-jepa-quality-lab-export:
	python3 scripts/build_bedc_jepa_quality_lab_export.py

build-bedc-jepa-paper-writeback-packet:
	python3 scripts/build_bedc_jepa_paper_writeback_packet.py

build-bedc-jepa-rollup: build-public-benchmark-scope-contracts export-public-jepa-baseline-result build-public-jepa-registry build-public-baseline-native-metric-contract build-public-baseline-native-metric-template build-vjepa2-native-boundary build-vjepa2-near-native-reproduction build-bedc-jepa-run-kit build-bedc-jepa-manifest build-bedc-jepa-readiness build-bedc-jepa-review-bundle build-bedc-jepa-quality-backend build-bedc-jepa-quality-lab-export build-bedc-jepa-paper-writeback-packet build-bedc-jepa-review-bundle build-bedc-jepa-manifest

probe-public-minigrid:
	python3 scripts/probe_public_minigrid.py

clean-reports:
	rm -f reports/*.json reports/*.md
