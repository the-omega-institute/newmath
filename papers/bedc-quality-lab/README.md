# BEDC Model Quality Lab

This directory contains the BEDC-JEPA quality-lab environment.  It generates
reproducible lab-local evidence records for the BEDC-JEPA paper; it does not
define BEDC semantics, replace the paper, or replace Lean-side verification.

Python-side records are evidence envelopes, metric packets, certificate
records, and review artifacts.  References to BEDC names, paper sections,
labels, and Lean targets are opaque pointers.  NameCert, closure status,
origin, and ledger semantics remain owned by the BEDC paper and formal layers.

## Evidence Scope

The BEDC-JEPA evidence packet contains:

- boundary-gated OU-world S0/S1/S2/S3 comparisons;
- fixed-latent torch objective seed sweeps;
- grid-pixel learned-transition and MiniGrid-style visual-planning records;
- two-object, four-slot, and six-slot object-counterfactual and distractor
  records;
- public MiniGrid-DoorKey native S0/S1/S2/S3 readback and seed-sweep records;
- public MiniGrid debt decomposition, conformal coverage, risk-success Pareto,
  and calibration-extension records;
- public V-JEPA2-AC Giant CUDA checkpoint-scope adapter evaluation;
- fixed-checkpoint V-JEPA2-AC MiniGrid latent-prediction evaluation;
- fixed-carrier V-JEPA2-AC latent-claim certificate record;
- local multi-step latent-prediction smoke record with one rollout schema,
  predictor spec, gate spec, and cannot-claim boundary;
- true torch retraining loss-term ablation for `full_s3`,
  `minus_l_unlogged`, `minus_l_gap`, `minus_l_stab`, and
  `minus_l_intervention`;
- CUDA-gated K-step action-conditioned latent-prediction record on the shared
  torch BEDC-JEPA train/eval surface;
- public baseline native-metric contract for importing an official or external
  V-JEPA2-AC / JEPA-family baseline result;
- fillable public baseline native-metric template for the same import
  contract;
- quality-lab export registry for rollup-style downstream consumption;
- paper writeback packet for admitted manuscript-facing claims.

These records do not claim public benchmark superiority, official V-JEPA2-AC
benchmark reproduction, robotics-scale control, natural-language grounding, or
full pixel-control world modeling.

## Common Commands

Use the project CUDA environment when available:

```powershell
.\.venv-cuda\Scripts\python.exe -m pytest -q
```

Main record-building commands:

```powershell
.\.venv-cuda\Scripts\python.exe scripts\run_bedc_jepa_experiment.py
.\.venv-cuda\Scripts\python.exe scripts\run_torch_bedc_jepa.py
.\.venv-cuda\Scripts\python.exe scripts\run_torch_retraining_loss_ablation.py
.\.venv-cuda\Scripts\python.exe scripts\run_bedc_multistep_latent_prediction.py
.\.venv-cuda\Scripts\python.exe scripts\run_bedc_latent_claim_certificate.py
.\.venv-cuda\Scripts\python.exe scripts\run_vjepa2_ac_minigrid_claim_certificate.py
.\.venv-cuda\Scripts\python.exe scripts\run_vjepa2_ac_minigrid_latent_prediction.py
.\.venv-cuda\Scripts\python.exe scripts\build_vjepa2_ac_native_boundary.py
.\.venv-cuda\Scripts\python.exe scripts\build_vjepa2_ac_near_native_reproduction.py
.\.venv-cuda\Scripts\python.exe scripts\run_public_minigrid_native_benchmark.py
.\.venv-cuda\Scripts\python.exe scripts\run_public_minigrid_native_seed_sweep.py
.\.venv-cuda\Scripts\python.exe scripts\build_public_minigrid_debt_closure.py
.\.venv-cuda\Scripts\python.exe scripts\build_public_minigrid_calibration_extension.py
.\.venv-cuda\Scripts\python.exe scripts\export_public_minigrid_benchmark_result.py
.\.venv-cuda\Scripts\python.exe scripts\import_public_minigrid_benchmark_metrics.py <minigrid-result.json>
.\.venv-cuda\Scripts\python.exe scripts\probe_public_jepa_baseline.py
.\.venv-cuda\Scripts\python.exe scripts\run_public_jepa_structure_adapter.py
.\.venv-cuda\Scripts\python.exe scripts\run_public_jepa_ac_giant_adapter.py
.\.venv-cuda\Scripts\python.exe scripts\build_public_jepa_adapter_comparison.py
.\.venv-cuda\Scripts\python.exe scripts\build_public_jepa_cuda_comparison.py
.\.venv-cuda\Scripts\python.exe scripts\export_public_jepa_baseline_result.py
.\.venv-cuda\Scripts\python.exe scripts\import_public_jepa_baseline_metrics.py <baseline-result.json>
.\.venv-cuda\Scripts\python.exe scripts\build_public_jepa_baseline_registry.py
.\.venv-cuda\Scripts\python.exe scripts\build_public_baseline_native_metric_contract.py
.\.venv-cuda\Scripts\python.exe scripts\build_public_baseline_native_metric_template.py
.\.venv-cuda\Scripts\python.exe scripts\build_bedc_jepa_external_run_kit.py
.\.venv-cuda\Scripts\python.exe scripts\build_bedc_jepa_artifact_manifest.py
.\.venv-cuda\Scripts\python.exe scripts\build_bedc_jepa_readiness.py
.\.venv-cuda\Scripts\python.exe scripts\build_bedc_jepa_review_bundle.py
.\.venv-cuda\Scripts\python.exe scripts\build_bedc_jepa_quality_backend_candidate.py
.\.venv-cuda\Scripts\python.exe scripts\build_bedc_jepa_quality_lab_export.py
.\.venv-cuda\Scripts\python.exe scripts\build_bedc_jepa_paper_writeback_packet.py
```

Script entrypoints are discovered directly from the local source tree:

```powershell
Get-ChildItem .\scripts\*.py | Sort-Object Name | Select-Object -ExpandProperty Name
```

On systems with `make`, the rollup target runs the record-level build chain:

```powershell
make build-bedc-jepa-rollup
```

External result import targets take explicit source paths:

```powershell
make import-public-minigrid-result MINIGRID_RESULT=<minigrid-result.json>
make import-public-jepa-baseline-result BASELINE_RESULT=<baseline-result.json>
```

The current Windows shell used for this workspace may not provide `make`; in
that case, run the Python commands directly.

## Primary Records

Important generated records live under `reports/`:

- `bedc_jepa_four_system_experiment.json`
- `bedc_jepa_torch_objective.json`
- `bedc_multistep_latent_prediction.json`
- `bedc_jepa_retraining_loss_ablation.json`
- `bedc_latent_claim_certificates.json`
- `bedc_conformal_gap_sweep.json`
- `bedc_claim_boundary_audit.json`
- `bedc_jepa_public_native_minigrid_benchmark.json`
- `bedc_jepa_public_native_minigrid_seed_sweep.json`
- `bedc_jepa_public_debt_decomposition.json`
- `bedc_jepa_risk_success_pareto.json`
- `bedc_jepa_public_ac_giant_adapter.json`
- `bedc_jepa_public_cuda_adapter_comparison.json`
- `bedc_vjepa2_ac_minigrid_claim_certificate.json`
- `bedc_vjepa2_ac_minigrid_latent_prediction.json`
- `bedc_jepa_vjepa2_ac_native_boundary.json`
- `bedc_jepa_public_baseline_native_metric_contract.json`
- `bedc_jepa_public_baseline_native_metric_template.json`
- `bedc_jepa_external_run_kit.json`
- `bedc_jepa_artifact_manifest.json`
- `bedc_jepa_readiness.json`
- `bedc_jepa_review_bundle.json`
- `bedc_jepa_quality_backend_candidate.json`
- `bedc_jepa_quality_lab_exports.json`
- `bedc_jepa_paper_writeback_packet.json`

## Evidence Boundary

The lab is fail-closed.  If a carrier, predicate, or benchmark setting does
not support a certified claim, the corresponding record must return coverage
debt, source debt, or a cannot-claim row rather than silently upgrading the
claim.

The remaining manuscript-bearing evidence boundary is an official V-JEPA2-AC
benchmark reproduction or external baseline run under the recorded
native-metric contract and template, public MiniGrid calibration beyond the
current DoorKey-family readback scope, a public pixel-world benchmark
comparison, and a public object-interaction benchmark with natural clutter or
control.
