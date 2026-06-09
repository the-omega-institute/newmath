# BEDC Model Quality Lab

本目录是 BEDC-JEPA 质量实验与证据记录环境。它不定义 BEDC
正文语义，也不替代论文或 Lean 侧验证；它只生成可复现的
lab-local evidence records，用来支撑论文中的 bounded claims。

Python 侧只拥有 `QualityEvidenceEnvelope` 和一组 JSON/Markdown 记录。
`bedc_refs` 只保存不透明指针，例如章节路径、label 或 Lean 目标名。
这里不重新定义 NameCert、closurestatus、origin、ledger 等 BEDC
语义。

## 当前证据范围

当前 BEDC-JEPA 证据包包含：

- boundary-gated OU world 的四系统 S0/S1/S2/S3 对照；
- fixed-latent torch objective seed sweep；
- grid-pixel learned-transition 与 MiniGrid-style visual-planning 研究；
- two-object、four-slot、six-slot object-counterfactual / distractor 研究；
- public MiniGrid-DoorKey S0/S1/S2/S3 native readback packet 与 seed sweep；
- public MiniGrid debt decomposition、conformal coverage sweep、risk-success Pareto；
- public V-JEPA2-AC Giant CUDA checkpoint-scope adapter evaluation；
- fixed-checkpoint V-JEPA2-AC MiniGrid latent-prediction evaluation；
- V-JEPA2-AC fixed-carrier LCCP certificate record；
- true torch retraining loss-term ablation for `full_s3`,
  `minus_l_unlogged`, and `minus_l_gap`, with `minus_l_stab` and
  `minus_l_intervention` recorded as source debt in the current boundary-world
  supervision surface.

These records do not claim public benchmark superiority, official/native
V-JEPA2-AC benchmark reproduction, robotics-scale control, natural-language
grounding, or full pixel-control world modeling.

## Common Commands

Use the project CUDA environment when available:

```powershell
.\.venv-cuda\Scripts\python.exe -m pytest -q
```

The main record-building commands are:

```powershell
.\.venv-cuda\Scripts\python.exe scripts\run_bedc_jepa_experiment.py
.\.venv-cuda\Scripts\python.exe scripts\run_torch_bedc_jepa.py
.\.venv-cuda\Scripts\python.exe scripts\run_torch_retraining_loss_ablation.py
.\.venv-cuda\Scripts\python.exe scripts\run_bedc_latent_claim_certificate.py
.\.venv-cuda\Scripts\python.exe scripts\run_vjepa2_ac_minigrid_claim_certificate.py
.\.venv-cuda\Scripts\python.exe scripts\run_vjepa2_ac_minigrid_latent_prediction.py
.\.venv-cuda\Scripts\python.exe scripts\build_public_jepa_baseline_registry.py
.\.venv-cuda\Scripts\python.exe scripts\build_bedc_jepa_external_run_kit.py
.\.venv-cuda\Scripts\python.exe scripts\build_bedc_jepa_artifact_manifest.py
.\.venv-cuda\Scripts\python.exe scripts\build_bedc_jepa_readiness.py
.\.venv-cuda\Scripts\python.exe scripts\build_bedc_jepa_review_bundle.py
.\.venv-cuda\Scripts\python.exe scripts\build_bedc_jepa_quality_backend_candidate.py
```

## Primary Records

Important generated records live under `reports/`:

- `bedc_jepa_four_system_experiment.json`
- `bedc_jepa_torch_objective.json`
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
- `bedc_jepa_external_run_kit.json`
- `bedc_jepa_artifact_manifest.json`
- `bedc_jepa_readiness.json`
- `bedc_jepa_review_bundle.json`
- `bedc_jepa_quality_backend_candidate.json`

## Evidence Boundary

The lab is fail-closed. If a carrier, predicate, or benchmark setting does not
support a certified claim, the corresponding record must return coverage debt,
source debt, or a cannot-claim row rather than silently upgrading the claim.

The remaining manuscript-bearing evidence boundary is not another local toy
world. It is an official/native V-JEPA2-AC benchmark reproduction or a
rollout-benchmark parity protocol, plus stronger public MiniGrid calibration
and risk-success summaries.
