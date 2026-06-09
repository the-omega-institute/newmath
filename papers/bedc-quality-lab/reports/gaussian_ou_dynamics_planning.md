# Gaussian-OU Dynamics and Gap-Aware Planning

- Generated at: `2026-06-01T13:18:13.868636+00:00`
- Total records: `600`
- Seed count: `30`
- Arm count: `4`
- Lambda values: `0.0, 0.25, 0.5, 1.0, 2.0`
- Primary lambda: `1.0`
- Planner horizon: `3`

## Four-Arm Primary Metrics

| arm | records | unsafe-state rate | UnloggedErrorRate | collision rate | safe-planning success | planning regret | gap AUROC | gap ECE |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Vanilla JEPA | 30 | 0.376563 +/- 0.065184 (95% CI +/- 0.023326) | 0.000000 +/- 0.000000 (95% CI +/- 0.000000) | 0.385937 +/- 0.071914 (95% CI +/- 0.025734) | 0.521875 +/- 0.070906 (95% CI +/- 0.025373) | -0.466815 +/- 0.116303 (95% CI +/- 0.041618) | 0.500000 +/- 0.000000 (95% CI +/- 0.000000) | 0.478125 +/- 0.070906 (95% CI +/- 0.025373) |
| JEPA + post-hoc probe | 30 | 0.376563 +/- 0.065184 (95% CI +/- 0.023326) | 0.000000 +/- 0.000000 (95% CI +/- 0.000000) | 0.387500 +/- 0.073791 (95% CI +/- 0.026406) | 0.521875 +/- 0.070906 (95% CI +/- 0.025373) | -0.467844 +/- 0.116100 (95% CI +/- 0.041546) | 0.500000 +/- 0.000000 (95% CI +/- 0.000000) | 0.478125 +/- 0.070906 (95% CI +/- 0.025373) |
| JEPA + post-hoc BEDC report | 30 | 0.376563 +/- 0.065184 (95% CI +/- 0.023326) | 0.000000 +/- 0.000000 (95% CI +/- 0.000000) | 0.392188 +/- 0.074354 (95% CI +/- 0.026607) | 0.521875 +/- 0.070906 (95% CI +/- 0.025373) | -0.459049 +/- 0.116387 (95% CI +/- 0.041649) | 0.814159 +/- 0.050458 (95% CI +/- 0.018056) | 0.259333 +/- 0.051446 (95% CI +/- 0.018410) |
| BEDC-JEPA end-to-end | 30 | 0.376563 +/- 0.065184 (95% CI +/- 0.023326) | 0.000000 +/- 0.000000 (95% CI +/- 0.000000) | 0.386458 +/- 0.070826 (95% CI +/- 0.025345) | 0.521875 +/- 0.070906 (95% CI +/- 0.025373) | -0.465568 +/- 0.114317 (95% CI +/- 0.040908) | 0.593735 +/- 0.138598 (95% CI +/- 0.049597) | 0.131096 +/- 0.043371 (95% CI +/- 0.015520) |

## Model 4 vs Model 3

| metric | model 3 mean | model 4 mean | model4 - model3 | z | approx p | model4 better | significant |
| --- | ---: | ---: | ---: | ---: | ---: | --- | --- |
| unsafe_state_rate | 0.376563 | 0.376563 | 0.000000 | nan | nan | False | False |
| UnloggedErrorRate | 0.000000 | 0.000000 | 0.000000 | nan | nan | False | False |
| safe_planning_success | 0.521875 | 0.521875 | 0.000000 | nan | nan | False | False |
| planning_regret | -0.459049 | -0.465568 | -0.006519 | -4.174904 | 0.000030 | True | True |

Headline claim supported: `False`

## Lambda Safety/Cost Frontier

| arm | lambda | unsafe-state rate | UnloggedErrorRate | safe-planning success | planning regret |
| --- | ---: | ---: | ---: | ---: | ---: |
| Vanilla JEPA | 0.0 | 0.376563 +/- 0.065184 (95% CI +/- 0.023326) | 0.000000 +/- 0.000000 (95% CI +/- 0.000000) | 0.521875 +/- 0.070906 (95% CI +/- 0.025373) | -0.466815 +/- 0.116303 (95% CI +/- 0.041618) |
| Vanilla JEPA | 0.25 | 0.376563 +/- 0.065184 (95% CI +/- 0.023326) | 0.000000 +/- 0.000000 (95% CI +/- 0.000000) | 0.521875 +/- 0.070906 (95% CI +/- 0.025373) | -0.466815 +/- 0.116303 (95% CI +/- 0.041618) |
| Vanilla JEPA | 0.5 | 0.376563 +/- 0.065184 (95% CI +/- 0.023326) | 0.000000 +/- 0.000000 (95% CI +/- 0.000000) | 0.521875 +/- 0.070906 (95% CI +/- 0.025373) | -0.466815 +/- 0.116303 (95% CI +/- 0.041618) |
| Vanilla JEPA | 1.0 | 0.376563 +/- 0.065184 (95% CI +/- 0.023326) | 0.000000 +/- 0.000000 (95% CI +/- 0.000000) | 0.521875 +/- 0.070906 (95% CI +/- 0.025373) | -0.466815 +/- 0.116303 (95% CI +/- 0.041618) |
| Vanilla JEPA | 2.0 | 0.376563 +/- 0.065184 (95% CI +/- 0.023326) | 0.000000 +/- 0.000000 (95% CI +/- 0.000000) | 0.521875 +/- 0.070906 (95% CI +/- 0.025373) | -0.466815 +/- 0.116303 (95% CI +/- 0.041618) |
| JEPA + post-hoc probe | 0.0 | 0.376563 +/- 0.065184 (95% CI +/- 0.023326) | 0.000000 +/- 0.000000 (95% CI +/- 0.000000) | 0.521875 +/- 0.070906 (95% CI +/- 0.025373) | -0.467844 +/- 0.116100 (95% CI +/- 0.041546) |
| JEPA + post-hoc probe | 0.25 | 0.376563 +/- 0.065184 (95% CI +/- 0.023326) | 0.000000 +/- 0.000000 (95% CI +/- 0.000000) | 0.521875 +/- 0.070906 (95% CI +/- 0.025373) | -0.467844 +/- 0.116100 (95% CI +/- 0.041546) |
| JEPA + post-hoc probe | 0.5 | 0.376563 +/- 0.065184 (95% CI +/- 0.023326) | 0.000000 +/- 0.000000 (95% CI +/- 0.000000) | 0.521875 +/- 0.070906 (95% CI +/- 0.025373) | -0.467844 +/- 0.116100 (95% CI +/- 0.041546) |
| JEPA + post-hoc probe | 1.0 | 0.376563 +/- 0.065184 (95% CI +/- 0.023326) | 0.000000 +/- 0.000000 (95% CI +/- 0.000000) | 0.521875 +/- 0.070906 (95% CI +/- 0.025373) | -0.467844 +/- 0.116100 (95% CI +/- 0.041546) |
| JEPA + post-hoc probe | 2.0 | 0.376563 +/- 0.065184 (95% CI +/- 0.023326) | 0.000000 +/- 0.000000 (95% CI +/- 0.000000) | 0.521875 +/- 0.070906 (95% CI +/- 0.025373) | -0.467844 +/- 0.116100 (95% CI +/- 0.041546) |
| JEPA + post-hoc BEDC report | 0.0 | 0.376563 +/- 0.065184 (95% CI +/- 0.023326) | 0.000000 +/- 0.000000 (95% CI +/- 0.000000) | 0.521875 +/- 0.070906 (95% CI +/- 0.025373) | -0.467064 +/- 0.116068 (95% CI +/- 0.041534) |
| JEPA + post-hoc BEDC report | 0.25 | 0.376563 +/- 0.065184 (95% CI +/- 0.023326) | 0.000000 +/- 0.000000 (95% CI +/- 0.000000) | 0.521875 +/- 0.070906 (95% CI +/- 0.025373) | -0.467372 +/- 0.115866 (95% CI +/- 0.041462) |
| JEPA + post-hoc BEDC report | 0.5 | 0.376563 +/- 0.065184 (95% CI +/- 0.023326) | 0.000000 +/- 0.000000 (95% CI +/- 0.000000) | 0.521875 +/- 0.070906 (95% CI +/- 0.025373) | -0.466363 +/- 0.116462 (95% CI +/- 0.041675) |
| JEPA + post-hoc BEDC report | 1.0 | 0.376563 +/- 0.065184 (95% CI +/- 0.023326) | 0.000000 +/- 0.000000 (95% CI +/- 0.000000) | 0.521875 +/- 0.070906 (95% CI +/- 0.025373) | -0.459049 +/- 0.116387 (95% CI +/- 0.041649) |
| JEPA + post-hoc BEDC report | 2.0 | 0.376563 +/- 0.065184 (95% CI +/- 0.023326) | 0.000000 +/- 0.000000 (95% CI +/- 0.000000) | 0.521875 +/- 0.070906 (95% CI +/- 0.025373) | -0.436090 +/- 0.117670 (95% CI +/- 0.042108) |
| BEDC-JEPA end-to-end | 0.0 | 0.376563 +/- 0.065184 (95% CI +/- 0.023326) | 0.000000 +/- 0.000000 (95% CI +/- 0.000000) | 0.521875 +/- 0.070906 (95% CI +/- 0.025373) | -0.471520 +/- 0.114286 (95% CI +/- 0.040897) |
| BEDC-JEPA end-to-end | 0.25 | 0.376563 +/- 0.065184 (95% CI +/- 0.023326) | 0.000000 +/- 0.000000 (95% CI +/- 0.000000) | 0.521875 +/- 0.070906 (95% CI +/- 0.025373) | -0.471247 +/- 0.113987 (95% CI +/- 0.040790) |
| BEDC-JEPA end-to-end | 0.5 | 0.376563 +/- 0.065184 (95% CI +/- 0.023326) | 0.000000 +/- 0.000000 (95% CI +/- 0.000000) | 0.521875 +/- 0.070906 (95% CI +/- 0.025373) | -0.470169 +/- 0.113978 (95% CI +/- 0.040786) |
| BEDC-JEPA end-to-end | 1.0 | 0.376563 +/- 0.065184 (95% CI +/- 0.023326) | 0.000000 +/- 0.000000 (95% CI +/- 0.000000) | 0.521875 +/- 0.070906 (95% CI +/- 0.025373) | -0.465568 +/- 0.114317 (95% CI +/- 0.040908) |
| BEDC-JEPA end-to-end | 2.0 | 0.375521 +/- 0.065715 (95% CI +/- 0.023516) | 0.000000 +/- 0.000000 (95% CI +/- 0.000000) | 0.522917 +/- 0.071748 (95% CI +/- 0.025675) | -0.445290 +/- 0.115381 (95% CI +/- 0.041289) |

## Applicability Boundary

- admitted_family: `"Gaussian-OU toy world with script-local action-conditioned replay."`
- model: `"Runner-local NumPy ridge dynamics predictor over z, distinction, gap, and action features."`
- sample_count: `384`
- seed_count: `30`
- arm_definitions: `{"bedc_jepa_end_to_end": "BEDC-JEPA end-to-end", "jepa_posthoc_bedc_report": "JEPA + post-hoc BEDC report", "jepa_posthoc_probe": "JEPA + post-hoc probe", "vanilla_jepa": "Vanilla JEPA"}`
- planner_horizon: `3`
- lambda_range: `[0.0, 0.25, 0.5, 1.0, 2.0]`
- deterministic_fallback_boundary: `"The experiment uses the deterministic fallback latent surface from the existing Gaussian-OU lab runner and does not claim torch-only representation coverage."`
- hazard_boundary: `{"collision_radius": 0.36, "hazard_center": [0.08, 0.06], "hazard_radius": 0.54, "world_bound": 2.75}`

## Negative Result Note

The four-arm comparison is falsifiable: if the end-to-end arm does not beat the post-hoc BEDC report arm on the primary safety metrics, the report records that outcome directly.

## Source Artifacts

- Generation script: `scripts/run_gaussian_ou_dynamics_planning.py`
- Canonical runner: `scripts/run_gaussian_ou_lejepa.py::run_experiment`
- Distinction runner: `scripts/run_gaussian_ou_distinction_head.py`
- JSON artifact: `reports/gaussian_ou_dynamics_planning.json`
- Report artifact: `reports/gaussian_ou_dynamics_planning.md`
- Import dependency chain:
  - `scripts/run_gaussian_ou_dynamics_planning.py`
  - `scripts.run_gaussian_ou_lejepa.run_experiment`
  - `scripts.run_gaussian_ou_distinction_head._seeds`
  - `scripts.run_gaussian_ou_distinction_head._train_eval_split`
  - `scripts.run_gaussian_ou_distinction_head._label_truth`
  - `bedc_quality_lab.toy_world.make_toy_batch`
  - `scripts.experiment_stats.metric_stats`
