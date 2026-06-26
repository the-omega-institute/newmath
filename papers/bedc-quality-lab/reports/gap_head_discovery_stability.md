# Gap-Head Discovery Stability

- Artifact: `bedc-quality-lab:gap-head-discovery-stability`
- Generated at: `2026-06-02T07:32:05.234066+00:00`
- Final verdict: `robust_positive`
- Backend use_torch: `false`
- Elapsed seconds: `3.342294`
- Grid: `independent_seed_grid`
- Cell shape: `one source payload per sample_count and child seed`
- Sample counts: `96, 192, 384, 768`
- Cells per sample count: `10`
- Total cells: `40`
- Invalid cells: `0`

## Sample Counts

| sample count | positive seeds | positive rate | mean net information | mean surface delta | mean shift information | invalid cells |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 96 | 10/10 | 1.000000 | 0.653448 +/- 0.152315 (95% CI +/- 0.094406) | 1.000000 +/- 0.000000 (95% CI +/- 0.000000) | 1.000000 +/- 0.000000 (95% CI +/- 0.000000) | 0 |
| 192 | 10/10 | 1.000000 | 0.627586 +/- 0.116781 (95% CI +/- 0.072382) | 1.000000 +/- 0.000000 (95% CI +/- 0.000000) | 1.000000 +/- 0.000000 (95% CI +/- 0.000000) | 0 |
| 384 | 10/10 | 1.000000 | 0.648261 +/- 0.104673 (95% CI +/- 0.064877) | 1.000000 +/- 0.000000 (95% CI +/- 0.000000) | 1.000000 +/- 0.000000 (95% CI +/- 0.000000) | 0 |
| 768 | 10/10 | 1.000000 | 0.674348 +/- 0.110130 (95% CI +/- 0.068259) | 1.000000 +/- 0.000000 (95% CI +/- 0.000000) | 1.000000 +/- 0.000000 (95% CI +/- 0.000000) | 0 |

## Boundary

- Representation boundary: `learned_h`
- Inference no ground-truth z: `true`
- Projection helper: `scripts/run_gap_head_discovery.py::_build_gap_head_projection`
- Verdict helper: `scripts/run_gap_head_discovery.py::_verdict_payload`

## Notes

Each cell contains exactly one source seed, so `surface_delta_count` is expected to be smaller than the #521 30-record aggregate.
Markdown values render from the JSON payload.
