# Observed-Debt Sweep

- JSON artifact: `reports/canonical/observed-debt-sweep.json`
- Report artifact: `reports/canonical/observed-debt-sweep.md`
- Generated at: `2026-06-12T17:17:37.919801+00:00`
- Mode: `full`
- Envelope schema pointer: `$.schema_id`
- Actual seed count pointer: `$.config.actual_seed_count_by_axis`
- Baseline pointer: `$.baseline`
- Cell records pointer: `$.cells`
- Hardgate evidence pointer: `$.hardgate_evidence`

## Grid

| axis | cell count | seed counts | row | skipped | values pointer |
| --- | ---: | --- | --- | ---: | --- |
| C1 | 4 | `10` | `source/dimension-match` | 0 | `$.grid_summary.C1.axis_values` |
| C2 | 6 | `6` | `classifier/optimizer-certificate` | 0 | `$.grid_summary.C2.axis_values` |
| C3 | 5 | `10` | `source/finite-sample-support` | 0 | `$.grid_summary.C3.axis_values` |
| C4 | 2 | `6` | `source/action-transition-identification` | 0 | `$.grid_summary.C4.axis_values` |

## Effect Pointers

| axis | value | row | metric | cell mean | delta | CI half-width | verdict | effect pointer |
| --- | ---: | --- | --- | ---: | ---: | ---: | --- | --- |
| C1 | 1 | `source/dimension-match` | `linear_identifiability_r2` | 0.476071 | -0.448718 | 0.010641 | `observed-debt` | `$.cells[0].effect` |
| C1 | 2 | `source/dimension-match` | `linear_identifiability_r2` | 0.925706 | 0.000917 | 0.002421 | `observed-debt-pipeline-only` | `$.cells[1].effect` |
| C1 | 3 | `source/dimension-match` | `linear_identifiability_r2` | 0.925706 | 0.000917 | 0.002421 | `observed-debt-pipeline-only` | `$.cells[2].effect` |
| C1 | 4 | `source/dimension-match` | `linear_identifiability_r2` | 0.925706 | 0.000917 | 0.002421 | `observed-debt-pipeline-only` | `$.cells[3].effect` |
| C2 | 10 | `classifier/optimizer-certificate` | `linear_identifiability_r2` | 0.923810 | -0.000979 | 0.004980 | `observed-debt-pipeline-only` | `$.cells[4].effect` |
| C2 | 20 | `classifier/optimizer-certificate` | `linear_identifiability_r2` | 0.923810 | -0.000979 | 0.004980 | `observed-debt-pipeline-only` | `$.cells[5].effect` |
| C2 | 50 | `classifier/optimizer-certificate` | `linear_identifiability_r2` | 0.923810 | -0.000979 | 0.004980 | `observed-debt-pipeline-only` | `$.cells[6].effect` |
| C2 | 100 | `classifier/optimizer-certificate` | `linear_identifiability_r2` | 0.923810 | -0.000979 | 0.004980 | `observed-debt-pipeline-only` | `$.cells[7].effect` |
| C2 | 500 | `classifier/optimizer-certificate` | `linear_identifiability_r2` | 0.923810 | -0.000979 | 0.004980 | `observed-debt-pipeline-only` | `$.cells[8].effect` |
| C2 | 2000 | `classifier/optimizer-certificate` | `linear_identifiability_r2` | 0.923810 | -0.000979 | 0.004980 | `observed-debt-pipeline-only` | `$.cells[9].effect` |
| C3 | 128 | `source/finite-sample-support` | `linear_identifiability_r2` | 0.936457 | 0.011669 | 0.010024 | `observed-debt-pipeline-only` | `$.cells[10].effect` |
| C3 | 256 | `source/finite-sample-support` | `linear_identifiability_r2` | 0.927005 | 0.002216 | 0.010743 | `observed-debt-pipeline-only` | `$.cells[11].effect` |
| C3 | 512 | `source/finite-sample-support` | `linear_identifiability_r2` | 0.922320 | -0.002468 | 0.006833 | `observed-debt-pipeline-only` | `$.cells[12].effect` |
| C3 | 1024 | `source/finite-sample-support` | `linear_identifiability_r2` | 0.925905 | 0.001116 | 0.004730 | `observed-debt-pipeline-only` | `$.cells[13].effect` |
| C3 | 4096 | `source/finite-sample-support` | `linear_identifiability_r2` | 0.923184 | -0.001604 | 0.003763 | `observed-debt-pipeline-only` | `$.cells[14].effect` |
| C4 | False | `source/action-transition-identification` | `linear_identifiability_r2` | 0.923861 | -0.000928 | 0.002251 | `observed-debt-pipeline-only` | `$.cells[15].effect` |
| C4 | True | `source/action-transition-identification` | `linear_identifiability_r2` | 0.923861 | -0.000928 | 0.002251 | `observed-debt-pipeline-only` | `$.cells[16].effect` |

## Boundaries

- Global claim flag pointer: `$.global_claim_flag`
- C4 claim boundary pointer: `$.claim_boundary.C4`
- Not claimed pointer: `$.not_claimed`
- Source artifacts pointer: `$.source_artifacts`
