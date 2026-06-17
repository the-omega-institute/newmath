# Aligned State-Generation Export

- schema: `bedc_jepa.aligned_state_generation_export`
- option depths: `[1, 2, 3, 4, 5]`

| split | anchors | episodes | feature dim |
|---|---:|---:|---:|
| train | 2043 | 167 | 4952 |
| calibration | 646 | 56 | 4952 |
| eval | 634 | 55 | 4952 |

The export aligns prediction targets, compute-value option labels, horizon labels, rollout features, and BEDC ledger variables on identical anchors.
