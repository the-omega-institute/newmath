# Fair Alignment Control Ledger

- Generated at: `2026-06-15T19:17:50.848759+00:00`
- Status: `pass`
- Rows: `2`
- Hardgate: `pass`

| producer | task | fair control | row status | candidate pointer | control pointer | base gate |
| --- | --- | --- | --- | --- | --- | --- |
| `gap-head-on-h` | `gaussian-ou:learned-h-gap-detection` | `matched-random-gap-head` | `pass` | `reports/canonical/gap-head-on-h.json:$.treatment_verdict` | `reports/canonical/gap-head-on-h.json:$.control_verdict` | `reports/canonical/fair-l1-decision.json:$.hardgates.FAIR-L1-HG3` |
| `discovery-regularized-training` | `gaussian-ou:discovery-regularized-replay` | `matched-random-structural-control` | `pass` | `reports/canonical/discovery-regularized-training.json:$.surface_registry.quality.by_arm.DGT_full` | `reports/canonical/discovery-regularized-training.json:$.matched_random_control` | `reports/canonical/fair-l1-decision.json:$.hardgates.FAIR-L1-HG3` |

## Producer Adapters

| producer | adapter role | ledger row |
| --- | --- | --- |
| `gap-head-on-h` | `pointer-only` | `reports/canonical/fair-alignment-control-ledger.json:$.rows[?producer_id=gap-head-on-h]` |
| `discovery-regularized-training` | `pointer-only` | `reports/canonical/fair-alignment-control-ledger.json:$.rows[?producer_id=discovery-regularized-training]` |
