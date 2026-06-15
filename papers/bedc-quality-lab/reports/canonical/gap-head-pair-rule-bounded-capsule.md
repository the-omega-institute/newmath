# Gap-Head Pair-Rule Bounded Capsule

- Artifact id: `bedc-quality-lab:gap-head-pair-rule-bounded-capsule`
- JSON artifact: `reports/canonical/gap-head-pair-rule-bounded-capsule.json`
- Capsule status pointer: `reports/canonical/gap-head-pair-rule-bounded-capsule.json:$.capsule_verdict.status`
- Positive claim pointer: `reports/canonical/gap-head-pair-rule-bounded-capsule.json:$.positive_claim.status`
- Pair-rule surface pointer: `reports/canonical/gap-head-pair-rule-bounded-capsule.json:$.pair_rule_surface`
- Prerequisite checks pointer: `reports/canonical/gap-head-pair-rule-bounded-capsule.json:$.prerequisite_checks`

## Prerequisite Pointers

| prerequisite | status | owner pointer |
| --- | --- | --- |
| `gap_head_discovery` | `pass` | `reports/canonical/gap-head-discovery.json:$.final_main_claim_status` |
| `gap_head_observed_debt_transfer` | `pass` | `reports/canonical/gap-head-observed-debt-transfer.json:$.gap_head_on_h_observed_debt_transfer.status` |
| `gap_head_attribution_capsule` | `bounded-negative` | `reports/canonical/gap_head_attribution_capsule.json:$.d5_m.status` |

## Boundary

- Order: `2`
- Starvation policy: `non-starving`
- Cost protocol: `reports/canonical/gap-head-pair-rule-bounded-capsule.json:$.cost_protocol`
- Not claimed: `reports/canonical/gap-head-pair-rule-bounded-capsule.json:$.not_claimed`
