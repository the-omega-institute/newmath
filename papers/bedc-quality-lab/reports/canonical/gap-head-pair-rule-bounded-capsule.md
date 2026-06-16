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
| `pair_rule_construct_validity` | `blocked` | `reports/canonical/dgt-pair-rule-construct-validity.json:$.downstream_admission.status` |
| `fair_alignment_control_ledger` | `blocked` | `reports/canonical/fair-alignment-control-ledger.json:$.claim_gate.status` |
| `pair_rule_base_exceeds_chance` | `blocked` | `reports/canonical/dgt-l1-controls.json:$.claim_capsule_ref.construct_validity.base_exceeds_chance.gate_status` |
| `pair_rule_attribution` | `blocked` | `reports/canonical/gap-head-pair-rule-attribution.json:$.d5_m.status` |
| `pair_rule_observed_debt_transfer` | `blocked` | `reports/canonical/gap-head-pair-rule-observed-debt-transfer.json:$.observed_debt_transfer.status` |

## Boundary

- Order: `2`
- Starvation policy: `non-starving`
- Cost protocol: `reports/canonical/gap-head-pair-rule-bounded-capsule.json:$.cost_protocol`
- Not claimed: `reports/canonical/gap-head-pair-rule-bounded-capsule.json:$.not_claimed`
