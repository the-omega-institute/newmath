# Scaling Ladder

- Generated at: `2026-06-11T22:15:23.594072+00:00`
- Artifact: `bedc-quality-lab:scaling-ladder`
- Schema: `bedc-quality-lab:scaling-ladder`

## Levels

| level | state | reason | owner decision | provenance | construct validity | split | separation |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `L0_toy` | `boundary` | `stale-or-injected` | `reports/canonical/scaling-ladder.json:$.levels[0].owner_contracts.owner_decision` | `reports/canonical/scaling-ladder.json:$.levels[0].owner_contracts.evidence_provenance` | `reports/canonical/dgt-base-undertraining-audit.json:$.base_undertraining_audit.construct_validity` | `reports/canonical/scaling-ladder.json:$.levels[0].owner_contracts.split_winnability` | `reports/canonical/scaling-ladder.json:$.levels[0].owner_contracts.separation` |
| `L1_tiny_sequence` | `boundary` | `stale-or-injected` | `reports/canonical/scaling-ladder.json:$.levels[1].owner_contracts.owner_decision` | `reports/canonical/scaling-ladder.json:$.levels[1].owner_contracts.evidence_provenance` | `reports/canonical/dgt-base-undertraining-audit.json:$.base_undertraining_audit.construct_validity` | `reports/canonical/scaling-ladder.json:$.levels[1].owner_contracts.split_winnability` | `reports/canonical/scaling-ladder.json:$.levels[1].owner_contracts.separation` |

## Boundary Ledger

| level | prior | current | reason | failed contract |
| --- | --- | --- | --- | --- |
| `L0_toy` | `open` | `boundary` | `stale-or-injected` | `reports/canonical/discovery-gated-transformer.json:$.scaling_ladder` |
| `L1_tiny_sequence` | `open` | `boundary` | `stale-or-injected` | `reports/canonical/discovery-gated-transformer.json:$.scaling_ladder` |

## Hardgates

| gate | status | pointer |
| --- | --- | --- |
| `SL-HG1-evidence-provenance` | `fail` | `reports/canonical/index.json:$.evidence_provenance` |
| `SL-HG2-construct-validity` | `fail` | `reports/canonical/dgt-base-undertraining-audit.json:$.base_undertraining_audit.construct_validity` |
| `SL-HG3-owner-decision` | `fail` | `reports/canonical/scaling-ladder.json:$.levels[*].owner_decision_pointer` |
| `SL-HG4-split-separation` | `fail` | `reports/canonical/scaling-ladder.json:$.levels` |
| `SL-HG5-no-injected-opening` | `fail` | `reports/canonical/discovery-gated-transformer.json:$.scaling_ladder` |

## Not Claimed

- Scaling-ladder decisions are bounded canonical owner rows.
- No non-owner artifact is an opening authority.
- No production, global superiority, or natural-language capability claim is made.
- Missing upstream owner contracts fail closed rather than inheriting adjacent level decisions.
