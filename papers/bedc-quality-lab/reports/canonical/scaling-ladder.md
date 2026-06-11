# Scaling Ladder

- Generated at: `2026-06-11T20:40:24.095919+00:00`
- Artifact: `bedc-quality-lab:scaling-ladder`
- Schema: `bedc-quality-lab:scaling-ladder`

## Levels

| level | state | reason | owner decision | provenance | construct validity | split | separation |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `L0_toy` | `boundary` | `stale-or-injected` | `reports/canonical/dgt-l0-controls.json:$.l0_toy_projection.owner_decision` | `reports/canonical/index.json:$.evidence_provenance` | `reports/canonical/dgt-base-undertraining-audit.json:$.base_undertraining_audit.construct_validity` | `reports/canonical/dgt-l0-controls.json:$.l0_toy_projection.split_winnability` | `reports/canonical/dgt-l0-controls.json:$.l0_toy_projection.separation` |
| `L1_tiny_sequence` | `boundary` | `stale-or-injected` | `reports/canonical/dgt-l1-controls.json:$.l1_tiny_sequence_projection.fair_decision` | `reports/canonical/index.json:$.evidence_provenance` | `reports/canonical/dgt-base-undertraining-audit.json:$.base_undertraining_audit.construct_validity` | `reports/canonical/dgt-l1-controls.json:$.l1_tiny_sequence_projection.split_winnability` | `reports/canonical/dgt-l1-controls.json:$.l1_tiny_sequence_projection.separation` |

## Boundary Ledger

| level | prior | current | reason | failed contract |
| --- | --- | --- | --- | --- |
| `L0_toy` | `open` | `boundary` | `stale-or-injected` | `reports/canonical/dgt-l0-controls.json:$.l0_toy_projection` |
| `L1_tiny_sequence` | `open` | `boundary` | `stale-or-injected` | `reports/canonical/dgt-l1-controls.json:$.l1_tiny_sequence_projection` |

## Hardgates

| gate | status | pointer |
| --- | --- | --- |
| `SL-HG1-evidence-provenance` | `pass` | `reports/canonical/index.json:$.evidence_provenance` |
| `SL-HG2-construct-validity` | `pass` | `reports/canonical/dgt-base-undertraining-audit.json:$.base_undertraining_audit.construct_validity` |
| `SL-HG3-owner-decision` | `pass` | `reports/canonical/scaling-ladder.json:$.levels[*].owner_decision_pointer` |
| `SL-HG4-split-separation` | `pass` | `reports/canonical/scaling-ladder.json:$.levels` |
| `SL-HG5-no-injected-opening` | `fail` | `reports/canonical/discovery-gated-transformer.json:$.scaling_ladder` |

## Not Claimed

- Scaling-ladder decisions are bounded canonical owner rows.
- No non-owner artifact is an opening authority.
- No production, global superiority, or natural-language capability claim is made.
- Missing upstream owner contracts fail closed rather than inheriting adjacent level decisions.
