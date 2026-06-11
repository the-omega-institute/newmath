<!-- payload-sha256: 0001c956dbc59d176258372780ab99f23bd0f1e2ec524e42be6c0855e71ca3f2 -->
# DGT Model Card

- Schema: `bedc-quality-lab:dgt-model-card`
- Card: `bedc-quality-lab:dgt-model-card`
- Status: `pass`
- Source pointer: `reports/canonical/dgt-model-card.json:$`

## Intended Use

- bounded research card for the DGT canonical artifacts (`reports/canonical/discovery-gated-transformer.json:$.model_id`)
- pointer index for L0 and L1 review boundaries (`reports/canonical/dgt-l0-controls.json:$.l0_toy_projection`)

## Not Intended Use

- bounded BEDC prototype
- not production model
- not LLM replacement
- not global Transformer superiority
- current L1 evidence invalid as fair architecture comparison

## Boundaries

- L0 review status: `pass` (`reports/canonical/dgt-l0-controls.json:$.l0_toy_projection`)
- L1 scoped review: `pass` (`reports/canonical/dgt-l1-controls.json:$.l1_tiny_sequence_projection`)
- fair architecture comparison: `defer-to-fair-reconstruction` (`reports/canonical/dgt-base-undertraining-audit.json:$.base_undertraining_audit`)
- ablation null interpretation: `mixed` (`reports/canonical/dgt-ablation-null-decomposition.json:$.null_decomposition`)
- dgt-l0-controls construct validity: `fail` (`reports/canonical/dgt-l0-controls.json:$.construct_validity_hardgates`)
- dgt-l1-controls construct validity: `pass` (`reports/canonical/dgt-l1-controls.json:$.construct_validity_hardgates`)

## Known Failure Modes

- construct-validity boundary: `construct-boundary` (`reports/canonical/dgt-base-undertraining-audit.json:$.base_undertraining_audit.construct_validity`)
- fair comparison boundary: `defer-to-fair-reconstruction` (`reports/canonical/dgt-base-undertraining-audit.json:$.base_undertraining_audit.claim_action`)
- ablation null decomposition: `mixed` (`reports/canonical/dgt-ablation-null-decomposition.json:$.null_decomposition`)
- OOD boundary: `not-claimed` (`reports/canonical/dgt-l1-controls.json:$.l1_tiny_sequence_projection.ood_boundary`)

## Hardgates

- CARD-HG1: `pass`
- CARD-HG2: `pass`
- CARD-HG3: `pass`
- CARD-HG4: `pass`
- CARD-HG5: `pass`
- CARD-HG6: `pass`
- CARD-HG7: `pass`
- CARD-HG8: `pass`
- CARD-HG9: `pass`

## Not Claimed

- No production deployment authority.
- No global model superiority claim.
- No LLM replacement claim.
- No fair architecture advantage claim.
- No OOD generalization claim.
- No component-causal closure claim.
