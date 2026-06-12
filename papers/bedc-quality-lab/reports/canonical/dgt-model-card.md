<!-- payload-sha256: 4d5c7a1c74e3ef7b42a9db8c345d1ab1a2d91a3b0f453f6c139cc3a187c70cb1 -->
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

- L0 review status: `scoped-boundary` (`reports/canonical/dgt-l0-controls.json:$.l0_toy_projection`)
- L1 scoped review: `pass` (`reports/canonical/dgt-l1-controls.json:$.l1_tiny_sequence_projection`)
- fair architecture comparison: `bounded-negative` (`reports/canonical/fair-l1-decision.json:$.ladder_state_projection`)
- ablation null interpretation: `mixed` (`reports/canonical/dgt-ablation-null-decomposition.json:$.null_decomposition`)
- dgt-l0-controls construct validity: `fail` (`reports/canonical/dgt-l0-controls.json:$.construct_validity_hardgates`)
- dgt-l1-controls construct validity: `pass` (`reports/canonical/dgt-l1-controls.json:$.construct_validity_hardgates`)

## Known Failure Modes

- construct-validity boundary: `construct-boundary` (`reports/canonical/dgt-base-undertraining-audit.json:$.base_undertraining_audit.construct_validity`)
- fair comparison boundary: `l1-bounded-negative` (`reports/canonical/fair-l1-decision.json:$.ladder_state_projection`)
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
