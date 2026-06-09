# DGT neural ablation

- Status: `pass`
- Device: `mps`
- Arms: `11`
- Torch steps per arm: `36`
- Claim capsule: `reports/runs/dgt-neural-ablation/claim_capsule.json:$`

## NABL hardgates

- `NABL-HG1`: `pass`
- `NABL-HG2`: `pass`
- `NABL-HG3`: `pass`
- `NABL-HG4`: `pass`
- `NABL-HG5`: `pass`
- `NABL-HG6`: `pass`
- `NABL-HG7`: `pass`

## Component claims

- `LAT`: Under the bounded toy training protocol, removing LAT causes measurable degradation on FalseLedgerRate, JetCoverage, UER, benefit_q, debt_q, quality_q.
- `CGA`: Under the bounded toy training protocol, removing CGA causes measurable degradation on FalseLedgerRate, JetCoverage, UER, benefit_q, debt_q, quality_q.
- `DRT`: Under the bounded toy training protocol, removing DRT causes measurable degradation on FalseLedgerRate, JetCoverage, UER, benefit_q, debt_q, quality_q.
- `gap_head`: Under the bounded toy training protocol, removing gap_head causes measurable degradation on FalseLedgerRate, UER, benefit_q, classifier_shift_count, debt_q, quality_q.
- `ledger_head`: Under the bounded toy training protocol, removing ledger_head causes measurable degradation on FalseLedgerRate, UER, benefit_q, classifier_shift_count, debt_q, quality_q.
- `route_certificate`: Under the bounded toy training protocol, removing route_certificate causes measurable degradation on FalseLedgerRate, UER, benefit_q, classifier_shift_count, debt_q, quality_q.
- `mechanism_probe`: Under the bounded toy training protocol, removing mechanism_probe causes measurable degradation on FalseLedgerRate, UER, benefit_q, debt_q, quality_q.
- `jet_loss`: Under the bounded toy training protocol, removing jet_loss causes measurable degradation on FalseLedgerRate, JetCoverage, UER, benefit_q, debt_q, quality_q.
- `negative_witness_loss`: Under the bounded toy training protocol, removing negative_witness_loss causes measurable degradation on FalseLedgerRate, JetCoverage, UER, benefit_q, debt_q, negative_witness_hits, quality_q.

## Boundary ledger

- `LAT`: `measurable_effect` - measurable bounded-toy effect supports a scoped component-causal claim
- `CGA`: `measurable_effect` - measurable bounded-toy effect supports a scoped component-causal claim
- `DRT`: `measurable_effect` - measurable bounded-toy effect supports a scoped component-causal claim
- `gap_head`: `measurable_effect` - measurable bounded-toy effect supports a scoped component-causal claim
- `ledger_head`: `measurable_effect` - measurable bounded-toy effect supports a scoped component-causal claim
- `route_certificate`: `measurable_effect` - measurable bounded-toy effect supports a scoped component-causal claim
- `mechanism_probe`: `measurable_effect` - measurable bounded-toy effect supports a scoped component-causal claim
- `jet_loss`: `measurable_effect` - measurable bounded-toy effect supports a scoped component-causal claim
- `negative_witness_loss`: `measurable_effect` - measurable bounded-toy effect supports a scoped component-causal claim
- `scope_seal`: `no_measurable_effect` - HG7 boundary: no measurable effect; component-causal claim blocked
