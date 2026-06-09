# DGT neural ablation

- Status: `pass`
- PURE status: `pass`
- Device: `mps`
- Arms: `11`
- Seeds: `3`
- Torch steps per arm seed: `40`
- Claim capsule: `reports/runs/dgt-neural-ablation/claim_capsule.json:$`

## PURE hardgates

- `PURE-HG1`: `pass`
- `PURE-HG2`: `pass`
- `PURE-HG3`: `pass`
- `PURE-HG4`: `pass`
- `PURE-HG5`: `pass`
- `PURE-HG6`: `pass`
- `PURE-HG7`: `pass`

## NABL hardgates

- `NABL-HG1`: `pass`
- `NABL-HG2`: `pass`
- `NABL-HG3`: `pass`
- `NABL-HG4`: `pass`
- `NABL-HG5`: `pass`
- `NABL-HG6`: `pass`
- `NABL-HG7`: `pass`

## Component claims

- `DRT`: Under the bounded toy training protocol, removing DRT causes measured degradation on benefit_q, negative_witness_hits, quality_q.
- `ledger_head`: Under the bounded toy training protocol, removing ledger_head causes measured degradation on JetCoverage, UER, benefit_q, classifier_shift_count, debt_q, quality_q, scope_pressure_q.
- `scope_seal`: Under the bounded toy training protocol, removing scope_seal causes measured degradation on UER, benefit_q, classifier_shift_count, debt_q, negative_witness_hits, quality_q, scope_pressure_q.

## Boundary ledger

- `LAT`: `blocked` - NABL-HG7
- `CGA`: `blocked` - NABL-HG7
- `DRT`: `measured` - measured paired training delta supports a scoped component-causal claim
- `gap_head`: `blocked` - NABL-HG7
- `ledger_head`: `measured` - measured paired training delta supports a scoped component-causal claim
- `route_certificate`: `blocked` - NABL-HG7
- `mechanism_probe`: `blocked` - NABL-HG7
- `jet_loss`: `blocked` - NABL-HG7
- `negative_witness_loss`: `blocked` - NABL-HG7
- `scope_seal`: `measured` - measured paired training delta supports a scoped component-causal claim
