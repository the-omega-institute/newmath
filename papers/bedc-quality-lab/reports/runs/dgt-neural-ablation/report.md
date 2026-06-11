# DGT neural ablation

- Status: `pass`
- PURE status: `pass`
- Stable causal attribution: `none`
- Device: `mps`
- Arms: `11`
- Seeds: `8`
- Torch step grid: `[128, 256]`
- Arm trainings: `176`
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

## NABL2 hardgates

- `NABL2-HG1`: `pass`
- `NABL2-HG2`: `pass`
- `NABL2-HG3`: `pass`
- `NABL2-HG4`: `pass`
- `NABL2-HG5`: `pass`
- `NABL2-HG6`: `pass`

## Component claims

- No positive component-causal claim.

## Boundary ledger

- `LAT`: `blocked` - NABL2-HG3
- `CGA`: `blocked` - NABL2-HG3
- `DRT`: `blocked` - NABL2-HG3
- `gap_head`: `blocked` - NABL2-HG3
- `ledger_head`: `blocked` - NABL2-HG3
- `route_certificate`: `blocked` - NABL2-HG3
- `mechanism_probe`: `blocked` - NABL2-HG3
- `jet_loss`: `blocked` - NABL2-HG3
- `negative_witness_loss`: `blocked` - NABL2-HG3
- `scope_seal`: `blocked` - NABL2-HG3
- `<all>`: `null_result` - no component shows cross-seed-stable causal effect on this bounded toy at 8 seeds / 128-256 steps; component causality requires a harder task (L1+ per scope algebra)
