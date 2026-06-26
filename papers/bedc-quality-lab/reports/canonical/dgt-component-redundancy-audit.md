# DGT component redundancy audit

- Audit status: `pass`
- Global recommendation: `redesign-confirmed-redundant-components`
- Confirmed redundant: `route_certificate, mechanism_probe, negative_witness_loss`
- Inconclusive: `LAT`

## Component verdicts

- `LAT`: `inconclusive` (delta `0.000783`, null `mixed`)
- `CGA`: `independent` (delta `0.00182`, null `mixed`)
- `DRT`: `independent` (delta `0.001211`, null `saturation`)
- `gap_head`: `independent` (delta `0.001316`, null `saturation`)
- `ledger_head`: `independent` (delta `0.001683`, null `mixed`)
- `route_certificate`: `confirmed-redundant` (delta `-0.000162`, null `mixed`)
- `mechanism_probe`: `confirmed-redundant` (delta `0.000213`, null `mixed`)
- `jet_loss`: `independent` (delta `-0.000927`, null `saturation`)
- `negative_witness_loss`: `confirmed-redundant` (delta `4.4e-05`, null `mixed`)
- `scope_seal`: `independent` (delta `0.000764`, null `saturation`)

## Not claimed

- Bounded toy component redundancy audit only.
- No production or global DGT component necessity verdict is claimed.
- No architecture redesign is performed by this report.
- No claim outside the existing canonical leave-one-out artifacts is made.
