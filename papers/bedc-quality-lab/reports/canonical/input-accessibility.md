# Input Accessibility Audit

- Schema: `bedc-quality-lab:input-accessibility`
- Rows: `8`
- Access gate: `fail`
- OOD gate: `fail`
- Registry digest: `096af276a1b4bca2bf71cce367aa283e3c48741705e4c08c8821800cd2fc7af1`

## Rows

| row | experiment | split | arm | visible | required | missing | coverage | exclusion |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `204ec8632f4351bb` | `dgt_l1_tiny_sequence` | `in_distribution` | `parameter_matched_attention` | `x_minus_1, x_minus_2, full_sequence` | `x_minus_1, x_minus_2` | `none` | `pass` | `none` |
| `39f940c7504e9416` | `dgt_l1_tiny_sequence` | `ood` | `input_ablation_masked_tail` | `x_minus_1, full_sequence` | `x_minus_1, x_minus_2` | `x_minus_2` | `fail` | `boundary-ledger-only` |
| `6001d70d815f574b` | `dgt_l1_tiny_sequence` | `in_distribution` | `input_ablation_masked_tail` | `x_minus_1, full_sequence` | `x_minus_1, x_minus_2` | `x_minus_2` | `fail` | `demote-from-fair-baseline` |
| `67dd876765f7cbbd` | `dgt_l1_tiny_sequence` | `ood` | `compute_matched_attention` | `x_minus_1, x_minus_2, full_sequence` | `x_minus_1, x_minus_2` | `none` | `pass` | `none` |
| `72e156330c8aeb12` | `dgt_l1_tiny_sequence` | `ood` | `dgt_l1` | `x_minus_1, x_minus_2, full_sequence` | `x_minus_1, x_minus_2` | `none` | `pass` | `none` |
| `9c45ac4c2f3c1d32` | `dgt_l1_tiny_sequence` | `in_distribution` | `dgt_l1` | `x_minus_1, x_minus_2, full_sequence` | `x_minus_1, x_minus_2` | `none` | `pass` | `none` |
| `d3c1cb0042d46cd5` | `dgt_l1_tiny_sequence` | `in_distribution` | `compute_matched_attention` | `x_minus_1, x_minus_2, full_sequence` | `x_minus_1, x_minus_2` | `none` | `pass` | `none` |
| `d4aef293c17f980d` | `dgt_l1_tiny_sequence` | `ood` | `parameter_matched_attention` | `x_minus_1, x_minus_2, full_sequence` | `x_minus_1, x_minus_2` | `none` | `pass` | `none` |

## Boundary Ledger

- `39f940c7504e9416` `boundary-ledger-only` missing `x_minus_2`; source `reports/canonical/input-accessibility.json#row_id=39f940c7504e9416`
- `6001d70d815f574b` `information-starved` missing `x_minus_2`; source `reports/canonical/input-accessibility.json#row_id=6001d70d815f574b`

## Not Claimed

- Input-accessibility rows audit callable source only.
- No training result is produced by this audit.
- No architecture claim is supported when required label variables are invisible to the feature callable.
- No out-of-distribution claim is supported by a row marked unanswerable.
