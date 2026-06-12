# Input Accessibility Audit

- Schema: `bedc-quality-lab:input-accessibility`
- Rows: `5`
- Access gate: `fail`
- OOD gate: `fail`
- Registry digest: `65b6ade09e466cb7e27780441c143cd2b87bde0020a97d3394351d754512d7c0`

## Rows

| row | experiment | split | arm | visible | required | missing | coverage | exclusion |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `14ed3059f448592a` | `dgt_l1_tiny_sequence` | `ood` | `information_starved_l1_baseline` | `x_minus_1` | `x_minus_1, x_minus_3` | `x_minus_3` | `fail` | `boundary-ledger-only` |
| `2501a86ca1e1740b` | `dgt_l1_tiny_sequence` | `in_distribution` | `matched_random_structural_l1` | `x_minus_1, x_minus_2, batch_shifted_tokens` | `x_minus_1, x_minus_2` | `none` | `pass` | `none` |
| `59a87f14e31796e4` | `dgt_l1_tiny_sequence` | `in_distribution` | `information_starved_l1_baseline` | `x_minus_1` | `x_minus_1, x_minus_2` | `x_minus_2` | `fail` | `demote-from-fair-baseline` |
| `815dc7a2b911856d` | `dgt_l1_tiny_sequence` | `in_distribution` | `dgt_l1` | `x_minus_1, x_minus_2, gates` | `x_minus_1, x_minus_2` | `none` | `pass` | `none` |
| `919ac19434f330f9` | `dgt_l1_tiny_sequence` | `ood` | `dgt_l1` | `x_minus_1, x_minus_2, gates` | `x_minus_1, x_minus_3` | `x_minus_3` | `fail` | `boundary-ledger-only` |

## Boundary Ledger

- `14ed3059f448592a` `boundary-ledger-only` missing `x_minus_3`; source `reports/canonical/input-accessibility.json#row_id=14ed3059f448592a`
- `59a87f14e31796e4` `information-starved` missing `x_minus_2`; source `reports/canonical/input-accessibility.json#row_id=59a87f14e31796e4`
- `919ac19434f330f9` `boundary-ledger-only` missing `x_minus_3`; source `reports/canonical/input-accessibility.json#row_id=919ac19434f330f9`

## Not Claimed

- Input-accessibility rows audit callable source only.
- No training result is produced by this audit.
- No architecture claim is supported when required label variables are invisible to the feature callable.
- No out-of-distribution claim is supported by a row marked unanswerable.
