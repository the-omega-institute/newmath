# LeJEPA Theorem Ledger

- run_id: `lejepa-theorem-ledger`
- schema_id: `bedc-quality-lab:lejepa-theorem-ledger`
- status: `pass`

## Scope

- Canonical theorem-row ledger for LeJEPA theorem certificates.
- Literature pointers reference this report through `used_by`; this report owns theorem-row status.

## Theorem Rows

| theorem | BEDC role | implemented metrics | ledger debt |
| --- | --- | --- | --- |
| `theorem-1` | `SourceSpec` | `[]` | Source assumptions are explicit in the envelope, while theorem-level source discharge remains outside the lab-local certificate row. |
| `theorem-2` | `StabCert` | `alignment_gap_delta_mse`, `whitening_deviation_epsilon` | Stability evidence is metric-backed and scoped to the Gaussian-OU toy runner. |
| `theorem-3` | `StabCert` | `theorem3_bound_mse`, `actual_recovery_mse`, `linear_identifiability_r2` | The existing LeJEPA backend points theorem3-bound-certificate at classifier_spec.cert_status; this ledger records the theorem-row boundary. |
| `theorem-4` | `Ledger` | `[]` | Ledger rows identify source and classifier residues that must stay visible until discharged by stronger evidence. |

- theorem DNA warning rows: `0`

## Not Implemented

- `theorem-1`: paper theorem statement is not represented as a kernel-checked formal target; source assumptions are recorded as payload fields rather than closed source reconstruction
- `theorem-2`: stability claim is represented by metric cells rather than a closed theorem certificate; optimizer and population-optimum assumptions are not discharged by the local runner
- `theorem-3`: bound projection is a certificate cell and not a theorem derivation; finite-sample and optimizer certificates remain ledger debt
- `theorem-4`: ledger row statuses are derived from local debt machinery rather than theorem closure; terminal verdict classification is outside the LeJEPA backend theorem row

## Hermite Degree Boundary

| label | behavioral boundary | theorem-bound pointer | scope | not claimed |
| --- | --- | --- | --- | --- |
| `degree1` | linear latent recovery boundary | `$.theorem_rows[2]` | `$.scope` | `$.not_claimed` |
| `degree2` | quadratic boundary | `$.theorem_rows[2]` | `$.scope` | `$.not_claimed` |
| `degree3+` | high-order boundary | `$.theorem_rows[3]` | `$.scope` | `$.not_claimed` |

## Hardgates

- `F-HG1`: `pass`
- `F-HG2`: `pass`
- `theorem_dna_warning`: `pass`
- `F-HG3`: `pass`
- `F-HG4`: `pass`
- `metric_resolvability`: `pass`
