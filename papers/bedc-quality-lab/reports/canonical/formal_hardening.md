# Formal Hardening

- Generated at: `2026-06-03T13:46:08.765921+00:00`
- Artifact: `bedc-quality-lab:formal-hardening`
- Status: `not-ready`
- Ready: `False`
- Coverage: `3/4`

## Verification ledger

| item | status | recorded | evidence | gap |
| --- | --- | --- | --- | --- |
| `same-class-equivalence` | `verified` | `True` | `reports/canonical/spectral-ablation-hinge.json:$.ledger_summary.basis.hardening_coverage.items[0].recorded` | `` |
| `margin-stability` | `verified` | `True` | `reports/canonical/spectral-ablation-hinge.json:$.ledger_summary.basis.hardening_coverage.items[1].recorded` | `` |
| `finite-ledger-coverage` | `missing` | `False` | `` | `delete-1 has no recorded finite ledger coverage evidence` |
| `missing-row-negative-example` | `verified` | `True` | `reports/canonical/spectral-ablation-hinge.json:$.ledger_summary.basis.hardening_coverage.items[3].recorded` | `` |

## Trust boundary

- pointer-only verification ledger; not a QualityEvidenceEnvelope and not a BEDC closure certificate
