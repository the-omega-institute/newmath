# Formal Hardening

- Generated at: `2026-06-12T20:50:37.568652+00:00`
- Artifact: `bedc-quality-lab:formal-hardening`
- Status: `ready`
- Ready: `True`
- Coverage: `4/4`

## Verification ledger

| item | status | recorded | resolved | evidence | gap |
| --- | --- | --- | --- | --- | --- |
| `same-class-equivalence` | `verified` | `True` | `True` | `reports/canonical/spectral-ablation-hinge.json:$.ledger_summary.basis.hardening_coverage.items[0].recorded` | `` |
| `margin-stability` | `verified` | `True` | `True` | `reports/canonical/spectral-ablation-hinge.json:$.ledger_summary.basis.hardening_coverage.items[1].recorded` | `` |
| `finite-ledger-coverage` | `verified` | `True` | `True` | `lean://FiniteLedgerCoverage.coverage_of_recorded_witnesses` | `` |
| `missing-row-negative-example` | `verified` | `True` | `True` | `reports/canonical/spectral-ablation-hinge.json:$.ledger_summary.basis.hardening_coverage.items[3].recorded` | `` |

## Trust boundary

- pointer-only verification ledger; not a QualityEvidenceEnvelope and not a BEDC closure certificate
