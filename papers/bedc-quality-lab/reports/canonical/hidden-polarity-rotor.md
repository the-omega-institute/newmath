# Hidden-Polarity Rotor

- Generated at: `2026-06-20T00:00:00+00:00`
- Verdict: `diagnostic_only`
- Dependency status: `downgraded`
- Identifiability gate: `effect_lower_ci - chance_upper_ci >= identifiability_margin`
- Control gate: `each control upper_ci <= chance_upper_ci + control_margin`
- Claim boundary: `reports/canonical/hidden-polarity-rotor.json:$.claim_boundary`

## Hardgates

| gate | status | evidence |
| --- | --- | --- |
| `FIXTURE` | `pass` | `$.diagnostic_fixture` |
| `MEASURED-RESULT` | `not_evaluated` | `$.measured_result_intake` |
| `IDENTIFIABILITY` | `not_evaluated` | `$.evidence_gate` |
| `CONTROL` | `not_evaluated` | `$.controls` |
| `PAYLOAD` | `pass` | `$` |

## Controls

| control | status | max delta over chance |
| --- | --- | --- |
| `phase_shuffle` | `not_evaluated` | `None` |
| `polarity_swap` | `not_evaluated` | `None` |
| `rotor_blind` | `not_evaluated` | `None` |

## Claim Boundary

- Status: `diagnostic`
- Claim kind: `None`
- Boundary: No bounded physical identifiability claim is opened by this artifact.

## Not Claimed

- No claim is made from issue comments, task prose, controller logs, or temporary scripts.
- No shared HPR admission framework is introduced.
- No GPU, MuJoCo, torch, or external simulator dependency is required for the default artifact.
- No downstream report may treat diagnostic_only as a positive physical identifiability claim.
