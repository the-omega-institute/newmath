# STI Admission

- Generated at: `2026-06-18T15:15:12.952427+00:00`
- Verdict: `accepted`
- Base margin: `0.05`
- Control margin: `0.02`
- Base/chance gate: `base_acc_L95 > empirical_chance_U95 + base_margin`
- Control gate: `max_control_score <= empirical_chance_U95 + control_margin`
- Downstream gate: `reports/canonical/sti-admission.json:$.downstream_gate`

## Hardgates

| gate | status | evidence |
| --- | --- | --- |
| `BASE-CHANCE` | `pass` | `$.base_chance_gate` |
| `CONTROL` | `pass` | `$.controls` |
| `PAYLOAD` | `pass` | `$` |

## Controls

| control | status | max delta over chance |
| --- | --- | --- |
| `metadata_only` | `pass` | `-0.03` |
| `no_support` | `pass` | `-0.02` |
| `query_only` | `pass` | `-0.01` |
| `shuffled_support` | `pass` | `-0.03` |

## Not Claimed

- No shared base/chance admission protocol is introduced.
- No non-STI task producer is covered by this payload.
- No downstream report may bypass the STI downstream gate pointer.
- No public benchmark superiority claim is made.
