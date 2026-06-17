# STI Admission

- Generated at: `2026-06-17T20:11:14.194586+00:00`
- Verdict: `accepted`
- Base margin: `0.05`
- Control margin: `0.02`
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
| `metadata_only` | `pass` | `-0.02` |
| `label_shuffle` | `pass` | `-0.01` |
| `context_blind` | `pass` | `0.0` |
| `surface_permutation` | `pass` | `-0.02` |

## Not Claimed

- No shared base/chance admission protocol is introduced.
- No non-STI task producer is covered by this payload.
- No downstream report may bypass the STI downstream gate pointer.
- No public benchmark superiority claim is made.
