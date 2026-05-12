# Automath BOARD Continuation Ledger

This durable ledger records Automath-to-NewMath bridge candidates that were shaped as evidence-backed BEDC continuation targets.
Runtime inbox, state, logs, and raw gate output remain untracked.

| Metric | Value |
| --- | --- |
| Apply | `True` |
| Eligible candidates | `3` |
| Accepted into BOARD | `0` |
| Rejected | `3` |
| Appended ids | `none` |
| Judge backend | `codex_fallback` |

## Candidate Modes

| Title | Mode | Source commit | Source paths | Evidence packet | Expected NewMath delta |
| --- | --- | --- | --- | --- | --- |
| `Cayley weighted integral normalization bridge evidence` | `board_continuation` | `aecb76a5a5eed83cc6bdbb981b51ebfb58dd695f` | `papers/publication/2026_cayley_chebyshev_poisson_entropy_strip_rkhs_jfa/sec_appendix.tex` | `tools\automath_newmath_bridge\review_packets\papers-publication-2026-cayley-chebyshev-poisson-entropy-strip-rkhs-jfa-sec-appendix-tex-98a1027e8c35.json` | minimal BEDC wrapper, native restatement, obstruction, or audit/planning task that cites the Automath evidence packet |
| `Cayley boundary chart bridge wrapper` | `board_continuation` | `aecb76a5a5eed83cc6bdbb981b51ebfb58dd695f` | `papers/publication/2026_cayley_chebyshev_poisson_entropy_strip_rkhs_jfa/sec_cayley_gate.tex` | `tools\automath_newmath_bridge\review_packets\papers-publication-2026-cayley-chebyshev-poisson-entropy-strip-rkhs-jfa-sec-cayley-gate-tex-ce39cd0cc9a6.json` | minimal BEDC wrapper, native restatement, obstruction, or audit/planning task that cites the Automath evidence packet |
| `Doob Phi-entropy dissipation bridge obligation` | `board_continuation` | `aecb76a5a5eed83cc6bdbb981b51ebfb58dd695f` | `papers/publication/2026_cayley_chebyshev_poisson_entropy_strip_rkhs_jfa/sec_doob_phi_entropy.tex` | `tools\automath_newmath_bridge\review_packets\papers-publication-2026-cayley-chebyshev-poisson-entropy-strip-rkhs-jfa-sec-doob-phi-entropy-tex-218a5391e43c.json` | minimal BEDC wrapper, native restatement, obstruction, or audit/planning task that cites the Automath evidence packet |

## Policy

- `evidence_only` records are reference material; they should not create BEDC theorem work automatically.
- `board_continuation` records enter BOARD only as continuation targets with Automath evidence packets.
- `proposal_seed_candidate` records may seed a BEDC-native proposal, but still go through native intake gates.
- BEDC workers should inspect the Automath evidence first and write only the minimal BEDC-native wrapper, proposal, audit task, or rejection reason.
- Machine-readable ACK/NACK status is appended to `docs\bridge\automath-newmath-ack.jsonl`.
