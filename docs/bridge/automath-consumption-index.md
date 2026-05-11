# Automath Consumption Index

This index is a lightweight NewMath receiving surface for Automath evidence.
It records gate-passed bridge evidence and synthesis-only review leads without creating BEDC paper or Lean
content directly. BEDC-native writing remains owned by the BEDC board and
supervisor pipelines.

Input source: `gate`.

## Current Review Inputs

| Source | Kind | Readiness | Priority | Input | NewMath action |
| --- | --- | --- | ---: | --- | --- |
| `the-omega-institute/automath@origin/dev:lean4/Omega/CircleDimension/KilloGodelCompressionNotFiniteRankHomologizable.lean` | `lean_theorem` | `needs_operator_review` | low | `gate` | review as a NewMath research-object input; do not auto-promote synthesis-only rows |
| `the-omega-institute/automath@origin/dev:lean4/Omega/CircleDimension/KilloGrothendieckCompletionPreservesInjection.lean` | `lean_theorem` | `needs_operator_review` | low | `gate` | review as a NewMath research-object input; do not auto-promote synthesis-only rows |
| `the-omega-institute/automath@origin/dev:lean4/Omega/CircleDimension/KilloS4BurnsideKaniRosenPrymSquare.lean` | `lean_theorem` | `needs_operator_review` | low | `gate` | review as a NewMath research-object input; do not auto-promote synthesis-only rows |
| `the-omega-institute/automath@origin/dev:lean4/scripts/codex_formalize.py` | `pipeline_status` | `needs_operator_review` | low | `gate` | review as a NewMath research-object input; do not auto-promote synthesis-only rows |
| `the-omega-institute/automath@origin/dev:lean4/scripts/omega_ci.py` | `pipeline_status` | `needs_operator_review` | low | `gate` | review as a NewMath research-object input; do not auto-promote synthesis-only rows |
| `the-omega-institute/automath@origin/dev:papers/publication/2026_cayley_chebyshev_poisson_entropy_strip_rkhs_jfa/sec_appendix.tex` | `paper_claim` | `needs_operator_review` | low | `gate` | review as a NewMath research-object input; do not auto-promote synthesis-only rows |
| `the-omega-institute/automath@origin/dev:papers/publication/2026_cayley_chebyshev_poisson_entropy_strip_rkhs_jfa/sec_cayley_gate.tex` | `paper_claim` | `needs_operator_review` | low | `gate` | review as a NewMath research-object input; do not auto-promote synthesis-only rows |
| `the-omega-institute/automath@origin/dev:papers/publication/2026_cayley_chebyshev_poisson_entropy_strip_rkhs_jfa/sec_doob_phi_entropy.tex` | `paper_claim` | `needs_operator_review` | low | `gate` | review as a NewMath research-object input; do not auto-promote synthesis-only rows |
| `the-omega-institute/automath@origin/dev:tools/chatgpt-oracle/oracle_pipeline.py` | `pipeline_status` | `needs_operator_review` | low | `gate` | review as a NewMath research-object input; do not auto-promote synthesis-only rows |

## Policy

- Only records with `gate_status=gate_passed` may be consumed by BEDC board adapters.
- `Input source: synthesis` means review-only evidence, not a deterministic gate pass.
- `ready_for_local_packet` means the source may be summarized for review.
- This index does not mark a bridge record accepted or consumed.
- Automath paper content must pass the Automath Killo/golden writeback lane before it becomes durable Automath text.
- NewMath paper and Lean writes remain behind BEDC board, TasteGate, and audit gates.
- Bridge candidates must not be appended to `tools/bedc-deep/BOARD.completed.md`; completed archive entries require BEDC completion semantics.
