# BEDC Deep Reasoning Board

Purpose: drive a self-iterating BEDC paper-extension loop. Each entry below is
a target the oracle deep-reasoning loop runs to a complete result, then
appends as canonical current-state LaTeX into `papers/bedc/parts/`. The
downstream `lean4/scripts/codex_formalize.py` lane (on dev) picks up new
theorem sites by scanning the paper.

Lane edge:
- This lane never edits `lean4/`. The handshake to formalization is the
  appended LaTeX in `papers/bedc/parts/<theme>/<concept>.tex` (no marker
  macros — those are added by `codex_formalize.py` after the Lean target lands).
- New targets are auto-spawned by Stage 1.5 topic discovery and appended to
  this board with `Status: Candidate (auto-spawned)`.

Each target card carries enough context (Object, Local inputs) for the loop
to build its initial prompt without external lookups.

---

### B-551 - Pullback ledger composition associativity at the gap-policy level

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Pullback ledger composition associativity at the gap-policy level |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
If τ1:D'→D, τ2:D''→D', τ3:D'''→D'' each carry a classifier-preserving pullback ledger over Π and GapPol(Π,D) holds, then the composite pulled-back gap predicates obtained by ((τ1∘τ2)∘τ3) and (τ1∘(τ2∘τ3)) are logically equivalent on every D'''-source/token pair.

Local inputs:
- `papers/bedc/parts/proof_obligations/gap_policy.tex`

Rationale:
papers/bedc/parts/proof_obligations/gap_policy.tex defines the classifier-preserving pullback ledger at line 109 and proves the n-fold composite case `thm:composite-pullback-gap-policy-preserves-coverage-and-separation` at line 197 (B-504) plus the identity unit law `thm:identity-pullback-gap-policy-unit-law` at line 269 (B-550). Associativity of pullback composition is the missing third law that closes the categorical structure (identity + composition + associativity), and is not implied by either existing theorem since each one only fixes a single composition order. Grep `pullback.*associat|pulled-back.*associat|composite-pullback.*associat` across papers/bedc/parts/ returns zero matches. The file is 324 lines, well under the 760-line cap, with the existing pullback section ending at line 324 — clean append point. The proof is a chain unfolding of `def:classifier-preserving-pullback-ledger` clause (ii) twice on each side and reducing to the underlying composition equality τ1(τ2(τ3 h''')) = (τ1∘(τ2∘τ3))(h''') = ((τ1∘τ2)∘τ3)(h'''), then folding back.

---

