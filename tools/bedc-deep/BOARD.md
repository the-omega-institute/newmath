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

### B-579 - Polynomial raw multiplication right distributivity over raw addition

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Polynomial raw multiplication right distributivity over raw addition |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
If R carries a RingUp certificate with classifier ~_R and operations radd_R, rmul_R as in def:polynomial-raw-cauchy-product, then for every finite coefficient spines p, q, r, PolySame_R(rmul_R(p, radd_R(q, r)), radd_R(rmul_R(p, q), rmul_R(p, r))).

Local inputs:
- `papers/bedc/parts/concrete_instances/25_polynomial_literal_multiplication.tex`
- `papers/bedc/parts/concrete_instances/25_polynomial_literal_addtrim_eval.tex`

Rationale:
Same host file as candidate #1 (103 lines). Searched grep 'distrib' across papers/bedc/parts/concrete_instances/25_polynomial*.tex returned 0 hits for raw multiplication distributivity over addition — only the singleton-collapse-level distributivity at 25_polynomial_namecert_construction.tex L349 (thm:polynomial-singleton-append-distrib-classified) and the FPS sibling 26_fps_namecert_construction.tex L546 (thm:fps-cauchy-product-distributes-over-fps-addition) exist. So distributivity is proven for FPS Cauchy product but not for finite-spine polynomial Cauchy product. Proof: Cauchy formula gives rmul(p, radd(q,r))[n] ~ Σ p[i]·radd(q,r)[j] = Σ p[i]·(q[j]+r[j]) ~ Σ (p[i]·q[j] + p[i]·r[j]) by ring left-distributivity in def:ring-stability-certificate, splits via finite-additive-fold-congruence into Cauchy(p,q;n) + Cauchy(p,r;n) ~ rmul(p,q)[n] + rmul(p,r)[n], then padded extensionality gives PolySame.

---
