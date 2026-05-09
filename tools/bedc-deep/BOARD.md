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

### B-592 - PolynomialUp raw multiplication left identity by singleton-1 polynomial

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | PolynomialUp raw multiplication left identity by singleton-1 polynomial |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 7/10 |

Problem:
If R carries a RingUp(R) certificate with multiplicative unit 1_R and additive zero 0_R, and p:ListCarrier(R) is any finite coefficient spine, then PolySame_R(rmul_R(cons(1_R, nil), p), p).

Local inputs:
- `papers/bedc/parts/concrete_instances/25_polynomial_literal_multiplication.tex`
- `papers/bedc/parts/concrete_instances/25_polynomial_literal_addtrim_algebra.tex`
- `papers/bedc/parts/concrete_instances/25_polynomial_literal_addtrim_eval.tex`
- `papers/bedc/parts/concrete_instances/26_fps_ringup_tail.tex`

Rationale:
PolynomialUp file 25_polynomial_literal_multiplication.tex (182 lines, well under cap) currently proves polynomial raw multiplication associativity (thm:polynomial-multiplication-associativity-commring-scalars), commutativity (thm:polynomial-raw-multiplication-commutativity-from-commring-scalars in 25_polynomial_literal_addtrim_algebra.tex), left/right zero absorption (thm:polynomial-multiplication-left-zero-absorption, thm:polynomial-multiplication-right-zero-absorption), and left/right distributivity (B-579, B-587 already completed). The fifth basic ring-multiplication law — that the singleton-1 polynomial cons(1_R, nil) is a multiplicative left identity — is conspicuously absent: grep for 'polynomial.*identity\|polynomial.*one\|raw.mul.*one\|raw.mul.*unit\|PolyOne\|PolyUnit' across papers/bedc/parts/ returns zero hits, and grep across lean4/BEDC/Derived/PolynomialUp/CauchyProduct.lean returns _zero, _commutative, _associative theorems but no _left_unit / _right_unit / _one. The exact analogue for FormalPowerSeriesUp is fully proven as thm:fps-cauchy-product-unit-laws (papers/bedc/parts/concrete_instances/26_fps_ringup_tail.tex line 56) with Lean target FpsSingletonCauchyProduct_unit_laws. The polynomial proof reuses lem:raw-cauchy-product-coefficient-formula and the additive-zero / multiplicative-left-unit rows already retained in def:ring-stability-certificate; structurally identical to the FPS unit-law argument but on finite ListCarrier instead of Nat → R.

---


### B-593 - PolynomialUp raw multiplication right identity by singleton-1 polynomial

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | PolynomialUp raw multiplication right identity by singleton-1 polynomial |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 6/10 |

Problem:
If R carries a RingUp(R) certificate with multiplicative unit 1_R and additive zero 0_R, and p:ListCarrier(R) is any finite coefficient spine, then PolySame_R(rmul_R(p, cons(1_R, nil)), p).

Local inputs:
- `papers/bedc/parts/concrete_instances/25_polynomial_literal_multiplication.tex`
- `papers/bedc/parts/concrete_instances/25_polynomial_literal_addtrim_algebra.tex`
- `papers/bedc/parts/concrete_instances/26_fps_ringup_tail.tex`

Rationale:
Symmetric counterpart to the left-identity candidate above. Same evidence: no polynomial-multiplication-right-identity / right-unit theorem appears in the labels of 25_polynomial_literal_multiplication.tex or in PolynomialUp/CauchyProduct.lean. Note that thm:polynomial-raw-multiplication-commutativity-from-commring-scalars only triggers under CommRingUp; for general RingUp scalars the right-identity is an independent theorem requiring direct proof on the right-side Cauchy fold (mirroring the right-unit half of thm:fps-cauchy-product-unit-laws). Local proof inputs include: lem:raw-cauchy-product-coefficient-formula (raw product coefficient = Cauchy fold), the multiplicative right-unit row from def:ring-stability-certificate, the right-zero-absorption row, and lem:padded-coefficient-extensionality-polynomial-classifier (to lift coefficient-wise classifier comparisons to PolySame_R).

---

