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

### B-544 - JonesPolynomial skein ledger obligation surface

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | JonesPolynomial skein ledger obligation surface |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
If a JonesPolynomialUp packet supplies a KnotUp diagram row, three skein-related KnotUp boundary rows, a PolynomialUp Laurent-polynomial endpoint, and a finite skein ledger compatible with Reidemeister transport, then it exposes an accepted JonesPolynomial carrier/classifier surface over those rows.

Local inputs:
- `papers/bedc/parts/concrete_instances/233_jonespolynomial_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/232_knot_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/25_polynomial_namecert_construction.tex`

Rationale:
This lands in the empty JonesPolynomialUp certificate chapter as the first conservative skein-ledger obligation, not as a proof of the full Jones polynomial invariant. KnotUp already has Reidemeister ledger composition and classifier completeness, and PolynomialUp supplies the polynomial-side carrier surface, so the proposed theorem is a bounded bridge/coverage target over supplied rows. No existing BOARD title or paper label covers the JonesPolynomial skein surface, and the short JonesPolynomial landing file avoids hub-only and line-cap risks.

---

### B-547 - AtiyahSinger index-pairing carrier surface

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | AtiyahSinger index-pairing carrier surface |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
If an AtiyahSingerUp packet supplies a SpectralTheoremUp analytic-index row and a ChernWeilUp topological characteristic-class row over the same closed-manifold endpoint, then it exposes an index-pairing classifier row whose equality obligation is scoped exactly to those two dependency surfaces.

Local inputs:
- `papers/bedc/parts/concrete_instances/251_atiyahsinger_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/192_spectraltheorem_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/250_chernweil_namecert_construction.tex`

Rationale:
The target is the first AtiyahSingerUp carrier/classifier obligation surface, not the full Atiyah-Singer theorem. SpectralTheoremUp already has public spectral-data certificate rows and ChernWeilUp has characteristic-class exactness rows, so the proposed bridge can be stated as a scoped index-pairing surface over existing dependency rows. It is distinct from all BOARD titles and paper labels, and the short AtiyahSingerUp chapter is a safe landing file.

---

### B-548 - CurryHoward cut-beta bridge obligation

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | CurryHoward cut-beta bridge obligation |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 7/10 |
| Novelty | 7/10 |

Problem:
If a CurryHowardUp packet pairs a FirstOrderUp deduction ledger with a LambdaCalcUp term packet through a shared proof-program carrier, then a displayed cut-elimination step on the deduction side is carried to a beta-reduction/substitution ledger on the LambdaCalc side under the shared classifier.

Local inputs:
- `papers/bedc/parts/concrete_instances/243_curryhoward_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/175_firstorder_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/178_lambdacalc_namecert_construction.tex`

Rationale:
This is a concrete bridge obligation between the existing FirstOrderUp deduction-ledger surface and the LambdaCalcUp beta/substitution ledger surface, not the broad capstone observation that Curry-Howard is built into closure laws. The concrete CurryHowardUp chapter is empty, the relevant dependency theorems are already present, and no BOARD entry or paper label states this cut-to-beta bridge. The short CurryHowardUp file is a safe landing point for the bounded theorem.

---
