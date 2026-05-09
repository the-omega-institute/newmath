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

### B-590 - Quadrature two-node sum equals sum of two weighted evaluations

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Quadrature two-node sum equals sum of two weighted evaluations |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |

Problem:
If a finite weighted QuadratureUp rule Q=(xs,α,ω,I_Q) over scalar carrier R has node spine xs enumerating exactly two positions i_0,i_1, then for every finite polynomial-code spine p, QSum_Q(p) ~_R ω_{i_0}·Eval(α_{i_0},R)(p) +_R ω_{i_1}·Eval(α_{i_1},R)(p).

Local inputs:
- `papers/bedc/parts/concrete_instances/205_quadrature_namecert_construction.tex`

Rationale:
Fills the gap between the empty-node case (thm:quadrature-empty-node-sum-zero, file:267, BOARD B-538) and the singleton-node case (thm:quadrature-singleton-node-sum-weighted-evaluation, file:313, BOARD B-575). grep for 'two-node|binary.*node|Quadrature.*pair|Quadrature.*two' in 205_quadrature_namecert_construction.tex returned 0 matches. Builds directly on def:quadrature-finite-weighted-exactness-degree (file:22), lem:quadrature-empty-position-fold-zero (file:255), and lem:quadrature-singleton-position-fold (file:294). Concrete identity, not a transport echo. File is at 347 lines, well under cap. Natural extension of the existing empty/singleton fold-shape pattern.

---
