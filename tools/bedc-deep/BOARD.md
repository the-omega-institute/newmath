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

### B-583 - CliffordUp polarization identity uv + vu ~ q(u+v) - q(u) - q(v)

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | CliffordUp polarization identity uv + vu ~ q(u+v) - q(u) - q(v) |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 9/10 |

Problem:
For accepted vector histories u,v in the shared VecSpaceUp source, the Clifford classifier identifies u*v + v*u with q(u+v) - q(u) - q(v) via the displayed quadratic-relation row applied to u+v together with bilinearity transport from BilinFormUp.

Local inputs:
- `papers/bedc/parts/concrete_instances/125_clifford_namecert_construction.tex`

Rationale:
125_clifford has the diagonal quadratic-relation v*v ~ q(v)*1 and product-stability/confluence rows, but the universal symmetric polarization formula relating two distinct vectors is not derived. Polarization is the unique fact that distinguishes Clifford from a free tensor algebra and what downstream Spin/Pin certificates need to anchor double-cover constructions. Polarization shows up only in commring/innerproduct chapters elsewhere, never in Clifford. Frontier algebra capstone.

---
