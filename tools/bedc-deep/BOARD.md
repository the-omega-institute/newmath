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

### B-690 - LocatedCauchy constant window degeneracy

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | LocatedCauchy constant window degeneracy |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 7/10 |
| Novelty | 7/10 |

Problem:
If a LocatedCauchyUp packet is the constant dyadic-stream carrier from the local carrier definition, then every requested precision window reads a located dyadic ball classified with the same degenerate dyadic endpoint under the displayed StreamNameUp, DyadicRatCoreUp, and CauchyModulusUp rows.

Local inputs:
- `papers/bedc/parts/concrete_instances/809_locatedcauchy_namecert_construction.tex`

Rationale:
The LocatedCauchyUp carrier is the finite packet L=(S,D,M,W,H,C,P,N), with schedule S, dyadic endpoint family D, Cauchy modulus M, located-ball witnesses W, transport H, and Cont readback routes C at papers/bedc/parts/concrete_instances/809_locatedcauchy_namecert_construction.tex:11-41. The definition says a constant dyadic stream inhabits the carrier by repeating one scheduled dyadic endpoint and using degenerate located balls at each requested window at lines 37-40, and the window-stability theorem only handles refined requested windows generally at lines 61-70. The NameCert theorem uses constant-stream habitation at lines 86-103 but does not isolate the per-window degenerate readback as a theorem. Focused rg for `locatedcauchy.*degenerate|locatedcauchy.*constant.*window|constant dyadic.*window` returned no LocatedCauchy theorem label; the only nonlocal hit was a LocatedReal proof sentence. This is a boundary exactness theorem about a concrete existing carrier, and the target file has 200 lines with 4 theorem-like blocks.

---
