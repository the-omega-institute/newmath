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

### B-594 - Lattice one-sided distributive inequality (universal modular bound)

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Lattice one-sided distributive inequality (universal modular bound) |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 7/10 |

Problem:
For carried lattice elements $x,y,z$ in a $\LatticeUp$ certificate, the meet-over-join admits the universal one-sided bound $(x\wedge y)\vee(x\wedge z)\preceq x\wedge(y\vee z)$ in the underlying poset order.

Local inputs:
- `papers/bedc/parts/concrete_instances/lattice/the_certificate.tex`

Rationale:
Birkhoff Lattice Theory Ch. I §6: the universal one-sided modular inequality holds in every lattice (without distributivity). The chapter has meet/join idempotence (`lem:lattice-meet-idempotence-from-bounds` line 44, `lem:lattice-join-idempotence-from-bounds` line 71), absorption (lines 98, 133), commutativity (`thm:lattice-commutativity-from-directional-bounds` line 194), and bound-uniqueness (line 378). Verified no `thm:lattice-distrib*|modular*|inequal*` exists in the_certificate.tex. The proof reuses meet-monotonicity in each argument (deducible from the bound characterization) plus join's least-upper-bound property — both already explicit. File is 656 lines (under cap). 1-2 codex rounds.

---

