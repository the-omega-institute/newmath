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

### B-588 - HomotopyUp reversal involution: reverse-of-reverse classifies original packet

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | HomotopyUp reversal involution: reverse-of-reverse classifies original packet |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
For a HomotopyUp source packet H from f to g of def:homotopy-bhist-source-packet, applying the reversal-symmetry construction of thm:homotopy-reversal-symmetry-row twice produces a packet whose deformation row, interval-parameter row, endpoint ContinuousMap rows, and finite Cont ledger are componentwise hsame to those of H under the same Pkg provenance.

Local inputs:
- `papers/bedc/parts/concrete_instances/134_homotopy_namecert_construction.tex`

Rationale:
134_homotopy (363 lines) carries reflexivity (thm:homotopy-constant-deformation-reflexivity-row), single reversal (thm:homotopy-reversal-symmetry-row), composition (thm:homotopy-deformation-composition-row), associativity (thm:homotopy-composition-associativity-row), and transitivity (thm:homotopy-endpoint-composition-transitivity-row), but never states the involution `reverse∘reverse ~ id`. This is the canonical missing algebraic identity for the reversal operation — directly parallel to B-582 (RootSystem reflection involution s_α∘s_α ~ β) which BOARD just landed in the same week. Single-implication: reverse twice and project the deformation row through the interval-classifier transport recorded in λ. No hub append (134 is a body file) and well below the 800-line cap.

---


### B-589 - DynSystemUp fixed-point flow stability: hsame-fixed phase point has hsame-fixed orbit iterates

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | DynSystemUp fixed-point flow stability: hsame-fixed phase point has hsame-fixed orbit iterates |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 9/10 |

Problem:
For an accepted DynSystemUp packet of def:dynsystem-carried-source-row (cited via thm:dynsystem-orbit-iterate-carrier-closure), if the displayed phase-point row p is hsame to its image under a single time-step flow row F_t (hsame(F_t(p), p)), then the n-fold iterate row F_{nt}(p) is hsame to p for every finite n in the displayed UnaryHistory horizon, with the iterate Cont ledger collapsing to repeated copies of the supplied invariance row.

Local inputs:
- `papers/bedc/parts/concrete_instances/173_dynsystem_namecert_construction.tex`

Rationale:
173_dynsystem (503 lines) carries flow surface, identity flow, composition flow, ODE generator ledger, orbit-iterate carrier closure (thm:dynsystem-orbit-iterate-carrier-closure), invariant consumer projection, time-reindex stability, endpoint determinacy, but has zero fixed-point/equilibrium/periodic-orbit instance — grep on 'fixed.point|equilibrium|periodic|stationary' returns no theorem. Fixed points are the canonical first invariant of any dynamical system and the natural single-row instance to anchor downstream invariant-measure / ergodic targets. Mirrors B-585 (singleton-equation zero-locus exactness): a single supplied row plus orbit-iterate closure gives the iterate by induction over the displayed unary horizon.

---

