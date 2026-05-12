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

### B-701 - ThetaFunction coefficient-prefix restriction carrier

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | ThetaFunction coefficient-prefix restriction carrier |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
If a ThetaFunctionUp packet has a finite q-expansion coefficient window and a displayed prefix window accepted by the same ComplexSeriesUp coefficient classifier, then replacing the window by that prefix while keeping the same period, holomorphic-chart, package, and continuation rows yields another accepted ThetaFunctionUp carrier source.

Local inputs:
- `papers/bedc/parts/concrete_instances/229_thetafunction_namecert_construction.tex`

Rationale:
ThetaFunctionUp has no matching completed state target in the scanned state files and remains only public-closed with no bridge at papers/bedc/parts/concrete_instances/229_thetafunction_namecert_construction.tex:139-154. The carrier source is explicitly a finite packet with period ledger, holomorphic local-function row, finite q-expansion coefficient window, package provenance, and continuation readbacks at papers/bedc/parts/concrete_instances/229_thetafunction_namecert_construction.tex:9-19. Ledger exactness says exactly those finite rows are exposed and no infinite coefficient object or completed modular form is exported at papers/bedc/parts/concrete_instances/229_thetafunction_namecert_construction.tex:58-82. The existing modular-shift theorem handles transport by period shift at papers/bedc/parts/concrete_instances/229_thetafunction_namecert_construction.tex:113-124, but the simpler finite-prefix restriction companion is absent and would exercise the finite-window side rather than another transport boundary.

---


### B-702 - Regulator rank-zero layout degeneracy

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Regulator rank-zero layout degeneracy |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 9/10 |

Problem:
If a RegulatorUp root input packet carries an empty unary rank witness, then its determinant-layout ledger is the empty finite layout over the DirichletUnitUp and NumFieldUp projections and the packet exports no analytic regulator value, host determinant evaluation, or host logarithm equality.

Local inputs:
- `papers/bedc/parts/concrete_instances/237_regulator_namecert_construction.tex`

Rationale:
RegulatorUp has no matching completed state target in the scanned state files and its chapter is arithmetic/K-theory flavored rather than the heavily explored algebraic append/transport core. The root packet stores DirichletUnitUp and NumFieldUp dependencies, visible unit rows, a unary rank witness, finite basis/logarithmic ledger, determinant-layout ledger, and package provenance at papers/bedc/parts/concrete_instances/237_regulator_namecert_construction.tex:9-24. It explicitly contains no analytic regulator value, host logarithm map, determinant evaluation, or bridge row at papers/bedc/parts/concrete_instances/237_regulator_namecert_construction.tex:26-31. Ledger exactness identifies the determinant/logarithm data as finite displayed ledger rows shaping the input matrix, not analytic values, at papers/bedc/parts/concrete_instances/237_regulator_namecert_construction.tex:90-117. A rank-zero layout theorem is a concrete boundary case that is not just restating the public threshold at papers/bedc/parts/concrete_instances/237_regulator_namecert_construction.tex:122-190.

---

