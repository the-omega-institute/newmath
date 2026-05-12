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

### B-699 - KKT finite-packet standard bridge

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | KKT finite-packet standard bridge |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |

Problem:
If a standard KKT presentation is admitted solely through the finite primal, multiplier, residual, stationarity, feasibility, complementary-slackness, hsame, Cont, Pkg, NameCert, and dependency rows exported by KKTUp, then it roundtrips through the public KKTUp packet without adding Slater, differentiability, solver, or host minimization semantics.

Local inputs:
- `papers/bedc/parts/concrete_instances/273_kkt_namecert_construction.tex`

Rationale:
KKTUp already has row obligations, transport, complementarity exactness, downstream boundary, and public finite-packet export, while its closure block names the standard bridge as the next paper obligation. The proposed theorem is a bounded bridge target over the displayed finite packet, not a request for nonlinear optimization semantics, and it is not already covered by the public export theorem because it asks for the standard-presentation roundtrip boundary.

---

### B-700 - GeomQuantization public-surface standard bridge

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | GeomQuantization public-surface standard bridge |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
If a standard geometric-quantization presentation is read only through the SymplecticUp source row, HilbertUp endpoint row, prequantum line-bundle row, polarisation classifier, metaplectic ledger, finite Cont readback, hsame transport family, and Pkg provenance of the public packet, then it conservatively bridges to the GeomQuantizationUp public certificate and cannot expose an ambient quantization functor or host Hilbert construction.

Local inputs:
- `papers/bedc/parts/concrete_instances/248_geomquantization_namecert_construction.tex`

Rationale:
The GeomQuantizationUp chapter already proves the public certificate handoff but explicitly leaves standard bridges outside the current surface and names a schema-level public-surface bridge as the upgrade path. This candidate is a concrete conservative bridge theorem over the listed packet rows, distinct from the existing handoff because it constrains how a standard geometric-quantization presentation may be admitted without adding ambient quantization or host-space rows.

---
