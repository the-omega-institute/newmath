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

### B-558 - Max-flow value lifts to a primal LP optimum bridge between NetworkFlow and LPDuality

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | Max-flow value lifts to a primal LP optimum bridge between NetworkFlow and LPDuality |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
For a NetworkFlowUp carrier G with capacity u, feasible flow F, and residual-cut exhaustion certificate Xi, the flow-value endpoint V_F and cut-capacity endpoint K_Xi assemble a primal-dual LPDualityUp feasible pair over the carrier's unary scalar field whose strong-duality classifier returns the same hsame endpoint.

Local inputs:
- `papers/bedc/parts/concrete_instances/211_networkflow_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/213_lpduality_namecert_construction.tex`

Rationale:
This is a genuine bridge target between two existing concrete_instances chapters that the project_governance roadmap pairs but never wires up: 211_networkflow already proves V_F hsame K_Xi via residual-cut exhaustion (B-463, B-554) and 213_lpduality already provides strong-duality classifier data over abstract ordered fields (B-516/B-519/B-525/B-540/B-549). What is missing is the assembly map: certificate-grade max-flow data → primal-dual LP feasible pair with classifier coincidence. None of the existing BOARD entries do this; B-554 is single-side optimality only, the LPDuality entries are face/feasibility transports on the LP side alone, and B-447/B-444/B-429 stay inside the LP carrier. The candidate also flags the right landing-safety move: 211_networkflow is near cap, so this lands in a new sibling 211_networkflow_lpduality_bridge.tex rather than mutating either existing file. Concrete implication form, in BEDC scope, no paper duplicate.

---
