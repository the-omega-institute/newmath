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

### B-669 - StoneDuality consumer-facing export

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | StoneDuality consumer-facing export |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |

Problem:
If a StoneDualityUp packet satisfies the Boolean-algebra source transport, Stone-space clopen classifier, clopen ledger, ultrafilter-free soundness, and continuous-map readback rows, then every downstream consumer reads exactly the LatticeUp, TopologyUp, finite BHist, hsame, Cont, Pkg, and NameCert rows and no ultrafilter, point-space, completed compact-Hausdorff, or choice-based Stone-space construction.

Local inputs:
- `papers/bedc/parts/concrete_instances/239_stoneduality_namecert_construction.tex`

Rationale:
The candidate is a concrete implication over an existing concrete_instances chapter and lands directly on the chapter's stated public-closure boundary. It is not a marker-only or closurestatus task: it would be a theorem-level consumer export aggregating already displayed StoneDuality rows while preserving the explicit non-claims. Existing BOARD has a related StoneDuality bridge-surface target, but this candidate is narrower and different: it exports the ultrafilter-free finite-row consumer surface rather than adding a clopen-ultrafilter bridge. The input file is short and safe for a local theorem addition.

---


### B-670 - GoedelIncompleteness public consumer certificate

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | GoedelIncompleteness public consumer certificate |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
If a GoedelIncompletenessUp witness satisfies the proof-checker obligation, fixed-point obligation, and conditional undecidable-row obligation over the displayed FirstOrderUp, ModelTheoryUp, ComputableUp, NatUp, and hsame surfaces, then it exports a public NameCert_GoedelIncompletenessUp theorem consumable by those users and exports no second-incompleteness theorem, omega-consistency, semantic completeness, Lob conditions, or set-theoretic foundations bridge.

Local inputs:
- `papers/bedc/parts/concrete_instances/268_goedelincompleteness_namecert_construction.tex`

Rationale:
The candidate is a bounded public certificate theorem for an existing concrete_instances chapter, expressed as a single implication from the three displayed obligation rows to the exported consumer surface. It is distinct from the existing proof-checker, fixed-point, and undecidable-row obligations already present in the paper because it asks for the aggregate NameCert-facing export and explicit consumer boundary. No existing BOARD title closely matches GoedelIncompleteness, and the landing file is short enough for a local theorem block without line-cap risk.

---

