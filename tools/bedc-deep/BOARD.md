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

### B-683 - Martingale finite suffix restriction carrier

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Martingale finite suffix restriction carrier |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 6/10 |

Problem:
If an accepted $\MartingaleUp$ adapted-sequence packet is restricted to a displayed suffix of its finite unary time spine while retaining the indexed $X$, $E$, $T$, $\rho$, and $\lambda$ rows and the same $\RandomVarUp$ and $\CondExpUp$ inputs, then the restricted tuple is again an accepted $\MartingaleUp$ adapted-sequence packet.

Local inputs:
- `papers/bedc/parts/concrete_instances/168_martingale_namecert_construction.tex`

Rationale:
The stochastic-process area has a prefix theorem for martingales but not the complementary suffix closure, while the adjacent MarkovChain chapter already has both prefix and suffix restriction targets. The Martingale packet is a finite tuple $(R,C,F,X,E,T,\rho,\lambda)$ accepted exactly when the displayed RandomVar, CondExp, filtration, tower, provenance, and ledger rows are present at papers/bedc/parts/concrete_instances/168_martingale_namecert_construction.tex:93-102. The existing finite-prefix restriction theorem appears at lines 345-385, and the closure story emphasizes finite packets and prefix restriction but excludes host stochastic-process data at lines 423-435. A finite-suffix restriction theorem would fill a specific missing half of the restriction schema without adding stopping-time or convergence theory.

---
