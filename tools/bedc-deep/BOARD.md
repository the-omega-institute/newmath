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


### B-684 - Ergodic invariant subledger restriction stays carried

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Ergodic invariant subledger restriction stays carried |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 7/10 |
| Novelty | 8/10 |

Problem:
If an accepted $\ErgodicUp$ measure-preserving carrier is restricted to a displayed finite subledger of its invariant-subspace rows while retaining the same $\DynSystemUp$ transformation row, $\MeasureUp$ measure row, $\hsame$ transports, $\Cont$ routes, and $\Pkg$ provenance, then the restricted packet remains an accepted $\ErgodicUp$ measure-preserving carrier.

Local inputs:
- `papers/bedc/parts/concrete_instances/174_ergodic_namecert_construction.tex`

Rationale:
ErgodicUp is unusually sparse compared with nearby probability chapters: it has only two definitions and three theorem blocks, all focused on classifier/decomposition surface rather than closure under finite subledgers. The source surface is a finite package of DynSystem rows, Measure rows, invariant-subspace classifier rows, $\hsame$ transport, finite $\Cont$ routes, and $\Pkg$ provenance at papers/bedc/parts/concrete_instances/174_ergodic_namecert_construction.tex:9-17; the measure-preserving carrier is an accepted instance of that finite source at lines 19-27. The decomposition ledger theorem says every witness is exhausted by those invariant rows and imports no host sigma-algebra quotient at lines 58-80. A subledger restriction theorem would give the chapter a concrete finite-structure closure result rather than another boundary projection.

---

