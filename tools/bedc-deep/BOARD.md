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

### B-556 - ModN singleton element plus negation classifies with the empty endpoint

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | ModN singleton element plus negation classifies with the empty endpoint |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 9/10 |

Problem:
For each unary modulus history $m:\mathsf{BHist}$, if $\mathsf{ModNCarrier}_m(h)$, then $\mathsf{ModNClassifier}_m(\mathsf{RingSingletonAdd}(h, \mathsf{RingSingletonNeg}(h)), \emp)$ — i.e. an element added to its singleton additive inverse classifies with the empty (zero) representative under the concrete ModN classifier.

Local inputs:
- `papers/bedc/parts/concrete_instances/80_modn_namecert_construction.tex`

Rationale:
ModN (80_, 199 lines) is a one-completion theme (only the bare quotient-presentation construction). The chapter establishes the concrete ModN singleton carrier/classifier (line 57-75), the classifier rows (line 77-112), and the singleton operation descent rows (line 114-159) including `RingSingletonNeg` closure and congruence — but never composes additive descent with negation descent to assert the canonical $h+(-h)\equiv 0$ row, which is the defining computational property of any modular-arithmetic interface. Single-implication, narrow (singleton scope), and tests both descent rows simultaneously. Critical structural gap: ModN closes scoped without ever stating an arithmetic identity beyond classifier reflexivity.

---


### B-557 - Preorder terminal endpoint-order opposite is the same relation

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Preorder terminal endpoint-order opposite is the same relation |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 9/10 |

Problem:
For the terminal endpoint-order surface $(A_{\emp}, \rho_{\emp}, \preceq_{\emp})$ of \autoref{def:preorder-terminal-endpoint-order-surface}, define $\preceq_{\emp}^{\mathrm{op}}(h, k) := \preceq_{\emp}(k, h)$. Then $h \preceq_{\emp}^{\mathrm{op}} k \Longleftrightarrow A_{\emp}(h) \land A_{\emp}(k)$, hence $h \preceq_{\emp}^{\mathrm{op}} k \Longleftrightarrow h \preceq_{\emp} k$ — the terminal endpoint-order surface is its own opposite.

Local inputs:
- `papers/bedc/parts/concrete_instances/27_preorder_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/preorder/terminal_endpoint_order_surface.tex`

Rationale:
Preorder (27_, 772 lines, near cap) has only the existing `preorder/terminal_endpoint_order_surface.tex` (85 lines) and `preorder/closure_status.tex` (9 lines) child files. The hub establishes the abstract preorder opposite construction (line 700-719) and the terminal endpoint-order surface (line 721-769); no theorem instantiates the opposite construction on the terminal endpoint-order surface. Single-implication, follows from the surface's symmetric definition $\preceq_{\emp}(h,k) \Leftrightarrow A_{\emp}(h) \land A_{\emp}(k)$ being unchanged under endpoint swap. Should be added as a new sibling file `preorder/opposite_terminal_endpoint_order.tex` rather than appending to the near-cap hub. Fills the 'op-instance' gap that demonstrates the opposite construction is well-defined on the closed surface.

---

