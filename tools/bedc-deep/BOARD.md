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

### B-636 - SpinGroup conjugation action classifier congruence row

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | SpinGroup conjugation action classifier congruence row |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |

Problem:
If $S$ is an accepted SpinGroupUp packet and $s,s'$ are visible Clifford-unit endpoints of $S$ with $s\sim_{\CliffordUp}s'$, and $v,v'$ are Clifford-vector rows accepted by the same NameCert_CliffordUp source with $v\sim_{\CliffordUp}v'$, then $\mathsf{Act}_{s}(v)\sim_{\CliffordUp}\mathsf{Act}_{s'}(v')$ inside the same packet.

Local inputs:
- `papers/bedc/parts/concrete_instances/spingroup/boundary_consumer_exactness.tex`

Rationale:
File `concrete_instances/spingroup/boundary_consumer_exactness.tex` (327 lines) currently has a product law (line 78), an identity law (line 160), and an inverse-involution law (line 233) for the conjugation action `Act_s(v):=(s·v)·s^{-1}`. It has the *readback* theorem (line 27) but NO `congruence`/`stability` row showing the action is well-defined under classifier transport of either argument. A grep across `papers/bedc/parts/concrete_instances/spingroup/` for `(action.*congruence|spingroup-action-congru)` returned 0 hits. BOARD covers SpinGroup conjugation identity (B-612), inverse-involution (B-620), and multiplicative (B-600) laws — none of which is the bilinear/two-argument classifier-respect statement. The proof is short: the readback word `(s·v)·s^{-1}` is built from Clifford product rows and inverse rows; congruence follows from `\autoref{thm:clifford-product-stability-obligation}` applied twice plus inverse congruence from `def:group-stability-certificate`, no new ledger row needed.

---
