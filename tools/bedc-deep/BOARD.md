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

### B-644 - RootSystem simple reflection negates its own axis: s_α(α) ~_V -_V α

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | RootSystem simple reflection negates its own axis: s_α(α) ~_V -_V α |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 10/10 |

Problem:
For every carried root α of a RootSystemUp carrier, the simple reflection s_α applied to α equals the additive inverse: s_α(α) ~_V -_V α.

Local inputs:
- `papers/bedc/parts/concrete_instances/122_rootsystem_namecert_construction.tex`

Rationale:
First lemma a textbook proves after defining a root reflection (Humphreys, Reflection Groups §1.2; Bourbaki Lie IV-VI §1.1). The chapter already proves the involution s_α∘s_α~id but skips the basic axis-negation identity. Grep 'rootsystem-(reflection-axis|self-reflection)' returns no matches. Proof: specialize the reflection definition route s_α(γ)~γ - c_{α,γ}·α at γ=α, use Cartan integer c_{α,α}=2 from thm:rootsystem-cartan-ledger-obligation and innerproduct-root-diagonal-zero-exactness, and arithmetic in the VecSpaceUp reduct. All infra already in the same file.

---

