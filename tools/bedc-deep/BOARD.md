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

### B-655 - Gap hsame transport gives a psame representative

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | Gap hsame transport gives a psame representative |
| Layer | proof_obligations |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |

Problem:
Under DomainPolicy(D), BundleAskPolicy(Π,D), PackageTokenPolicy(Π) and token totality, InGapsig(Π,D,p,h) and hsame(h,k) imply existence of q with InGapsig(Π,D,q,k) and psame(p,q).

Local inputs:
- `papers/bedc/parts/proof_obligations/domain_policy.tex`
- `papers/bedc/parts/proof_obligations/gap_policy.tex`
- `papers/bedc/parts/concrete_hardening/internalized_gap_globalize.tex`

Rationale:
This is a concrete coverage-with-soundness transport bridge that the current proof_obligations surface does not state. Existing pieces handle either same-source gap separation (B-646 strengthens separation from AskPol to BundleAskPolicy) or DomainPolicy hsame transport in isolation; neither combines them into the statement that an hsame move on the source endpoint preserves gap membership up to a psame-compatible representative. The claim is in single-implication form, fits cleanly under proof_obligations alongside the existing internalized-gap and gap-policy material, and gives a usable lemma for downstream bundle/package proofs rather than echoing an abstract carrier equivalence.

---


### B-656 - Three points are minimal for noncommutative Add obstruction

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | Three points are minimal for noncommutative Add obstruction |
| Layer | proof_obligations |
| Route | proof |
| Risk | unknown |
| Fit | 7/10 |
| Novelty | 7/10 |

Problem:
Under finite equality-classified total deterministic unital associative continuation setup, if swapped-source additive commutativity fails then the carrier has at least 3 elements, and the §29.13 three-point witness realizes the bound.

Local inputs:
- `papers/bedc/parts/proof_obligations/unary_shift_and_commutativity.tex`
- `papers/bedc/parts/concrete_instances/05_add_namecert_construction.tex`

Rationale:
Two complementary facts already exist in the paper: §71.16 forces swapped commutativity at carrier size 2, and §29.13 exhibits a three-element countermodel where core additive stability fails to imply swapped commutativity. The board does not yet contain the minimality / lower-bound statement that fuses these into a single obstruction theorem (failure of swapped-commutativity ⇒ |carrier| ≥ 3, with realization). This is a concrete obstruction/minimality target rather than a parameter echo, has a clear single-implication shape, and lands at the unary_shift_and_commutativity file which is not near the line cap.

---

