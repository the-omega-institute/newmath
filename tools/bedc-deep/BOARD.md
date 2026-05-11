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

### B-647 - AffineSpaceUp inverse-vector action cancels back to the carried point

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | AffineSpaceUp inverse-vector action cancels back to the carried point |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 7/10 |

Problem:
Let p be a carried point row and v be an accepted vector row whose translation reading is accepted by the GroupUp dependency; then act(act(p,v), -V v) and p admit AffineSpace repackings classified by AffCls over the same source certificates.

Local inputs:
- `papers/bedc/parts/concrete_instances/184_affinespace_namecert_construction.tex`

Rationale:
184_affinespace_namecert_construction.tex (230 lines) has 'AffineSpaceUp action additivity' at line 189 (= B-510) and 'AffineSpaceUp zero action classifies the carried point' at line 212 (= B-571). Combining them gives act(act(p,v),-v) ~ act(p, v +V (-v)) ~ act(p, 0V) ~ p, but no theorem exposes this two-step cancellation. Grep 'inverse.*vector|negative.*vector|act.*inv' in the file returns only proof prose at line 119 mentioning 'inverse translation packet supplied by the GroupUp certificate' — used internally for free-action argumentation, never as a top-level row. This is a concrete inversion claim about the action pair (v,-v); not parameter-transport because the proof requires combining additivity, zero-action, and the GroupUp inverse law for the translation-packet readings. File at 230 lines.

---


### B-648 - InnerProduct norm-of-sum direct expansion (no orthogonality hypothesis)

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | InnerProduct norm-of-sum direct expansion (no orthogonality hypothesis) |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |

Problem:
For carried vector endpoints x,y of the InnerProduct parallelogram norm seed source, the retained scalar classifier classifies ‖x +V y‖²_I with ‖x‖²_I +K ⟨x,y⟩_I +K ⟨y,x⟩_I +K ‖y‖²_I.

Local inputs:
- `papers/bedc/parts/concrete_instances/innerproduct/parallelogram_norm_seed.tex`

Rationale:
parallelogram_norm_seed.tex (416 lines) has 'Pythagorean row' at line 126 (= B-508, requires x⊥y), 'parallelogram identity row' at line 30 (= B-572 family), 'polarization difference row' at line 209 (= B-514), and 'ternary orthogonal Pythagorean row' at line 333 (= B-528). All three of these proofs internally invoke the four-term expansion ⟨x+y,x+y⟩ = ⟨x,x⟩+⟨x,y⟩+⟨y,x⟩+⟨y,y⟩ via 'thm:innerproduct-vecspace-linearity-row' (the proof prose at lines 153, 230, etc.), but the unconditional expansion is never exposed as a standalone reusable theorem. Grep 'norm.*sum|x\+y.*sim' returns no matching theorem statement. Landing file 416 lines. Concrete unconditional-classifier identity, not parameter-transport.

---


### B-649 - Sheaf base-change three-square associativity

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Sheaf base-change three-square associativity |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 7/10 |
| Novelty | 8/10 |

Problem:
If T'''→T''→T'→T is a triple of composable displayed base-change squares, then the cover-pullback, gluing-pullback, and common-refinement composites obtained by bracketing as ((h∘g)∘f) and (h∘(g∘f)) classify with the same downstream pullback rows on every cover, compatible family, and presentation.

Local inputs:
- `papers/bedc/parts/concrete_instances/sheaf/base_change_functoriality.tex`

Rationale:
sheaf/base_change_functoriality.tex (82 lines) currently has identity-square neutrality (line 22), two-square cover-pullback composition (line 37), gluing-pullback composition (line 53), and common-refinement composition (line 68). The associativity for three squares is the natural functoriality-completing companion to identity-square neutrality. Grep 'base-change.*associativ|three.*square' across sheaf/ returns 0 matches. The proof unfolds composability twice and chains the existing two-square composition theorem on each side; small theorem block fits well under 760-line cap. This is an associativity claim for the displayed composition operation, not a parameter echo of a single transport row.

---

