# BEDC Lean naming and decomposition discipline

This file is the canonical naming + theorem-decomposition reference for both
the paper revision pipeline (`papers/bedc/scripts/codex_revise.py`) and the
Lean formalization pipeline (`lean4/scripts/codex_formalize.py`). The phase
prompts cite this file by path; codex MUST grep the existing tree for
collisions before adding a new name.

The conventions below are adapted from the mathlib naming guide. We adopt the
methodology, **not** the imports — `import Mathlib.X.Y` and any
`Classical.*` / `Quot.*` use stay forbidden by `CLAUDE.md` and the
axiom-purity gate.

## 1. Name structure

A theorem name reads as a sentence: `<Object>_<predicate>` with the **object
first**, the **predicate last**, and `_iff` (when present) trailing.

Good:
- `add_assoc`
- `List.length_append`
- `BHist.append_assoc`
- `compGap_coverage`
- `psame_refl`

Bad (object/predicate order reversed, or `iff` not trailing):
- ~~`length_List_append`~~
- ~~`bwordLength_append`~~ (uses a non-canonical variant `bwordLength` —
  the canonical name is `external_append_length`; pick one and delete the
  alias)
- ~~`witnesses_iff_compGap_three`~~ (`_iff` must be terminal:
  `compGap_three_witnesses_iff`)

A name should read top-to-bottom as it would in prose: "list length under
append" → `List.length_append`, not `List_append_length`.

## 2. Single canonical name per statement

Two declarations with α-equivalent types are NOT both allowed to live under
`lean4/BEDC/`. If you discover a duplicate while picking a target:

- Keep the name that follows §1 word order.
- Delete the other and update its callers (`grep -rn '\b<old_name>\b' lean4/
  papers/bedc/`).
- If the old name is referenced from a paper marker (`\leanchecked{X}` /
  `\leandef{X}`), update the marker to point at the canonical declaration in
  the same commit.

Concrete pairs already known to need cleanup (samples — there are more):
- `Mbin_eq_BHist` ⇄ `external_model_mbin`
- `Mbin_reuses_kernel_history` ⇄ `external_model_no_parallel_word_input`
- `bwordLength_append` ⇄ `external_append_length`

Do not introduce a new alias to "make a paper reader happy"; pick the
canonical Lean name and the paper marker uses that exact spelling.

## 3. No mechanical depth expansion

A theorem about an associative or otherwise tactic-decidable operation MUST
be stated at the **binary** (or one-step) level. The 3-element / 4-element /
5-element / N-element instances are obtainable by induction, `simp`, or
`omega` and are NOT separate theorems.

Forbidden suffix patterns (do not introduce new ones):
- `_two` / `_three` / `_four` / `_five` / `_six` (counting fixed arities for
  associativity, commutativity, four-bundle membership, etc.)
- `_two_step_*` / `_three_step_*` (chained variants of an existing one-step
  composition)
- `_witness_chain_*` / `_three_step_chain_*` for an existing closure that
  already has its primitive form

Examples of statements you must NOT add separately when the binary version
already exists:
- `external_append_assoc_three` / `_four` / `_five` (induction from
  `external_append_assoc`)
- `compGap_three_witnesses_iff` / `_four_witnesses_iff` (decompose into
  binary `compGap_witnesses_iff`)
- `PsameEqClosure_two_base_reflection` / `_three_base_reflection` /
  `_four_base_reflection` (one base reflection plus `psame` chain induction)
- `PackageReflection_base_witness_chain` / `_three_step_chain` next to
  `PackageReflection_base`

When you genuinely need a 3-element fact in a downstream proof, write it
inline inside the proof (not as a public theorem). If the inline expansion
becomes unwieldy, the right answer is to abstract a stronger primitive
about lists/chains/witnesses, NOT to add `_three` / `_four` versions.

## 4. `_iff` is canonical; do not split into directional twins

For a biconditional, write ONE theorem with name ending in `_iff`. Use
`.mp` and `.mpr` projections at call sites instead of two separate names.

Forbidden patterns:
- Both `<X>_witnesses_iff` and `<X>_iff_witnesses` (these are the same iff,
  one was hallucinated as the reverse)
- Both `<X>_from_witnesses` and `<X>_witnesses_imply` (use `_iff` and
  destructure)
- Both `<X>_to_<Y>` and `<X>_iff_<Y>` (keep `_iff`, drop `_to_`)

When picking a Phase-B / paper-review target, grep the existing tree:

```bash
grep -rE 'theorem\s+[A-Za-z0-9_]*<concept>[A-Za-z0-9_]*_iff' lean4/BEDC/
```

If any hit, the directional twin is INVALID; refactor downstream callers
to use the existing `_iff` instead of adding the directional version.

## 5. Derived-domain layering

`lean4/BEDC/Derived/<X>Up.lean` for `BoolUp`, `IntUp`, `RatUp`, `FieldUp`,
`RingUp`, `CommRingUp`, `ComplexUp`, `ListUp`, `OptionUp`, `ProdUp`,
`SumUp`, `GroupUp`, `MonoidUp`, `AbGroupUp`, `PreorderUp`, `IntervalUp`,
... currently each carry their own copies of:

- `<X>HistoryClassifier_exactness`
- `<X>HistoryEndpoint_pair`
- `<X>HistoryLedgerPolicy_envelope_closure`
- `<X>HistoryClassifier_branch_inversion`
- `<X>HistoryCarrier_*_readback`

These are five **shape-identical** theorems repeated for every domain. The
target abstraction is a `class DomainUpClassifier` / `DomainUpEndpoint` /
`DomainUpRing` hierarchy in `BEDC.Derived` that exposes the shared shape
once and instantiates per domain. Until that abstraction lands, a Phase-B
target whose conclusion is yet another per-domain copy of one of these
five shapes — without doing something genuinely new for that domain (e.g.
constructor disjointness for `SumUp`, denominator-positivity transport
for `RatUp`, distributivity for `RingUp`) — is **discouraged**: prefer
either the abstraction step itself, or a closure / determinism / inversion
theorem that is specific to the domain's underlying inductive shape.

## 6. Lean ↔ paper marker discipline

- A new `\leanchecked{X}` MUST reference a Lean declaration that exists
  under `lean4/BEDC/` AND whose name matches §1 word order. If a paper
  audit reveals a marker pointing at a non-§1 name, the right fix is to
  rename the Lean declaration to its canonical form, not to add an alias.
- `\leanvariant{Y}` is reserved for genuinely different binder shapes of
  the same claim that already has a `\leanchecked` primary. Automated
  rounds do NOT add new `\leanvariant` markers.
- The same Lean target should not appear under `\leanchecked` at two
  different paper sites. The drift audit will flag this.

## 7. Pre-add grep checklist

Before committing a new declaration `Foo`, codex MUST run:

```bash
grep -rE 'theorem\s+Foo\b|lemma\s+Foo\b|def\s+Foo\b' lean4/BEDC/
```

If hits exist, treat as a duplicate (§2). If a near-miss like `Foo_two`,
`Foo_three`, `Foo_witness_chain` is found, treat as a mechanical-suffix
collision (§3) and skip the new declaration.

Also grep for the conclusion shape, not just the name — α-equivalent
statements under different names are still duplicates.

## 8. What is NOT in scope here

- We do NOT adopt mathlib's `@[simp]` ecosystem; explicit `simp [lemma_a,
  lemma_b]` is preferred.
- We do NOT adopt mathlib's universe polymorphism; carriers stay in
  `Type 0`.
- We do NOT add `import Mathlib.X.Y`. Any such line fails CI.
- We do NOT depend on `Classical.choice` / `Quot.sound` / `propext`.
  These are forbidden by the axiom-purity gate; a proof shape that needs
  them is wrong, not the lemma.
