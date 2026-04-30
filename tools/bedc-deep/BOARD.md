# BEDC Deep Reasoning Board

Purpose: route BEDC proof-obligation questions into a ChatGPT multi-turn
reasoning loop without touching Lean source files or paper markers.

Contract:
- The loop may read project text and produce a claim packet.
- The loop must not run Lean, lake, elan, or edit `lean4/`.
- The loop must not edit `papers/bedc/`.
- Any result is advisory until a separate formalization path accepts it.
- Each answer must classify the claim as one of:
  `Derived`, `NeedsDefinition`, `NeedsSetupField`, `NarrativeOnly`,
  `TooStrong`, or `False`.

---

### B-01 - Psame base inversion

| field | value |
|---|---|
| Status | Candidate |
| Source | `papers/bedc/parts/proof_obligations/verification_queue.tex` |
| Object | `PsameBase.inversion` |
| Layer | package-token policy |
| Route | proof |
| Risk | medium |

Problem:
Is base package-sameness inversion a definitional consequence of the current
one-constructor package relation, or does it require an explicit structure
field?

Local inputs:
- `papers/bedc/parts/proof_obligations/package_token_policy.tex`
- `papers/bedc/parts/proof_obligations/psame_design.tex`
- `lean4/BEDC/FKernel/Package.lean`

Success criterion:
State the smallest claim that exposes the introducing signatures and the
history-sameness proof from base package-sameness.

Failure criterion:
Identify the precise missing constructor, eliminator, or setup field.

---

### B-02 - Token replacement from uniqueness

| field | value |
|---|---|
| Status | Candidate |
| Source | `papers/bedc/parts/proof_obligations/verification_queue.tex` |
| Object | `TokUnique.tokenReplacement` |
| Layer | package-token policy |
| Route | proof |
| Risk | medium |

Problem:
Given one token with two introductions, determine whether token uniqueness
already forces history-sameness of the two introducing signatures.

Local inputs:
- `papers/bedc/parts/proof_obligations/package_token_policy.tex`
- `papers/bedc/parts/core/06_packages_and_package_policies.tex`
- `lean4/BEDC/FKernel/Package.lean`
- `lean4/BEDC/FKernel/Sig.lean`

Success criterion:
Separate the exact uniqueness premise from the derived replacement claim.

Failure criterion:
Show that the currently named uniqueness premise is only narrative and must be
encoded as a setup field.

---

### B-03 - Base package reflection

| field | value |
|---|---|
| Status | Candidate |
| Source | `papers/bedc/parts/proof_obligations/verification_queue.tex` |
| Object | `PackageReflection.base` |
| Layer | package-token policy |
| Route | proof |
| Risk | medium |

Problem:
Can base package reflection be reduced to base inversion plus token uniqueness,
or does it require stronger coverage of token introductions?

Local inputs:
- `papers/bedc/parts/proof_obligations/package_token_policy.tex`
- `papers/bedc/parts/concrete_hardening/domain_and_token_reflection.tex`
- `lean4/BEDC/BaseReflection.lean`
- `lean4/BEDC/FKernel/Package.lean`

Success criterion:
Give a dependency-minimal claim chain for base reflection.

Failure criterion:
Identify which premise is not derivable from the current package setup.

---

### B-04 - Gap coverage and separation

| field | value |
|---|---|
| Status | Candidate |
| Source | `papers/bedc/parts/proof_obligations/verification_queue.tex` |
| Object | `Gap.coverage`, `Gap.separation` |
| Layer | gap policy |
| Route | proof |
| Risk | high |

Problem:
Decide which part of gap coverage and gap separation is a theorem about the
generated BEDC objects and which part is a policy assumption.

Local inputs:
- `papers/bedc/parts/proof_obligations/gap_policy.tex`
- `papers/bedc/parts/core/07_gap_policies_coverage_separation_and_composition.tex`
- `lean4/BEDC/FKernel/Gap.lean`
- `lean4/BEDC/FKernel/Package.lean`

Success criterion:
Classify coverage and separation into derived fragments and setup-field
fragments.

Failure criterion:
Find a finite countermodel showing that an unconditional statement is too
strong.

---

### B-05 - Unary shift spine

| field | value |
|---|---|
| Status | Candidate |
| Source | `papers/bedc/parts/proof_obligations/verification_queue.tex` |
| Object | `E1.congruence`, `UnaryShift.base`, `UnaryShift.step`, `UnaryShift.theorem` |
| Layer | unary interface |
| Route | proof |
| Risk | medium |

Problem:
Find the exact induction spine needed for unary right-shift without replacing
BEDC history-sameness by host equality.

Local inputs:
- `papers/bedc/parts/proof_obligations/unary_shift_and_commutativity.tex`
- `papers/bedc/parts/concrete_hardening/unary_add_commutativity.tex`
- `lean4/BEDC/FKernel/Examples/Unary.lean`
- `lean4/BEDC/FKernel/Hist.lean`

Success criterion:
State the smallest ordered lemma sequence that could make unary right-shift
machine-checkable.

Failure criterion:
Show which congruence or continuation inversion principle is missing.

---

### B-06 - Unary commutativity and naming license

| field | value |
|---|---|
| Status | Candidate |
| Source | `papers/bedc/parts/proof_obligations/verification_queue.tex` |
| Object | `UnaryComm.theorem`, `NameCert.Add.activation` |
| Layer | name certificate |
| Route | proof |
| Risk | high |

Problem:
Determine whether additive naming can be licensed from unary commutativity, and
which earlier claims must be accepted first.

Local inputs:
- `papers/bedc/parts/proof_obligations/unary_shift_and_commutativity.tex`
- `papers/bedc/parts/core/08_typed_naming_certificates.tex`
- `papers/bedc/parts/concrete_instances/05_add_namecert_construction.tex`
- `lean4/BEDC/FKernel/NameCert.lean`

Success criterion:
Give a dependency chain that makes the naming license conditional and explicit.

Failure criterion:
Show that the additive name is being asserted before the needed stability
claim is available.

