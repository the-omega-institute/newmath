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

---

### B-07 - Lattice idempotence and absorption from bound characterization

| field | value |
|---|---|
| Status | Candidate (audit-curated 2026-05-02) |
| Source | hand audit of `concrete_instances/30_lattice_namecert_construction.tex` |
| Object | Lattice meet/join idempotence + absorption |
| Layer | concrete_instances |
| Route | proof |
| Risk | medium |
| Fit | 9/10 |
| Novelty | 9/10 |

Problem:
Under a lattice classifier whose meet $\wedge$ and join $\vee$ obligations are
specified by greatest-lower-bound and least-upper-bound characterizations,
the laws $x \wedge x = x$, $x \vee x = x$, $x \wedge (x \vee y) = x$,
$x \vee (x \wedge y) = x$ hold up to the lattice classifier.

Local inputs:
- `papers/bedc/parts/concrete_instances/30_lattice_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/28_poset_namecert_construction.tex`

Rationale:
Definition 30:30-41 lists "meet/join congruence" as a stability obligation
and defers to a "bound-characterization certificate", but no
`\begin{theorem|lemma}` proves idempotence or absorption from those
characterizations. Grep for "idempotence" / "absorption" in lattice files
returns 0 labeled theorems.

---

### B-08 - Module scalar action compatibility theorem

| field | value |
|---|---|
| Status | Candidate (audit-curated 2026-05-02) |
| Source | hand audit of `concrete_instances/21_module_namecert_construction.tex` |
| Object | Module scalar action compatibility |
| Layer | concrete_instances |
| Route | proof |
| Risk | medium |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
For a module $M$ over a commutative ring $R$ with abelian-group structure on
$M$, if the scalar action respects the ring multiplication classifier and
the group addition classifier, then $r \cdot (s \cdot m) = (r \cdot s) \cdot m$
is exact up to the module classifier.

Local inputs:
- `papers/bedc/parts/concrete_instances/21_module_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/17_abgroup_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/19_commring_namecert_construction.tex`

Rationale:
Definition 21:30-42 (Module stability certificate) lists scalar associativity
and distributivity as named obligations, but they never become standalone
theorems. No `\label{thm:module-...}` in 21_module_namecert.

---

### B-09 - Polynomial normalize commutes with add and multiply

| field | value |
|---|---|
| Status | Candidate (audit-curated 2026-05-02) |
| Source | hand audit of `concrete_instances/25_polynomial_namecert_construction.tex` |
| Object | Polynomial normalization commutativity |
| Layer | concrete_instances |
| Route | proof |
| Risk | medium-high |
| Fit | 8/10 |
| Novelty | 9/10 |

Problem:
For coefficient lists $p, q$ over a commutative ring with normalization
removing trailing zeros, $\mathrm{normalize}(\mathrm{add}(p, q)) = \mathrm{add}(\mathrm{normalize}(p), \mathrm{normalize}(q))$ and similarly for multiplication, both up to the polynomial classifier.

Local inputs:
- `papers/bedc/parts/concrete_instances/25_polynomial_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/19_commring_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/11_list_namecert_construction.tex`

Rationale:
Chapter 25:5 says "Polynomial addition and multiplication are derived
operations governed by the ring's certificate fields" and lists obligations
"normalization removes trailing zeros / idempotence / closure after
normalization", but no theorem proves `add` or `multiply` preserve
normalization. Grep "polynomial.*commut.*normali" = 0 hits.

---

### B-10 - Interval classifier nested-bound refinement

| field | value |
|---|---|
| Status | Candidate (audit-curated 2026-05-02) |
| Source | hand audit of `concrete_instances/31_interval_namecert_construction.tex` |
| Object | Interval nested bound refinement |
| Layer | concrete_instances |
| Route | proof |
| Risk | low-medium |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
If interval classifiers $(l_1, u_1)$ and $(l_2, u_2)$ are transitively
composed and $l_1 \leq l_2$, $u_2 \leq u_1$ (nested), then the composed
classifier refines to the outer interval $(l_1, u_1)$ up to history-sameness.

Local inputs:
- `papers/bedc/parts/concrete_instances/31_interval_namecert_construction.tex`
- `papers/bedc/parts/core/03_relational_extension_and_continuation.tex`

Rationale:
Theorem 31:190-200 proves general transitivity of interval classifiers but
no theorem states the refinement property under nested bounds. Grep
"interval.*nested|interval.*bound.*refine" = 0 labeled theorems.

---

### B-11 - Functor composition preserves hom-carrier classifier

| field | value |
|---|---|
| Status | Candidate (audit-curated 2026-05-02) |
| Source | hand audit of `concrete_instances/37_functor_namecert_construction.tex` |
| Object | Functor composition closure |
| Layer | concrete_instances |
| Route | proof |
| Risk | high |
| Fit | 10/10 |
| Novelty | 10/10 |

Problem:
If functors $F: C \to D$ and $G: D \to E$ have named certificates with
hom-carrier classifiers, the composite functor $G \circ F$ carries the
composed classifier: $\mathrm{HomCarrier}(G \circ F)(x, y) = \mathrm{HomCarrier}_E(G(F(x)), G(F(y)))$.

Local inputs:
- `papers/bedc/parts/concrete_instances/36_category_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/37_functor_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/38_nattrans_namecert_construction.tex`

Rationale:
Chapters 36, 37, 38 are 100% definition-only (7 definitions each, 0
theorems, all `\leandef`). Functor composition is foundational but no
theorem proves the composite carries the certificate.

---

### B-12 - Continuous function modulus composition

| field | value |
|---|---|
| Status | Candidate (audit-curated 2026-05-02) |
| Source | hand audit of `concrete_instances/34_continuous_namecert_construction.tex` |
| Object | Uniform continuity modulus composition |
| Layer | concrete_instances |
| Route | proof |
| Risk | high |
| Fit | 8/10 |
| Novelty | 9/10 |

Problem:
For metric spaces $X, Y, Z$ with certified moduli $\delta_1$ for $X \to Y$
and $\delta_2$ for $Y \to Z$, on any totally bounded $S \subseteq X$, the
composition $\delta_1(S, Y) \circ \delta_2(Y, Z)$ witnesses uniform
continuity of $f \circ g$ on $S$.

Local inputs:
- `papers/bedc/parts/concrete_instances/32_metric_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/34_continuous_namecert_construction.tex`

Rationale:
Definition 34:30-41 lists "closure under composition by composing moduli"
as a stability obligation but no theorem proves it. Grep
"continuous.*compos|modulus.*compos" returns only the obligation statement.

---

### B-13 - Total order trichotomy reduces classifier fields

| field | value |
|---|---|
| Status | Candidate (audit-curated 2026-05-02) |
| Source | hand audit of `concrete_instances/29_totalorder_namecert_construction.tex` |
| Object | Total order trichotomy classifier reduction |
| Layer | concrete_instances |
| Route | proof |
| Risk | low-medium |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
Under a total order whose classification is given by trichotomy
($x \leq y$ or $y < x$), the classifier is determined by a single direction
of ordering: $\leq(x, y) \vee \leq(y, x)$ together with the negation of
strict inequality is definitionally equivalent to the order classifier.

Local inputs:
- `papers/bedc/parts/concrete_instances/29_totalorder_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/28_poset_namecert_construction.tex`

Rationale:
Definition 29:25-28 says the classifier is "the partial-order classifier
plus trichotomy" but no theorem proves the reduction. Grep
"total.*trichotomy|trichotomy.*thm" returns 0 labeled theorems.

---

### B-14 - Natural transformation composition naturality

| field | value |
|---|---|
| Status | Candidate (audit-curated 2026-05-02) |
| Source | hand audit of `concrete_instances/38_nattrans_namecert_construction.tex` |
| Object | NatTrans composition preserves naturality square |
| Layer | concrete_instances |
| Route | proof |
| Risk | high |
| Fit | 10/10 |
| Novelty | 10/10 |

Problem:
For natural transformations $\alpha: F \Rightarrow G$ and
$\beta: G \Rightarrow H$ with component certificates, the composite
$(\beta \circ \alpha)_C$ satisfies the naturality square:
$H(f) \circ (\beta \circ \alpha)_C = (\beta \circ \alpha)_{C'} \circ F(f)$.

Local inputs:
- `papers/bedc/parts/concrete_instances/38_nattrans_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/37_functor_namecert_construction.tex`

Rationale:
Chapter 38 is 100% definitions (7 def, 0 thm). Definition 38:25-28 has a
"component coherence certificate"; composition preserving it is the next
natural theorem. Grep "nattrans.*compos" = 0 labeled theorems.

---

### B-15 - Real history-sameness under limit-classifier transport

| field | value |
|---|---|
| Status | Candidate (audit-curated 2026-05-02) |
| Source | hand audit of `concrete_instances/13_real_namecert_construction.tex` |
| Object | Bishop real sameness preserved under limit-classifier transport |
| Layer | concrete_instances / core |
| Route | proof |
| Risk | high |
| Fit | 8/10 |
| Novelty | 9/10 |

Problem:
For real numbers $x, y: \RealUp$ with $\hsame(x, y)$ via construction
histories, if a limit interface $L$ classifies $x$ and $y$ with a common
carrier witness, then the limit-endpoint history-sameness is congruent
with the base real sameness.

Local inputs:
- `papers/bedc/parts/concrete_instances/13_real_namecert_construction.tex`
- `papers/bedc/parts/core/10_thin_seal_interface.tex`

Rationale:
Definition 13 (Real certificate) describes Bishop reals with explicit
moduli; Chapter 10 remark says "completion / thread sealing are not
primitive finite-kernel steps" and "real-like names may appear only as
certificate-obligation schemas" but no theorem states the sameness transport
when sealing does occur.

---

### B-16 - Concrete token reflection duality

| field | value |
|---|---|
| Status | Candidate (audit-curated 2026-05-02) |
| Source | hand audit of `proof_obligations/package_token_policy.tex` |
| Object | Concrete-term token reflection from package sameness |
| Layer | proof_obligations |
| Route | proof |
| Risk | high |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
Under a package token policy whose `\TokIntro(\Pi, s, p)` predicate is given
a concrete term-level definition (rather than left abstract), $\psame(p, q)$
implies $\hsame(s, t)$ for the introducing signatures, decidably from the
concrete predicate without invoking the abstract policy.

Local inputs:
- `papers/bedc/parts/proof_obligations/package_token_policy.tex`
- `papers/bedc/parts/proof_obligations/exact_globalize.tex`
- `lean4/BEDC/FKernel/Package.lean`

Rationale:
Theorem 21:64-75 proves "package-sameness ↔ signature-sameness" under the
abstract policy. Line 40 hints at "the concrete signature-token instance"
but no theorem treats concrete `\TokIntro` directly. Grep
"token.*concrete|concrete.*reflect" = 0 new labeled theorems.

---
