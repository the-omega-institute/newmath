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

### B-17 - SemanticNameCert presentation weakening

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | SemanticNameCert presentation weakening |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 10/10 |

Problem:
If `SemanticNameCert S P L C` holds and the presentation predicates weaken pointwise by `P(h) -> P'(h)` and `L(h) -> L'(h)`, then `SemanticNameCert S P' L' C` holds with unchanged source and classifier specifications.

Local inputs:
- `papers/bedc/parts/core/08_typed_naming_certificates.tex`
- `lean4/BEDC/FKernel/NameCert.lean`

Rationale:
Surfaced in Turn 1 as the weakest record-level bridge: source and classifier are reused while only pattern and ledger soundness are post-composed with implications. It deserves its own loop because it is a general core naming-certificate theorem, not specific to additive naming, and it would clarify which certificate fields are invariant under presentation changes.

---


### B-18 - Core additive stability does not imply swapped commutativity

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Core additive stability does not imply swapped commutativity |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 9/10 |

Problem:
There exists a finite carrier with equality classifier and deterministic associative unital continuation such that `NameCert`, closure, unit, associativity, same-source determinacy, and pattern/ledger soundness hold, but the swapped-source additive commutativity field fails.

Local inputs:
- `papers/bedc/parts/concrete_instances/05_add_namecert_construction.tex`
- `papers/bedc/parts/core/08_typed_naming_certificates.tex`
- `lean4/BEDC/FKernel/NameCert.lean`

Rationale:
Surfaced in Turn 3 as the finite three-element monoid obstruction separating same-source determinacy from swapped-source commutativity. It deserves its own loop because it is a concrete independence theorem supporting the naming boundary: the unary-continuation name can be licensed from the accepted stability fields, while the additive name requires an additional commutativity theorem.

---

### B-19 - Module scalar action representative stability

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Module scalar action representative stability |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
Under a ModuleUp setup, if scalars and module elements are replaced by classifier-equal representatives, then scalar associativity transports to r ⊙ (s ⊙ m) hsame_M (r' ·_R s') ⊙ m' using scalar-action congruence and ring multiplication congruence.

Local inputs:
- `papers/bedc/parts/concrete_instances/21_module_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/19_commring_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/17_abgroup_namecert_construction.tex`

Rationale:
Surfaced explicitly in Turn 0 as the alternative follow-up question: whether to state the result in a representative-stable form using scalar congruence and ring multiplication congruence. It deserves its own loop because B-08 commits only to the direct scalar-associativity field projection, while this adjacent theorem tests the classifier-transport behavior of the same module expression under representative changes.

---


### B-20 - Module associativity independence from additive and unit action laws

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Module associativity independence from additive and unit action laws |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 9/10 |

Problem:
For the concrete action of R = F_2[epsilon]/(epsilon^2) on M = F_2 defined by chi(0)=0, chi(1)=1, chi(epsilon)=1, chi(1+epsilon)=0, scalar congruence, scalar additivity, module additivity, and unit law hold, but scalar associativity fails.

Local inputs:
- `papers/bedc/parts/concrete_instances/21_module_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/19_commring_namecert_construction.tex`

Rationale:
Surfaced in Turns 0 and 1 as the finite obstruction showing that congruence, distributive/additive behavior, and unit are insufficient without the scalar-associativity field. It deserves its own loop as a compact independence proposition for the module certificate boundary, separate from the positive compatibility projection proved in B-08.

---

### B-21 - Trim invariance under zero-remainder spines

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Trim invariance under zero-remainder spines |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
Under the polynomial normalization setup over a scalar classifier, if two coefficient lists are pointwise scalar-classifier equal on their common shorter spine and every remaining coefficient in either list is scalar-classified as zero, then their normalized representatives are structurally list-same.

Local inputs:
- `papers/bedc/parts/concrete_instances/25_polynomial_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/11_list_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/19_commring_namecert_construction.tex`

Rationale:
Surfaced in Turn 1 as the explicit Lemma `Trim invariance under a common classified spine and zero remainders`, separated from raw polynomial addition. It deserves its own loop because it is a reusable normalization lemma for polynomial representatives, needed by addition and by any later operation whose raw outputs differ only by zero-classified tails, while not duplicating the broader B-09 operation-commutativity target.

---


### B-22 - Polynomial multiplication zero-tail invariance

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Polynomial multiplication zero-tail invariance |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 6/10 |

Problem:
For raw Cauchy convolution over a scalar ring, if a coefficient tail is pointwise scalar-classified as zero, then appending that tail to one input preserves the raw multiplication result up to the polynomial classifier.

Local inputs:
- `papers/bedc/parts/concrete_instances/25_polynomial_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/19_commring_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/11_list_namecert_construction.tex`

Rationale:
Surfaced in Turn 0 as the parallel first claim for multiplication: `ZeroTail_R(t) -> PolySame(rmul(p++t,q), rmul(p,q))`, with raw Cauchy convolution and finite-sum stability requirements. It is close to B-09, but distinct enough as the multiplication-side zero-tail theorem because the completed reasoning only made the addition proof exact and left multiplication with separate assumptions about multiplicative zero laws and finite sums.

---

### B-23 - Module scalar compatibility under representative transport

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Module scalar compatibility under representative transport |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
Under a ModuleUp setup with scalar associativity, scalar-action congruence, and ring multiplication congruence, if r hsime_R r', s hsime_R s', and m hsime_M m', then r odot (s odot m) hsime_M (r' dot_R s') odot m'.

Local inputs:
- `papers/bedc/parts/concrete_instances/21_module_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/19_commring_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/17_abgroup_namecert_construction.tex`

Rationale:
Surfaced in Turn 0 as the follow-up distinction between the direct scalar-associativity projection and the stronger representative-stable form that also uses scalar congruence and ring multiplication congruence. It deserves its own loop because B-08 deliberately commits only to the field projection, while this adjacent theorem records the classifier-transport behavior expected of module expressions.

---


### B-24 - Scalar associativity independent of module additivity and unit

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Scalar associativity independent of module additivity and unit |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 9/10 |

Problem:
There exists a finite equality-classified scalar action over R = F2[epsilon]/(epsilon^2) and M = F2 such that scalar congruence, scalar additivity, module additivity, and unit hold, but scalar associativity fails.

Local inputs:
- `papers/bedc/parts/concrete_instances/21_module_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/19_commring_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/17_abgroup_namecert_construction.tex`

Rationale:
Surfaced in Turn 0 as the obstruction showing congruence, distributivity-like additivity, and unit cannot prove the B-08 theorem, and was made finite and explicit in Turn 1 by naming the four ring elements and checking the action. It deserves its own loop because it sharpens the module certificate boundary: scalar associativity is an independent stability field rather than a consequence of the surrounding module action obligations.

---

### B-25 - Lattice commutativity from directional bounds

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Lattice commutativity from directional bounds |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 9/10 |

Problem:
Under a lattice setup with inherited poset antisymmetry and directional meet and join bound fields, the implications from the bound-characterization hypotheses yield x∧y ∼C y∧x and x∨y ∼C y∨x for all x,y.

Local inputs:
- `papers/bedc/parts/concrete_instances/30_lattice_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/28_poset_namecert_construction.tex`

Rationale:
Surfaced in Turn 1 and Turn 2 where the oracle states that commutativity is not used in the idempotence and absorption proof, while the lattice chapter excerpt says commutativity is among the laws derived from bound characterizations. It deserves its own loop because B-07 proves only idempotence and two absorption laws, and commutativity needs the opposite lower and upper bound fields that the completed theorem explicitly did not use.

---


### B-26 - Lattice associativity from directional bounds

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Lattice associativity from directional bounds |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 9/10 |

Problem:
Under a lattice setup with inherited preorder transitivity, poset antisymmetry, and directional meet and join bound fields, the implications from the bound-characterization hypotheses yield (x∧y)∧z ∼C x∧(y∧z) and (x∨y)∨z ∼C x∨(y∨z) for all x,y,z.

Local inputs:
- `papers/bedc/parts/concrete_instances/30_lattice_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/28_poset_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/27_preorder_namecert_construction.tex`

Rationale:
Surfaced in Turn 1 and Turn 2 where the oracle explicitly separates associativity from the fields used for B-07, while the lattice chapter excerpt presents associativity as another law derived from bound characterizations. It deserves its own loop because associativity is not covered by the finished idempotence and absorption theorem and requires an additional inherited preorder-transitivity dependency.

---

### B-27 - Lattice opposite absorption from directional bounds

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Lattice opposite absorption from directional bounds |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 7/10 |

Problem:
Under a lattice carrier with inherited P-refl and P-antisymm plus directional meet and join bound fields, the opposite absorption orientations x∧(y∨x) ∼C x, (x∨y)∧x ∼C x, x∨(y∧x) ∼C x, and (x∧y)∨x ∼C x hold for all x,y.

Local inputs:
- `papers/bedc/parts/concrete_instances/30_lattice_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/28_poset_namecert_construction.tex`

Rationale:
Surfaced in Turns 1 and 2 when the oracle made the dependency map explicit and noted that M-lower-right and J-upper-right are not used for the four displayed B-07 orientations. This deserves its own loop because B-07 proves only the left-oriented absorption laws, while the opposite orientations test the remaining directional bound fields directly without relying on the separate commutativity target.

---

### B-28 - CommRing forgets to Ring certificate

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | CommRing forgets to Ring certificate |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
Under a \(\CommRingUp(R)\) setup, dropping the multiplicative commutativity field yields the \(\RingUp(R)\) source package with the same carrier operations and classifier.

Local inputs:
- `papers/bedc/parts/concrete_instances/19_commring_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/18_ring_namecert_construction.tex`

Rationale:
Surfaced in Turn 0 where the oracle notes that if the ambient scalar package is stated as \(\CommRingUp(R)\), its ring fields supply the \(\RingUp(R)\) input, while multiplicative commutativity is unused. This deserves its own loop because B-08 depends only on the ring fragment of a commutative-ring scalar package, and a forgetful certificate projection would make that dependency explicit without duplicating the representative-transport or independence targets already on the board.

---

### B-29 - Lattice bound uniqueness from directional certificates

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Lattice bound uniqueness from directional certificates |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
Under the LatticeUp directional bound setup, for all x,y,m,j, if m satisfies the greatest-lower-bound inequalities for x,y and j satisfies the least-upper-bound inequalities for x,y, then m ∼C x∧y and j ∼C x∨y.

Local inputs:
- `papers/bedc/parts/concrete_instances/30_lattice_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/28_poset_namecert_construction.tex`

Rationale:
Turn 0 identified the precise obstruction that the lattice certificate might record greatestness or leastness as an unnamed uniqueness principle, requiring explicit lower/upper witnesses; Turn 1 then fixed the directional GLB/LUB fields. This deserves its own loop because B-07 proves laws of the certified meet and join operations, while this adjacent proposition proves classifier uniqueness for any candidate satisfying the same bound characterization.

---

### B-30 - Polynomial addition two-sided trim compatibility

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Polynomial addition two-sided trim compatibility |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 6/10 |

Problem:
Under the polynomial normalization setup over a scalar ring, for coefficient lists p and q, PolySame(radd(p,q), radd(trim(p),trim(q))) holds for zero-padded coefficientwise raw addition.

Local inputs:
- `papers/bedc/parts/concrete_instances/25_polynomial_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/11_list_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/19_commring_namecert_construction.tex`

Rationale:
Surfaced in Turn 0 as the two-sided addition statement following from two one-sided zero-tail applications, and again in Turn 1 as the explicit NEXT question about packaging it directly. It is adjacent to B-09 but narrower than the broad add-and-multiply normalization target, making it a useful standalone theorem site if the loop wants a direct classifier-level addition compatibility statement.

---


### B-31 - Polynomial addition right zero-tail invariance

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Polynomial addition right zero-tail invariance |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |

Problem:
Under the polynomial normalization setup over a scalar ring, if ZeroTail_R(t) holds, then PolySame(radd(p,q++t),radd(p,q)) holds for zero-padded coefficientwise raw addition.

Local inputs:
- `papers/bedc/parts/concrete_instances/25_polynomial_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/11_list_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/19_commring_namecert_construction.tex`

Rationale:
Surfaced in Turn 0 when the oracle says the two-sided addition statement follows by applying the one-sided claim once to p and once to q. The completed proof in Turn 1 handles only the left input p++t, so the right-input version is a precise adjacent proposition needed to make that two-sided derivation explicit without duplicating the reusable trim lemma B-21.

---

### B-32 - Unary continuation monoid activation

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Unary continuation monoid activation |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
Under the typed naming-certificate setup, `NameCert(UnaryCarrier, hsame)`, the `AddStabilityCert` fields for closure, unit, associativity, and same-source determinacy, plus the relevant pattern and ledger soundness, imply `License(UnaryContMonoidUp)`.

Local inputs:
- `papers/bedc/parts/concrete_instances/05_add_namecert_construction.tex`
- `papers/bedc/parts/core/08_typed_naming_certificates.tex`
- `lean4/BEDC/FKernel/NameCert.lean`

Rationale:
Surfaced in Turn 0, where the oracle says that without `UnaryComm` the strongest licensed name is `UnaryContMonoidUp`, and in Turn 3, where it asks which accepted fields license the unary-continuation name. This is separate from B-06's conditional `AddUp` activation and from B-18's countermodel: it records the positive boundary theorem for the monoid-like continuation interface using only the core `NameCert` and `AddStabilityCert` fields.

---

### B-33 - Raw polynomial addition can leave normal form

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Raw polynomial addition can leave normal form |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
Under a scalar ring with classified nonzero elements a and b satisfying a +_R b hsame_R 0_R, the normalized singleton coefficient lists [a] and [b] have raw zero-padded sum [a +_R b], whose trim is the empty zero representative while the raw sum itself is not a normalized representative.

Local inputs:
- `papers/bedc/parts/concrete_instances/25_polynomial_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/19_commring_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/11_list_namecert_construction.tex`

Rationale:
Surfaced in Turn 0 through the explicit p=[1], q=[-1] obstruction showing that literal list equality is too strong even when both inputs are normalized. It deserves its own loop because it records the exact reason polynomial addition must be stated through the classifier after trimming, rather than as a raw normalized-list operation.

---


### B-34 - Finite additive fold congruence for coefficient lists

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Finite additive fold congruence for coefficient lists |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
Under the scalar ring additive congruence fields and the list structural classifier, if two finite coefficient lists have the same length and pointwise scalar-classifier equal entries, then their additive folds are scalar-classifier equal.

Local inputs:
- `papers/bedc/parts/concrete_instances/11_list_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/19_commring_namecert_construction.tex`

Rationale:
Surfaced in Turn 0 when the multiplication-side zero-tail theorem was identified as needing additive congruence for finite sums. This deserves its own loop because raw Cauchy convolution reduces each coefficient to a finite additive fold, and the fold-congruence lemma is reusable beyond the single polynomial multiplication target.

---

### B-35 - Polynomial addition literal-list equality obstruction

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Polynomial addition literal-list equality obstruction |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 9/10 |

Problem:
Under the concrete integer commutative-ring polynomial setup, if p=[1] and q=[-1] for zero-padded raw addition radd, then trim(radd(p,q))=[] and radd(trim(p),trim(q))=[0], so the literal list equality trim(radd(p,q)) = radd(trim(p),trim(q)) fails while the polynomial classifier relates the two raw sums.

Local inputs:
- `papers/bedc/parts/concrete_instances/25_polynomial_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/19_commring_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/06_int_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/11_list_namecert_construction.tex`

Rationale:
Surfaced in Turn 0 as the explicit p=[1], q=[-1] obstruction to the stronger raw-list equality statement. It deserves its own loop because B-09 and the existing spawned targets state positive classifier-level compatibility, while this proposition records the precise reason the theorem must be classifier-level rather than literal list equality.

---

