# BEDC Deep Reasoning Board Completed Archive

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

### B-36 - Uniformly continuous images preserve total boundedness

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Uniformly continuous images preserve total boundedness |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 10/10 |
| Novelty | 9/10 |

Problem:
Under the certified metric and ContinuousFunctionUp setup, if S is a totally bounded subset of X and g:X->Y has a certified uniform-continuity modulus on S, then the image subset g[S] is totally bounded in Y.

Local inputs:
- `papers/bedc/parts/concrete_instances/32_metric_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/34_continuous_namecert_construction.tex`

Rationale:
Surfaced in Turn 0 as the setup-field proposition needed before the second modulus in the composition proof can be read from the ContinuousFunctionUp certificate. It deserves its own loop because B-12 handles chaining moduli for composition, while this proposition supplies the separate constructive cover-transfer lemma: a finite cover of S at precision delta_g(n) maps to a finite cover of g[S] at precision n.

---

### B-37 - Trim exposes a zero suffix

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Trim exposes a zero suffix |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 7/10 |

Problem:
Under the polynomial normalization setup, if a coefficient list p is decomposed at the normalization cut as p = trim(p) ++ s, then ZeroTail_R(s) holds.

Local inputs:
- `papers/bedc/parts/concrete_instances/25_polynomial_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/11_list_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/19_commring_namecert_construction.tex`

Rationale:
Surfaced in Turn 0 when the oracle says the two-sided addition statement follows by applying the one-sided theorem to the zero tail removed from p and q, and in Turn 1 when the trim proof identifies the kept prefix through the last nonzero-classified coefficient. It deserves its own loop because two-sided trim compatibility needs an explicit bridge from an arbitrary list to its normalized prefix plus a zero-classified deleted suffix.

---

### B-38 - Zero convolution summands fold to zero

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Zero convolution summands fold to zero |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
Under the scalar ring finite-sum setup used for raw Cauchy convolution, if every summand in a finite convolution index set is scalar-classifier equal to 0_R, then the additive fold over that index set is scalar-classifier equal to 0_R.

Local inputs:
- `papers/bedc/parts/concrete_instances/25_polynomial_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/19_commring_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/11_list_namecert_construction.tex`

Rationale:
Surfaced in Turn 0 where the oracle separates the multiplication case from addition and states that raw Cauchy convolution tail-invariance needs multiplicative zero laws plus additive congruence for finite sums. This is narrower than the full polynomial multiplication zero-tail theorem and isolates the finite-sum lemma that the multiplication proof must consume.

---

### B-39 - Literal polynomial add-trim equality fails

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Literal polynomial add-trim equality fails |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 7/10 |
| Novelty | 8/10 |

Problem:
Under the canonical integer coefficient ring, if p = [1] and q = [-1], then trim(radd(p,q)) = [] while radd(trim(p),trim(q)) = [0], so literal list equality fails although the two outputs are polynomial-classified the same.

Local inputs:
- `papers/bedc/parts/concrete_instances/25_polynomial_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/19_commring_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/11_list_namecert_construction.tex`

Rationale:
Surfaced explicitly in Turn 0 as the obstruction to the too-strong equation trim(radd(p,q)) = radd(trim(p),trim(q)). It deserves its own loop as a compact finite countermodel fixing the theorem boundary at classifier-level equality rather than raw list equality.

---

### B-40 - Polynomial literal add-normalization equality obstruction

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Polynomial literal add-normalization equality obstruction |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 9/10 |

Problem:
Over the canonical integer scalar ring, normalized coefficient lists p=[1] and q=[-1] imply trim(radd(p,q)) is not literally equal as a coefficient list to radd(trim(p),trim(q)), even though the two sides are polynomial-classified the same.

Local inputs:
- `papers/bedc/parts/concrete_instances/25_polynomial_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/19_commring_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/11_list_namecert_construction.tex`

Rationale:
Surfaced in Turn 0 when the oracle identified the literal list equation as too strong and gave the concrete p=[1], q=[-1] obstruction. It deserves its own loop because it records the exact boundary between classifier-level normalization compatibility and false raw-list equality, and it is not duplicated by the existing positive trim-compatibility or zero-tail invariance targets.

---

### B-41 - Uniform continuity preserves total bounded images

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Uniform continuity preserves total bounded images |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 10/10 |
| Novelty | 10/10 |

Problem:
Under certified metric spaces X and Y, if S is totally bounded in X and g:X->Y has a certified uniform-continuity modulus on S, then the image subset g[S] is totally bounded in Y.

Local inputs:
- `papers/bedc/parts/concrete_instances/32_metric_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/34_continuous_namecert_construction.tex`

Rationale:
Surfaced in Turn 0 as the setup-field proposition needed before the second modulus in the composition proof can be requested on g[S]. It deserves its own loop because B-12 handles modulus chaining, while this proposition supplies the separate certificate-side total-boundedness transport needed to license the image-subset modulus for the outer map.

---

### B-42 - Uniform modulus restriction along subset containment

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Uniform modulus restriction along subset containment |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 9/10 |

Problem:
Under a certified metric-function setup, if a modulus delta witnesses uniform continuity of f:T->Z on a subset T of Y and U is a subset of T, then the same delta witnesses uniform continuity of f on U.

Local inputs:
- `papers/bedc/parts/concrete_instances/32_metric_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/34_continuous_namecert_construction.tex`

Rationale:
Surfaced in Turn 0 through the alternative use of a certified totally bounded T subset Y containing g[S], where the outer modulus may be supplied on T rather than exactly on g[S]. It is adjacent to B-12 but distinct: it is a subset-transport lemma for modulus validity, not a composition theorem.

---

### B-43 - Uniform continuity modulus restricts along subset inclusion

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Uniform continuity modulus restricts along subset inclusion |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 9/10 |

Problem:
Under certified MetricSpaceUp objects Y and Z, if delta is a uniform-continuity modulus for f:Y->Z on a subset T and U subset T, then the same delta is a uniform-continuity modulus for f on U.

Local inputs:
- `papers/bedc/parts/concrete_instances/32_metric_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/34_continuous_namecert_construction.tex`

Rationale:
Surfaced in Turn 0 when the oracle allowed replacing g[S] by a certified totally bounded subset T containing g[S]. This is adjacent to B-12 because it packages the subset-restriction step separately from composition, making the theorem usable when the second map is certified on an enclosing subset rather than exactly on the image.

---

### B-44 - FunctorHomCarrier codomain evaluation

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | FunctorHomCarrier codomain evaluation |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 10/10 |
| Novelty | 9/10 |

Problem:
Under the category and functor certificate setup, if a certified functor H:C->E is equipped with the functor-layer abbreviation FunctorHomCarrier(H,x,y) := HomCarrier_E(H0(x),H0(y)), then the functor-indexed hom-carrier classifier at x,y is the codomain category hom-carrier classifier on H0(x),H0(y).

Local inputs:
- `papers/bedc/parts/concrete_instances/36_category_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/37_functor_namecert_construction.tex`

Rationale:
Surfaced in Turns 0 and 3 as the exact missing abbreviation needed to make the B-11 equality wording well typed and forced. It deserves its own loop because B-11 ended with an obstruction: the composite theorem cannot be stated canonically until the functor layer records this codomain-evaluation hom-carrier display.

---

### B-45 - Functor composite preservation witnesses

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Functor composite preservation witnesses |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 7/10 |

Problem:
Under certified categories C,D,E and certified functors F:C->D and G:D->E, the composite object and morphism maps imply that G∘F preserves identities and composition under the morphism classifier of E.

Local inputs:
- `papers/bedc/parts/concrete_instances/36_category_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/37_functor_namecert_construction.tex`

Rationale:
Surfaced in Turn 3 as the derivable positive part separate from the missing hom-carrier display: identity preservation follows by the identity fields of F and G, and composition preservation follows by their composition fields. It is adjacent rather than identical to B-11 because it isolates the preservation-witness assembly that remains valid even when the displayed HomCarrier(G∘F) equality is not forced.

---

### B-46 - Interval carrier boundary weakening

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Interval carrier boundary weakening |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
Under the interval setup, pointwise lower-bound weakening and upper-bound weakening maps imply that every history in the inner interval carrier \(\mathsf{IntervalCarrier}_{l_2,u_2}(h)\) also lies in the outer carrier \(\mathsf{IntervalCarrier}_{l_1,u_1}(h)\).

Local inputs:
- `papers/bedc/parts/concrete_instances/31_interval_namecert_construction.tex`
- `papers/bedc/parts/core/03_relational_extension_and_continuation.tex`

Rationale:
Surfaced in Turn 0 as the smallest testable claim before the classifier-level theorem: the oracle isolated carrier weakening from explicit boundary maps \(\lambda_h\) and \(\upsilon_h\). It deserves its own loop because it is a reusable carrier-level theorem underlying B-10 but not identical to the composed-classifier refinement target.

---

### B-47 - Interval classifier boundary weakening

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Interval classifier boundary weakening |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 7/10 |

Problem:
Under the interval setup, pointwise carrier boundary weakening maps imply that \(\mathsf{IntervalClassifierSpec}_{l_2,u_2}(h,k)\) entails \(\mathsf{IntervalClassifierSpec}_{l_1,u_1}(h,k)\) with the stored \(\hsame(h,k)\) witness unchanged.

Local inputs:
- `papers/bedc/parts/concrete_instances/31_interval_namecert_construction.tex`
- `papers/bedc/parts/core/03_relational_extension_and_continuation.tex`

Rationale:
Surfaced in Turn 0 as the direct classifier-level consequence of carrier weakening: apply the carrier lemma to both endpoints and reuse the history-sameness link. It is adjacent to B-10 because B-10 uses it inside a transitive composition proof, while this target records the standalone refinement of a single interval classifier.

---

### B-48 - Interval nesting requires boundary eliminators

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Interval nesting requires boundary eliminators |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 9/10 |

Problem:
There exists a finite one-history interval-classifier model in which the inner classifier holds and the outer classifier fails when symbolic nesting assumptions are present without lower- and upper-bound weakening eliminators.

Local inputs:
- `papers/bedc/parts/concrete_instances/31_interval_namecert_construction.tex`
- `papers/bedc/parts/core/08_typed_naming_certificates.tex`

Rationale:
Surfaced in Turn 0 as the precise obstruction: symbolic inequalities alone do not force carrier inclusion unless they eliminate to boundary-weakening maps or order-transitivity data. This deserves a separate loop as an independence/boundary proposition clarifying the exact setup-field obligation for interval nested-bound reasoning.

---

### B-49 - Polynomial normalization literal add equality obstruction

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Polynomial normalization literal add equality obstruction |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 9/10 |

Problem:
Under the canonical integer commutative-ring polynomial setup, if p=[1] and q=[-1], then p and q are normalized but trim(radd(p,q)) is not literally equal to radd(trim(p),trim(q)) as coefficient lists, while the two sides are polynomial-classifier equal.

Local inputs:
- `papers/bedc/parts/concrete_instances/25_polynomial_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/19_commring_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/11_list_namecert_construction.tex`

Rationale:
Surfaced in Turn 0 as the explicit p=[1], q=[-1] counterexample showing that the literal list equation is too strong even for normalized inputs. It deserves its own loop because the existing board has positive classifier-level compatibility targets, but no finite obstruction separating literal list equality from polynomial classifier equality.

---

### B-50 - Unary-continuation activation from additive stability

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Unary-continuation activation from additive stability |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
Under `NameCert(UnaryCarrier, hsame)` and the `AddStabilityCert` fields for closure, unit, associativity, and same-source determinacy, `License(UnaryContMonoidUp)` holds without any additive commutativity premise.

Local inputs:
- `papers/bedc/parts/concrete_instances/05_add_namecert_construction.tex`
- `papers/bedc/parts/core/08_typed_naming_certificates.tex`
- `papers/bedc/parts/proof_obligations/unary_shift_and_commutativity.tex`
- `lean4/BEDC/FKernel/NameCert.lean`

Rationale:
Surfaced in Turns 0 and 3 when the oracle separated the monoid-like unary-continuation name from the additive name: the core certificate plus closure, unit, associativity, and same-source determinacy license `UnaryContMonoidUp`, while `AddUp` requires an extra swapped-source commutativity field. This deserves its own loop because B-06 handles the conditional additive activation boundary, but the positive activation theorem for the weaker unary-continuation interface is a distinct certificate projection.

---

### B-51 - Same-source additive determinacy bridge

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Same-source additive determinacy bridge |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
Under `AddStabilityCert`, if `AddSource(h,k,r)` and `AddSource(h,k,r')` have the same ordered source pair, then `AddClassifier(r,r')` holds.

Local inputs:
- `papers/bedc/parts/concrete_instances/05_add_namecert_construction.tex`
- `papers/bedc/parts/core/08_typed_naming_certificates.tex`

Rationale:
Surfaced in Turns 2 and 3 as the exact contrast with swapped-source commutativity: determinacy compares two outputs of `ContR(h,k,-)` for the same ordered pair, and the oracle repeatedly used this type to explain why it cannot prove commutativity. A standalone bridge from `AddSourceSpec` plus the determinacy field to `AddClassifier` would clarify the accepted stability content without duplicating the separate B-18 obstruction.

---

### B-52 - Two-element unital continuations are swapped-commutative

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Two-element unital continuations are swapped-commutative |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 7/10 |
| Novelty | 9/10 |

Problem:
For any equality-classified deterministic total continuation on a carrier with at most two elements and a two-sided unit, swapped-source additive commutativity holds, so a finite equality countermodel to `AddCommField` requires at least three carrier elements.

Local inputs:
- `papers/bedc/parts/concrete_instances/05_add_namecert_construction.tex`
- `papers/bedc/parts/proof_obligations/unary_shift_and_commutativity.tex`

Rationale:
Surfaced explicitly in Turn 3, where the oracle noted that the three-element monoid obstruction is smallest because a two-element monoid with unit cannot witness the failure. This is adjacent to B-18 but not a duplicate: B-18 asks for an existence countermodel, while this target proves the finite minimality boundary for that obstruction.

---

### B-53 - AbGroup forgets to Group certificate

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | AbGroup forgets to Group certificate |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
Under an \(\AbGroupUp(M)\) setup, dropping the commutativity field yields the underlying \(\GroupUp(M)\) source package with the same carrier operation, identity, inverse, and classifier.

Local inputs:
- `papers/bedc/parts/concrete_instances/17_abgroup_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/16_group_namecert_construction.tex`

Rationale:
Surfaced in Turn 0 and Turn 1 when the oracle states that the abelian commutativity field is unused by module scalar action compatibility, except that \(\ModuleUp\) takes an additive abelian-group carrier as input. This is adjacent to B-08 because it isolates the forgetful certificate projection on the module-carrier side, and it is not the same as the already-boarded CommRing-to-Ring projection.

---

### B-54 - Raw addition literal list equality obstruction

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Raw addition literal list equality obstruction |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
Under the canonical integer-ring polynomial setup, if p=[1] and q=[-1], then p and q are normalized while trim(radd(p,q))=[] and radd(trim(p),trim(q))=[0], so literal list equality between these representatives fails although the polynomial classifier identifies them.

Local inputs:
- `papers/bedc/parts/concrete_instances/25_polynomial_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/19_commring_namecert_construction.tex`

Rationale:
Turn 0 gives this explicit p=[1], q=[-1] obstruction to the too-strong list equation. It deserves its own loop because it records the exact boundary between classifier-level polynomial equality and literal representative equality, without duplicating the existing positive trim-compatibility targets.

---

### B-55 - Finite additive fold respects scalar classifier

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Finite additive fold respects scalar classifier |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
Under a scalar RingUp setup and the finite list setup, if two coefficient lists xs and ys have the same length and xs_i hsame_R ys_i for every valid index i, then fold_add(xs) hsame_R fold_add(ys).

Local inputs:
- `papers/bedc/parts/concrete_instances/18_ring_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/19_commring_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/11_list_namecert_construction.tex`

Rationale:
Turn 0 identifies finite-sum stability as a required assumption for the multiplication analogue. This is a reusable ring/list proposition needed for raw Cauchy convolution arguments, distinct from the existing polynomial multiplication zero-tail target because it isolates the finite additive-fold transport step.

---

### B-56 - Unary continuation monoid activation from stability

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Unary continuation monoid activation from stability |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
If `C : NameCert(UnaryCarrier, hsame)` holds and `S : AddStabilityCert` supplies unary closure, unit, associativity, and same-source determinacy, then `License(UnaryContMonoidUp)` holds without any `AddCommField` or `UnaryComm` premise.

Local inputs:
- `papers/bedc/parts/concrete_instances/05_add_namecert_construction.tex`
- `papers/bedc/parts/core/08_typed_naming_certificates.tex`
- `lean4/BEDC/FKernel/NameCert.lean`

Rationale:
Surfaced in Turns 0, 2, and 3 as the positive boundary complementary to the additive obstruction: the accepted core certificate and additive stability fields license the unary-continuation monoid-like name, while the additive name requires an extra swapped-source commutativity field. It deserves its own loop because B-06 focuses on conditional `AddUp` activation, whereas this isolates the weaker activation theorem that should remain valid when commutativity is unavailable.

---

### B-57 - Two-element monoid cannot witness additive noncommutativity

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Two-element monoid cannot witness additive noncommutativity |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 7/10 |
| Novelty | 8/10 |

Problem:
If `M` is a two-element monoid with equality classifier, total unary carrier, and `ContR(x,y,z)` defined by `x * y = z`, then the swapped-source additive commutativity field holds for all `x,y,z,z'`.

Local inputs:
- `papers/bedc/parts/concrete_instances/05_add_namecert_construction.tex`
- `papers/bedc/parts/core/08_typed_naming_certificates.tex`

Rationale:
Surfaced explicitly in Turn 3, where the oracle noted that a two-element monoid with unit cannot witness the failure exhibited by the three-element obstruction. It is distinct from the existing three-element independence target because it proves the minimality side of that counter-situation: the separation cannot occur at carrier size two under the same equality-classified monoid interpretation.

---

### B-58 - Uniformly continuous image of totally bounded subsets

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Uniformly continuous image of totally bounded subsets |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 10/10 |
| Novelty | 9/10 |

Problem:
Under the ContinuousFunction and MetricSpace certificate setups, if S is a certified totally bounded subset of X and g:X->Y has a certified uniform-continuity modulus on S, then the image subset g[S] is certified totally bounded in Y.

Local inputs:
- `papers/bedc/parts/concrete_instances/32_metric_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/34_continuous_namecert_construction.tex`

Rationale:
Surfaced in Turn 0 as the setup-field proposition needed before the second modulus can be read on g[S]: TotBdd_X(S) together with UCMod_S(g,delta_g) implies TotBdd_Y(g[S]). It deserves its own loop because B-12 handles modulus chaining, while this proposition licenses the image subset on which the second continuous-function certificate may supply a modulus.

---

### B-59 - Uniform-continuity modulus restricts along subset inclusion

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Uniform-continuity modulus restricts along subset inclusion |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
Under the ContinuousFunction certificate setup, if delta is a uniform-continuity modulus for f:Y->Z on a certified subset T and U is a subset of T, then the same delta is a uniform-continuity modulus for f on U.

Local inputs:
- `papers/bedc/parts/concrete_instances/34_continuous_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/32_metric_namecert_construction.tex`

Rationale:
Surfaced in Turn 0 when the oracle replaced the global-looking delta_2(Y,Z) by a modulus for f on g[S] or on a certified totally bounded T subset Y containing g[S]. The containment case requires a standalone restriction principle, distinct from B-12's composition theorem and useful for any later continuous-function certificate transport across smaller requested subsets.

---

### B-60 - Unary continuation activation without commutativity

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Unary continuation activation without commutativity |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
Under the additive semantic naming setup, if `NameCert(\UnaryCarrier,\hsame)` and `AddStabilityCert` supply carrier inhabitedness, equivalence laws, transport, closure, unit, associativity, same-source determinacy, and pattern/ledger soundness, then `\License(\UnaryContMonoidUp)` holds without assuming the swapped-source additive commutativity field.

Local inputs:
- `papers/bedc/parts/concrete_instances/05_add_namecert_construction.tex`
- `papers/bedc/parts/core/08_typed_naming_certificates.tex`
- `lean4/BEDC/FKernel/NameCert.lean`

Rationale:
Surfaced in Turn 0 when the oracle states that the `NameCert` fields and `AddStabilityCert` license the monoid-like continuation name but not the additive name, and again in Turn 3 in the final dependency map separating accepted fields for `\UnaryContMonoidUp` from the additional theorem needed for `\AddUp`. It deserves its own loop because it is the positive half of the naming boundary and is distinct from B-06, which focuses on conditional activation of `\AddUp`, and from B-18, which focuses on the finite obstruction.

---

### B-61 - Two-element unital continuation commutativity

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Two-element unital continuation commutativity |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 7/10 |
| Novelty | 7/10 |

Problem:
If a finite equality-classified carrier has exactly two unary elements and `ContR` is the graph of a total deterministic binary operation with a two-sided unit, then for any `ContR(h,k,r)` and `ContR(k,h,r')` one has `\hsame(r,r')`.

Local inputs:
- `papers/bedc/parts/concrete_instances/05_add_namecert_construction.tex`
- `papers/bedc/parts/core/08_typed_naming_certificates.tex`

Rationale:
Surfaced in Turn 3 where the oracle states that a two-element monoid with unit cannot witness the swapped-commutativity failure, because all products involving the unit commute and the remaining product is the same on both sides. It deserves its own loop if the paper wants the three-element obstruction to be minimal, and it does not duplicate B-18 because B-18 proves existence of a three-element counter-situation rather than the two-element lower bound.

---

### B-62 - Raw functor hom-carrier landing obstruction

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Raw functor hom-carrier landing obstruction |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 9/10 |

Problem:
Under the explicit finite C,D,F setup from Turn 1, satisfaction of the object map, raw morphism map, identity preservation, and composition preservation fields implies HomCarrier_C(0,1,a) and not HomCarrier_D(F0(0),F0(1),F1(a)).

Local inputs:
- `papers/bedc/parts/concrete_instances/36_category_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/37_functor_namecert_construction.tex`

Rationale:
Turn 1 gives a finite two-object countermodel where identity and composition preservation hold strictly while the raw image of a displayed source hom lands in the wrong codomain hom carrier; Turn 2 asks for the same obstruction as a citable theorem with category-law verification. This deserves a standalone loop because it isolates the exact missing endpoint-indexed mapHom field, distinct from the B-11 composition theorem itself.

---

### B-63 - Functor composition identity requires sameness-respect

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Functor composition identity requires sameness-respect |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 9/10 |

Problem:
Under the finite C,D,E,F,G setup from Turn 0, raw identity and composition preservation for F and G without morphism-sameness respect for G implies failure of identity preservation for the composite G o F.

Local inputs:
- `papers/bedc/parts/concrete_instances/36_category_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/37_functor_namecert_construction.tex`

Rationale:
Turn 0 surfaces a separate obstruction: F preserves identity only through universal D-sameness, while G maps D-same morphisms to E-distinct morphisms, so the composite sends the source identity to a non-identity in E. This is adjacent to hom-carrier landing but tests a different boundary field, namely mapSame or classifier-respect for morphism maps.

---

### B-64 - Directed meet associativity comparison from bounds

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Directed meet associativity comparison from bounds |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 7/10 |

Problem:
Under a LatticeUp carrier with inherited PreorderUp transitivity and the directional meet lower-bound and greatest-lower-bound implication fields, (x∧y)∧z ≤C x∧(y∧z) holds for all x,y,z.

Local inputs:
- `papers/bedc/parts/concrete_instances/30_lattice_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/27_preorder_namecert_construction.tex`

Rationale:
Surfaced in Turn 1 as the explicitly named smallest Lean-facing test lemma before applying POSetUp antisymmetry. It deserves its own loop because it isolates the preorder-transitivity and meet-bound dependency without using antisymmetry, join fields, commutativity, idempotence, or absorption, and it is not the same object as the full classifier-level associativity target B-26.

---

### B-65 - Directed join associativity comparison from bounds

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Directed join associativity comparison from bounds |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 7/10 |

Problem:
Under a LatticeUp carrier with inherited PreorderUp transitivity and the directional join upper-bound and least-upper-bound implication fields, (x∨y)∨z ≤C x∨(y∨z) holds for all x,y,z.

Local inputs:
- `papers/bedc/parts/concrete_instances/30_lattice_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/27_preorder_namecert_construction.tex`

Rationale:
Surfaced in Turn 1 as the dual join-side comparison to be tested after the meet-directed lemma succeeds. It deserves its own loop because it gives the join-only order comparison underlying classifier-level join associativity while avoiding POSetUp antisymmetry and all meet-side fields, making the LUB dependency independently auditable.

---

### B-66 - Functor composition preservation requires morphism-sameness respect

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (codex) |
| Object | Functor composition preservation requires morphism-sameness respect |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
Under FunctorUp setups for F: C -> D and G: D -> E with raw composition ledgers, if G separates a D-classifier witness supplied by F's composition ledger (i.e. fails morphism-sameness on F's image), then the composite functor pair fails the composition-preservation field of the FunctorUp certificate, even though both individual raw composition ledgers exist.

Local inputs:
- `papers/bedc/parts/concrete_instances/37_functor_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/36_category_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/38_nattrans_namecert_construction.tex`

Rationale:
This is the separation/independence counterpart to B-11 (positive functor composition preservation). Where B-11 proves the composite carries the certificate when both factors do, this candidate isolates exactly which field is required: morphism-sameness respect by G on F's image. It pinpoints the concrete failure mode when the abstract obligation is dropped, mirroring the pattern set by B-18/B-20/B-24 (independence theorems for stability fields). The functor chapter is currently 100% definitions (per B-11 rationale); a finite-construction counterexample here would harden the boundary and supply a directly formalizable Lean target distinct from the positive theorem in B-11. Not a paraphrase of any existing BOARD entry: B-11 is positive preservation, this is negative-without-the-extra-hypothesis. Not present in paper coverage (no thm/lem/cor:functor-composition-* labels yet).

---

### B-67 - VecSpace forgets to Module certificate

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | VecSpace forgets to Module certificate |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
If V carries a VecSpaceUp(F,V) certificate over a field F, then dropping the field-specific scalar inverse data while keeping the underlying CommRing of F as the new scalar source leaves carrier, source, pattern, classifier, stability, and ledger fields that form a ModuleUp(R,V) certificate.

Local inputs:
- `papers/bedc/parts/concrete_instances/22_vecspace_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/21_module_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/20_field_namecert_construction.tex`

Rationale:
22_vecspace_namecert_construction.tex:4 explicitly states VecSpaceUp 'is the specialization of ModuleUp to the case where the scalar ring satisfies FieldUp. No new fields are required beyond the module ones; the change is the strengthened scalar source.' This is a paper-level statement of forgetful inheritance, but def:vecspace-stability-certificate at line 408 just lists fields without lifting the projection to a labeled proposition. Verified by Grep: 'forget' in 22_vecspace_namecert_construction.tex returned 0 hits. The two sibling propositions at concrete_instances/17:499 and concrete_instances/19:14 establish the recipe — projecting tuple fields and reusing carrier/operation/classifier.

---

### B-68 - Lattice forgets to Poset certificate

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Lattice forgets to Poset certificate |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
If L carries a LatticeUp(L) certificate, then dropping the meet, join, and bound-characterization fields together with their congruence stability obligations leaves carrier, source, pattern, classifier, ledger, and the inherited preorder-with-antisymmetry stability fields that form a PosetUp(L) certificate over the same carrier and order relation.

Local inputs:
- `papers/bedc/parts/concrete_instances/30_lattice_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/28_poset_namecert_construction.tex`

Rationale:
30_lattice_namecert_construction.tex:4 says LatticeUp 'extends PosetUp with binary meet and join operations'; def:lattice-carrier at line 8 explicitly says 'Use a poset setup extended with meet and join operations carrying bound-characterization proofs'. So the forgetful is a structurally clean projection. Verified by Grep: 'forget' in 30_lattice_namecert_construction.tex returned 0 hits, and grep '\begin{(proposition|theorem)}.*[Ff]orget' across papers/bedc/parts/ returns only the two sibling proofs at 17:499 and 19:14. Distinct from the existing B-07 (idempotence/absorption) and B-25/B-26/B-27/B-29 (commutativity/associativity/opposite absorption/uniqueness) — those derive lattice laws inside the lattice certificate, not a structural projection out.

---

### B-69 - Module forgets to AbGroup certificate

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Module forgets to AbGroup certificate |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 7/10 |

Problem:
If M carries a ModuleUp(R,M) certificate, then dropping the scalar action and its associated stability data (closure, congruence, scalar-action associativity, scalar unit, scalar/module distributivities) leaves carrier, source, pattern, classifier, ledger, and the additive group fields that form an AbGroupUp(M) certificate over the underlying additive carrier.

Local inputs:
- `papers/bedc/parts/concrete_instances/21_module_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/17_abgroup_namecert_construction.tex`

Rationale:
Definition 21:30-42 (Module stability certificate) lists scalar associativity, scalar additivity, module additivity, scalar action congruence, and scalar unit as the scalar-action obligations layered on top of the abelian-group fields. The natural projection drops exactly this layer. Verified by Grep: 'forget' in 21_module_namecert_construction.tex returned 0 hits. The recipe is established at concrete_instances/17_abgroup_namecert_construction.tex:499 (AbGroup forgets to Group). Distinct from the existing B-08/B-19/B-20/B-23/B-24 module candidates, which all reason inside the module certificate (associativity laws, transport, independence) rather than projecting out of it.

---

### B-70 - NatDivides antisymmetry up to history-sameness

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | NatDivides antisymmetry up to history-sameness |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
For unary histories d, e, if NatDivides(d, e) and NatDivides(e, d) both hold, then hsame(d, e).

Local inputs:
- `papers/bedc/parts/concrete_instances/39_prime_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/04_nat_namecert_construction.tex`

Rationale:
39_prime_namecert_construction.tex contains lem:divides-reflexive at line 142 and lem:divides-transitive at line 153, but NO antisymmetry. Verified by Grep across papers/bedc/parts/: 'divid.*antisym|antisym.*divid|NatDivides.*hsame' returned only definitional uses inside def:nat-prime (line 175) and TrialDiv step (line 217), with NO labeled antisymmetry theorem. Antisymmetry is the natural third axiom completing the divisibility preorder on unary naturals into a partial order, and it is logically required to upgrade NatDivides to a preorder/poset certificate via the existing concrete_instances/27 and 28 patterns. The proof recipe: from the two NatMul witnesses NatMul(d, q1, e) and NatMul(e, q2, d), substitution gives NatMul(d, NatMul(q1, q2), d), which forces both q1 and q2 to be Eone(emp) by unary multiplication unit identification — a chain already exposed by lem:nat-mul-total and lem:unit-left-multiplication-reads-back-the-multiplier (line 84).

---

### B-71 - Field forgets to CommRing certificate

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (codex) |
| Object | Field forgets to CommRing certificate |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |

Problem:
Under a FieldUp(F) setup, dropping the nonzero apartness and proof-indexed multiplicative inverse fields yields the CommRingUp(F) source package with the same carrier operations and classifier.

Local inputs:
- `papers/bedc/parts/concrete_instances/20_field_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/19_commring_namecert_construction.tex`

Rationale:
Direct sibling to B-28 (CommRing forgets to Ring) at the next layer of the algebraic forgetful chain. Field-level certificates carry strictly more data than CommRing certificates (nonzero apartness, proof-indexed inverses), and the forgetful projection is the canonical way to license Field-bearing carriers as CommRing inputs to downstream theorems (e.g., module/ring scalar packages). Paper has both def:field-... and def:commring-... certificate definitions but no theorem proves the projection. Distinct from B-28 because the dropped fields are inverse/apartness, not multiplicative commutativity, and the source/target setups are different. Accepted as a clean concrete_instances projection theorem.

---

### B-72 - Ring forgets to AbGroup certificate

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Ring forgets to AbGroup certificate |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 10/10 |
| Novelty | 8/10 |

Problem:
If R carries a RingUp(R) certificate, then dropping multiplication, multiplicative one, and the multiplicative-monoid / distributivity / zero-multiplication stability fields leaves a carrier, source, additive pattern, classifier, additive-stability fields, and additive ledger that form an AbGroupUp(R) certificate, with the carrier, addition, zero, additive inverse, and classifier unchanged.

Local inputs:
- `papers/bedc/parts/concrete_instances/18_ring_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/17_abgroup_namecert_construction.tex`
- `lean4/BEDC/Derived/RingUp.lean`
- `lean4/BEDC/Derived/AbGroupUp.lean`

Rationale:
The Ring stability certificate at 18_ring_namecert_construction.tex:191-203 lists 'additive abelian-group laws' as its first stability item, mirroring the 'all group stability fields' phrasing that powers prop:abgroup-forgets-group-certificate at 17_abgroup_namecert_construction.tex:499-501. Grep for 'forgets' across papers/bedc/parts/ returns only commring-forgets-ring (19_commring_certificate_scaffold.tex:14), abgroup-forgets-group (17_abgroup:499), module-forgets-abgroup (21_module:371), vecspace-forgets-module (22_vecspace:436), and field-forgets-commring (field/20_field_certificate_record.tex:105). No 'ring-forgets' label exists anywhere in papers/ or lean4/. The chain Field -> CommRing -> Ring -> AbGroup -> Group is broken at exactly one link (Ring -> AbGroup); 25_polynomial_namecert_construction.tex repeatedly invokes 'additive ring fields retained in def:ring-stability-certificate' (lines 520, 551, 660, 718) without being able to cite a forget proposition, evidence the gap is real and load-bearing.

---

### B-73 - Module forgets to Ring certificate (scalar projection)

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Module forgets to Ring certificate (scalar projection) |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 10/10 |
| Novelty | 8/10 |

Problem:
If M carries a ModuleUp(R, M) certificate, then dropping the additive carrier M, vector addition, vector zero, vector negation, the scalar action smul, and the action-shaped stability and ledger rows leaves a carrier, source, ring pattern, classifier, ring stability fields, and ring ledger that form a RingUp(R) certificate, with R's operations and classifier unchanged.

Local inputs:
- `papers/bedc/parts/concrete_instances/21_module_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/18_ring_namecert_construction.tex`
- `lean4/BEDC/Derived/ModuleUp.lean`
- `lean4/BEDC/Derived/RingUp.lean`

Rationale:
The proof of prop:module-forgets-abgroup-certificate (21_module_namecert:371-401) explicitly exposes the existing structure: 'the source side of the module certificate is a certified RingUp(R) together with a certified AbGroupUp(M) sharing the scalar action'. So the scalar-projection forget keeps an already-certified RingUp witness, dual to the established additive-projection forget. Grep for 'module.*forgets|forgets.*ring' in papers/bedc/parts/ returns only commring-forgets-ring and module-forgets-abgroup; the scalar-projection direction is absent. The gap is not hidden under the AbGroup forget because the two forgets project to disjoint halves of the module pair (R, M).

---

### B-74 - POSet forgets to Preorder certificate

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | POSet forgets to Preorder certificate |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 10/10 |
| Novelty | 7/10 |

Problem:
If C carries a POSetUp(C) certificate, then dropping the antisymmetry field and its compatibility data with relation congruence leaves a carrier, source, pattern, classifier, preorder stability fields, and ledger that form a PreorderUp(C) certificate, with the relation, classifier, and carrier unchanged.

Local inputs:
- `papers/bedc/parts/concrete_instances/28_poset_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/27_preorder_namecert_construction.tex`
- `lean4/BEDC/Derived/PreorderUp.lean`

Rationale:
POSet stability certificate at 28_poset_namecert_construction.tex:206-214 explicitly lists 'all preorder stability fields' as its first item, plus antisymmetry and compatibility, mirroring exactly the structure of prop:abgroup-forgets-group-certificate (drop commutativity field). Preorder obligations are at 27_preorder_namecert_construction.tex:500-503. Grep 'poset.*forgets|forgets.*preorder' returns 0 matches in papers/. The Lean side has PreorderUp.lean but no POSetUp.lean (so this lane is paper-only as expected for bedc-deep). This is the order-theoretic analogue of the algebraic forget chain that already covers AbGroup -> Group, CommRing -> Ring, Field -> CommRing, Module -> AbGroup, VecSpace -> Module.

---

### B-75 - TotalOrder forgets to POSet certificate

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | TotalOrder forgets to POSet certificate |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 7/10 |

Problem:
If C carries a TotalOrderUp(C) certificate, then dropping the trichotomy comparison data, the strict-order-to-apartness field, the comparison-stability-under-classifier-replacement row, and any strict-comparison transitivity entries leaves a carrier, source, pattern, classifier, poset stability fields, and ledger that form a POSetUp(C) certificate, with the relation, classifier, and carrier unchanged.

Local inputs:
- `papers/bedc/parts/concrete_instances/29_totalorder_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/28_poset_namecert_construction.tex`

Rationale:
TotalOrder stability certificate at 29_totalorder_namecert_construction.tex lists 'all poset stability fields' as item 1, then strict-order-to-apartness, trichotomy, comparison stability, and strict-transitivity. Existing board entry B-13 ('Total order trichotomy reduces classifier fields') addresses the *abstract reduction* of the classifier under trichotomy, not the structural forget that drops trichotomy and comparison data. Grep for 'totalorder.*forgets|forgets.*poset' returns 0 matches anywhere in papers/. Distinct from B-13 because B-13 keeps trichotomy and uses it to *re-express* the classifier; this candidate *drops* trichotomy and projects to the bare poset certificate, which is the canonical mathematical forgetful functor.

---

### B-76 - Group forgets to Monoid certificate

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Group forgets to Monoid certificate |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
If C carries a GroupUp(C) certificate, then dropping the inverse-operation data, the inverse-related stability rows (left/right inverse and inverse congruence), and the inverse ledger entries leaves carrier, source, pattern, classifier, monoid stability fields, and monoid ledger that form a MonoidUp(C) certificate with carrier C, multiplication, identity e, and classifier unchanged.

Local inputs:
- `papers/bedc/parts/concrete_instances/16_group_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/15_monoid_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/group/namecert_construction_core/02_certificate.tex`
- `papers/bedc/parts/concrete_instances/group/16_group_certificate_tail.tex`

Rationale:
Forgetful-chain blindspot at the bottom of the algebraic ladder. The board has shipped the full upper chain — VecSpace→Module (B-67), Module→AbGroup (B-69), Module→Ring (B-73), Ring→AbGroup (B-72), AbGroup→Group (B-53), CommRing→Ring (B-28), Field→CommRing (B-71), Lattice→Poset (B-68), Poset→Preorder (B-74), TotalOrder→Poset (B-75) — but has never closed Group→Monoid even though both chapters carry the full certificate-obligations machinery: 15_monoid_namecert_construction.tex has \label{def:monoid-source-specification}, \label{def:monoid-stability-certificate}, \label{def:monoid-certificate-obligations}, while group/16_group_certificate_tail.tex has \label{def:group-certificate-obligations} and group/namecert_construction_core/02_certificate.tex has \label{def:group-source-specification}, \label{def:group-pattern-specification}, \label{def:group-classifier-specification}, \label{def:group-stability-certificate}. The pattern matches B-72 verbatim (drop one operation + its stability rows, retain the rest).

---

### B-77 - NatDivides transports along divisor history-sameness

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | NatDivides transports along divisor history-sameness |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
Under the unary-multiplication setup, if NatDivides(d, e) and hsame(d, d'), then NatDivides(d', e).

Local inputs:
- `papers/bedc/parts/concrete_instances/39_prime_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/04_nat_namecert_construction.tex`

Rationale:
Companion-stability gap in the divisibility relation. 39_prime_namecert_construction.tex defines 'NatDivides' (\label{def:nat-divides}) and ships 'Divisibility is reflexive on the unit and on every unary history' (\label{lem:divides-reflexive}), 'Divisibility is transitive' (\label{lem:divides-transitive}), and after B-70 'Divisibility antisymmetry up to history-sameness' (\label{thm:nat-divides-antisymmetry-hsame}). A reflexive/transitive/antisymmetric relation modulo hsame must be transport-stable on each side, but no theorem says so explicitly: grep for 'NatDivides.*transport|divides.*hsame.*transport' in the file returns 0 hits. This is the standard companion to the antisymmetry result completed at B-70 and would unblock any future theorem stating divisibility as a typed classifier on hsame-quotient classes. The 04_nat chapter itself has zero board coverage besides the indirect hit at B-70 which inserted into 39_prime instead.

---

### B-78 - Concrete unary-history magma classifier carrier-aware reflexivity

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Concrete unary-history magma classifier carrier-aware reflexivity |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
Under the concrete unary-history magma instance, if UnaryHistory(h), then R_U(h, h) where R_U(x,y) := UnaryHistory(x) ∧ UnaryHistory(y) ∧ hsame(x, y).

Local inputs:
- `papers/bedc/parts/concrete_instances/56_magma_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/57_semigroup_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/15_monoid_namecert_construction.tex`

Rationale:
Topic-coverage blindspot at the algebraic ladder root. The Magma chapter (56_magma_namecert_construction.tex) ships exactly one theorem — 'Concrete unary-history magma laws' (closure + binary congruence) — and its \section{The certificate} block is empty. The classifier R_U is defined and the laws theorem references reflexivity of hsame in passing, but the carrier-aware reflexivity R_U(h,h) is not a theorem of the chapter. The same chapter's neighbour 57_semigroup_namecert_construction.tex also has only its 'laws' theorem and an empty certificate section, and 15_monoid_namecert_construction.tex picks up identity uniqueness/left-right identity but never proves the magma-level reflexivity it inherits. The board has touched no algebraic-ladder content below 17_abgroup; this is the simplest single-implication theorem in those chapters.

---

### B-79 - NatDivides transports along dividend history-sameness

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (codex) |
| Object | NatDivides transports along dividend history-sameness |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 6/10 |

Problem:
If NatDivides(d,e) and e ~ e', then NatDivides(d,e').

Local inputs:
- `papers/bedc/parts/concrete_instances/39_prime_namecert_construction.tex`
- `lean4/BEDC/Derived/PrimeUp.lean`

Rationale:
Direct symmetric counterpart to the already-proven thm:nat-divides-divisor-hsame-transport (transport on the divisor d), filling the missing dividend/product side. The 2-sided transport is currently only listed as a thm:prime-namecert obligation (line 358) without a standalone theorem; this candidate closes that gap. The supporting lemma chain on the divisor side uses lem:nat-mul-multiplicand-hsame-transport, so the dividend side will likely require a parallel nat-mul product-side hsame-transport lemma — non-trivial enough to deserve its own loop. No BOARD entry currently covers NatDivides transport.

---

### B-80 - Module zero-action annihilation

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | Module zero-action annihilation |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
Under ModuleUp(R,M) with distributivity, scalar action congruence, ring zero, and additive cancellation in M, then 0_R ⊙ m ∼M 0_M and r ⊙ 0_M ∼M 0_M for all carried r,m.

Local inputs:
- `papers/bedc/parts/concrete_instances/21_module_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/18_ring_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/17_abgroup_namecert_construction.tex`

Rationale:
Module章节缺乏零标量/零向量湮灭的派生定理。区别于 B-08 / B-19 / B-20 / B-23 / B-24 这一组围绕 scalar associativity 与代表元稳定性/独立性的 module 目标:此候选不依赖 associativity field, 而是从分配律和加法消去得到零作用. 是 LinMap 零保持 (候选 3) 与矩阵零行列运算的 prerequisite.

---

### B-81 - VecSpace module-fragment projection

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | VecSpace module-fragment projection |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |

Problem:
Under VecSpaceUp(F,V) with FieldUp(F) projected to RingUp(F), forgetting inverse-enabled scalar reasoning yields a ModuleUp(F,V) with the same carrier, scalar action, and classifier.

Local inputs:
- `papers/bedc/parts/concrete_instances/22_vecspace_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/21_module_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/20_field_namecert_construction.tex`

Rationale:
VecSpace 章节明确把自身定位为 Module↑ 在 scalar source 为 Field 时的 specialization, 但 module fragment 投影未独立成定理. 与 B-28 (CommRing→Ring) 是同 pattern 的 forgetful certificate 但作用于不同 setup, 是 LinMap / Mat 章节使用 vector-space 输入时的 prerequisite, 落在 module-stack 中独立的一格.

---

### B-82 - LinearMap zero preservation from additivity

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | LinearMap zero preservation from additivity |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
Under LinMapUp(V,W) with f preserving addition and W's AbGroup additive cancellation, then f(0_V) ∼W 0_W.

Local inputs:
- `papers/bedc/parts/concrete_instances/23_linearmap_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/21_module_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/17_abgroup_namecert_construction.tex`

Rationale:
LinMap stability certificate 列了 zero preservation derived from linearity 这一字段, 但只在 singleton empty-history 实例下 instantiated, 一般 LinMap 上未证. 是 LinMap composition / identity law 与 module zero-action 的下游应用, 不与 BOARD 任何条目重复.

---

### B-83 - LinearMap composition classifier congruence

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | LinearMap composition classifier congruence |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
Over a common scalar source with Module/VecSpace carriers U,V,W, if f∼f′ as U→V LinMaps and g∼g′ as V→W LinMaps pointwise, then g∘f and g′∘f′ are LinMap carriers with the same pointwise classifier.

Local inputs:
- `papers/bedc/parts/concrete_instances/23_linearmap_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/22_vecspace_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/21_module_namecert_construction.tex`

Rationale:
B-11 是 Functor composition hom-carrier 关闭, 这是 LinMap 上的 pointwise classifier congruence —— 同 pattern, 不同 theory: 一个走 categorical hom-carrier, 一个走 module-style pointwise scalar classifier. LinMap 章节当前只有 singleton composition collapse, 缺一般合成 congruence, 是 LinMap stability certificate 列出的 identity-and-composition closure 字段所要求的.

---

### B-84 - Matrix identity multiplication unit

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | Matrix identity multiplication unit |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 9/10 |

Problem:
Under MatUp(n,m,R) with finite-index sum certificate, scalar 0/1 laws, and Kronecker-delta identity matrix closure, then I_n · M ∼Mat M and M · I_m ∼Mat M for every carried matrix M.

Local inputs:
- `papers/bedc/parts/concrete_instances/24_matrix_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/19_commring_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/04_nat_namecert_construction.tex`

Rationale:
Matrix 章节当前只覆盖 singleton empty-history matrix laws 与 append/continuation 精确性, 没有 identity-matrix 单位律. 是 multiplication closure 字段的极值版本, 也是 Mat↑ 接口必备的 structural theorem; 比矩阵结合律小, 主要走有限指标析取与 scalar 0/1.

---

### B-85 - FPS Cauchy product classifier congruence

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | FPS Cauchy product classifier congruence |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
Under FPSUp(R), if F∼FPS F′ and G∼FPS G′ coefficientwise scalar-classified, then the Cauchy product satisfies F⊙G ∼FPS F′⊙G′.

Local inputs:
- `papers/bedc/parts/concrete_instances/26_fps_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/19_commring_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/04_nat_namecert_construction.tex`

Rationale:
FPS 章节当前定理只覆盖 singleton zero-FPS 的 law package 和 classifier exactness, Cauchy product 仅作为 closure obligation 出现, 没有一般 product congruence. 区别于 B-22 (polynomial multiplication zero-tail invariance) 的 finite-list-trim 设置, 这里走形式幂级数的 coefficientwise scalar congruence, 不依赖 trim. 是 FPS↑ 的核心 operation-congruence theorem.

---

### B-86 - Equivalence-closure reflection obstruction

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | Equivalence-closure reflection obstruction |
| Layer | proof_obligations |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 9/10 |

Problem:
Without TokUnique or ClosureReflect, there exists a finite TokIntro/psamebase configuration where psameeq(p,q) holds but some introducing signatures s,t fail hsame(s,t), so ExactGlobalizeBase cannot extend to eq-closure exactness.

Local inputs:
- `papers/bedc/parts/proof_obligations/package_token_policy.tex`
- `papers/bedc/parts/proof_obligations/exact_globalize.tex`
- `papers/bedc/parts/proof_obligations/package_sameness_design.tex`

Rationale:
B-16 是正向: 在 concrete TokIntro 下 psame 反射 hsame; 此候选反向 obstruction: 显式给出 finite counterexample 证明 TokUnique / ClosureReflect 是 local-to-global exactness 的必要边界, 是 Corollary 69.6 的 counterexample counterpart. 与 paper 中现有 token-policy 引理不重复, 且支撑 package_token_policy 章节作为 boundary statement 的论证强度.

---

### B-87 - VecSpace additive carrier projection

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (codex) |
| Object | VecSpace additive carrier projection |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 6/10 |

Problem:
Under VecSpaceUp(F,V), composing the vector-space-to-module fragment projection with the module-to-additive-group reduct yields an AbGroupUp(V) certificate over the same carrier and additive operations.

Local inputs:
- `papers/bedc/parts/concrete_instances/22_vecspace_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/21_module_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/17_abgroup_namecert_construction.tex`

Rationale:
Two-stage forgetful certificate (VecSpace -> Module -> AbGroup) targeting the actively edited 22_vecspace_namecert_construction chapter (per git status). Distinct from B-28 (CommRing -> Ring) because it transits through the module-fragment projection, exercising both the Module reduct and the AbGroup base specification rather than a single obligation drop. Provides a reusable handle for any later VecSpace theorem that needs the additive subcertificate without re-deriving it through Module each time.

---

### B-88 - NatMul right unit projection

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | NatMul right unit projection |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
For every unary history d, if NatMul(d, Eone(emp), n), then hsame(n, d).

Local inputs:
- `papers/bedc/parts/concrete_instances/39_prime_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/04_nat_namecert_construction.tex`

Rationale:
39_prime_namecert_construction.tex:84-91 proves NatMul_unit_left_hsame for the LEFT unit (1·q = q). The dual right-unit theorem (d·1 = d) is missing both from the paper and from lean4/BEDC/Derived/PrimeUp.lean (greppable). Single-implication, mechanically derivable by NatMul_succ_inversion + NatMul.zero inversion + Cont(emp, d, d). This pair (with the absorption candidate above) closes the unit/zero ledger for NatMul, which the entire prime/p-adic/factorization stack downstream silently assumes.

---

### B-89 - Constant complex sequence has constant complex limit

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Constant complex sequence has constant complex limit |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 10/10 |

Problem:
For every complex history z, if the constant sequence s(n):=z and trivial modulus N(k):=emp form a regular complex sequence (lem:cplx-constant-regular), then CplxLim(s, N, z, M_const) holds with the trivial limit modulus M_const(k):=emp.

Local inputs:
- `papers/bedc/parts/concrete_instances/40_complex_limit_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/14_complex_namecert_construction.tex`

Rationale:
Chapter 40 (complex limit) has 15 theorems/12 definitions and is one of seven complex-analysis chapters (40-44, 52-54) that have ZERO completed targets — a major topic blindspot. 40:237-246 proves that the constant sequence is regular, but no theorem evaluates the limit of the constant sequence — the most basic CplxLim instance is missing. Single-implication, follows from CplxDist(z,z,append(z,z)) being trivially within any 2^{-k} tolerance. Closing this opens the complex-analysis chapters to the loop with the easiest possible foothold; the existing B-15 (real-history-sameness under limit transport) crashed and never produced LaTeX, so analytic-limit content remains entirely unwritten.

---

### B-90 - Geometric bound persists when radius shrinks

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Geometric bound persists when radius shrinks |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 9/10 |

Problem:
For coefficients a, unary radius histories r, r' with NatUnaryStrictPrefix(r', r), and unary constant K, if GeomBound(a, r, K), then GeomBound(a, r', K).

Local inputs:
- `papers/bedc/parts/concrete_instances/41_convergence_radius_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/04_nat_namecert_construction.tex`

Rationale:
Chapter 41 (convergence radius) has 8 theorems / 9 definitions, never targeted. 41:112-132 (`GeomBound_radius_constant_continuation_closed`) proves closure under generic continuation perturbations of the radius, but the natural monotone consequence — shrinking the radius preserves the bound — is not isolated as a theorem. The bound `|a_n|·r^n ≤ K` only gets easier when r decreases unarily, and Cauchy-Hadamard (41:220) and absolute-convergence-inside-disk (41:228) implicitly need radius monotonicity. Single-implication. Opens the convergence-radius chapter.

---

### B-91 - Adjunction triangle carrier swap symmetry

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Adjunction triangle carrier swap symmetry |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 10/10 |

Problem:
If AdjunctionTriangleCarrier(left, right, object, unit, counit, leftLeg, rightLeg), then AdjunctionTriangleCarrier(right, left, object, counit, unit, rightLeg, leftLeg).

Local inputs:
- `papers/bedc/parts/concrete_instances/85_adjunction_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/38_nattrans_namecert_construction.tex`

Rationale:
Chapter 85 (adjunction) has 9 theorems but never targeted. The advanced category-theoretic chapters 83-88 are mostly empty (83 catlimit, 84 catcolimit, 86 monad, 87 yoneda, 88 equivcat are 10-line stubs — only 85 has substrate). 85:100-135 defines AdjunctionTriangleCarrier and proves empty-roundtrip determinacy, but the basic carrier-level symmetry under data-swap is missing — required for any later left/right symmetric reasoning about adjunctions. Single-implication, definitionally follows from the symmetric structure of the two prefix natural-transformation components and the two ContR ledgers. Opens the only category-theoretic chapter that has substrate beyond functor/nattrans.

---

### B-92 - Padic prime scale at unit exponent reads back the prime

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Padic prime scale at unit exponent reads back the prime |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 9/10 |

Problem:
For every history p with NatPrime(p), PadicPrimeScale(p, Eone(emp), p) holds.

Local inputs:
- `papers/bedc/parts/concrete_instances/78_padic_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/39_prime_namecert_construction.tex`

Rationale:
Chapter 78 (p-adic) has 7 theorems but is otherwise a stub between section 6 (carrier) and section 9 (certificate) — never targeted. 78:9-15 defines PadicPrimeScale and 78:123-133 proves the empty-exponent case PadicPrimeScale(p, emp, emp) (i.e., p^0 readback). The dual unit-exponent case PadicPrimeScale(p, Eone(emp), p) (i.e., p^1 readback) is missing, even though it is the next constructor of NatMul and the prerequisite of any p-adic valuation computation. Single implication, derives from NatMul.succ over NatMul.zero via Cont(emp, p, p) plus the prime witness for the carrier field. Opens the p-adic chapter at its weakest current edge.

---

### B-93 - Ring zero absorption from distributivity

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | Ring zero absorption from distributivity |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
在 RingUp(R) setup 下，additive cancellation 与左右分配律推出 0_R·x ∼R 0_R 且 x·0_R ∼R 0_R。

Local inputs:
- `papers/bedc/parts/concrete_instances/18_ring_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/17_abgroup_namecert_construction.tex`

Rationale:
Classical foundational ring theorem missing from BOARD and not in paper labels (no zero-absorption / annihilation theorem labels visible in the ring or abgroup definition lists). It is a clean implication "distributivity + additive cancellation ⇒ zero-times-anything" expressible at the certificate level, and serves as a prerequisite for module/matrix targets like B-08, B-23 and the proposed matrix-associativity site without overlapping any of them.

---

### B-94 - Field nonzero product rigidity

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | Field nonzero product rigidity |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
在 FieldUp(F) setup 下，NonZero(x) 与 NonZero(y) 推出 NonZero(x·y)。

Local inputs:
- `papers/bedc/parts/concrete_instances/20_field_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/18_ring_namecert_construction.tex`

Rationale:
def:field-zero-apartness exists but the no-zero-divisor theorem is not stated. Single implication of the right shape, lives squarely in concrete_instances/field, and is the natural extension of the proposed ring zero absorption target. Distinct from the various field-rat-denominator definitions, none of which capture multiplicative rigidity at the certificate level.

---

### B-95 - Rational scaling invariance

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | Rational scaling invariance |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 9/10 |

Problem:
在 RatUp setup 下，若 (n,d) admissible 且 k 被分类为非零，则 (n,d) ∼Q (k·n,k·d)。

Local inputs:
- `papers/bedc/parts/concrete_instances/12_rat_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/20_field_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/18_ring_namecert_construction.tex`

Rationale:
Rat chapter has stability + denominator continuation definitions but no scaling-invariance theorem label. Concrete one-line implication that classifies rational representatives modulo nonzero common-factor scaling, sitting downstream of the proposed field nonzero rigidity. Not paraphrased by any existing BOARD entry, and a useful prerequisite for any later normalization or canonical-representative target.

---

### B-96 - LinearMap composition certificate

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | LinearMap composition certificate |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 10/10 |
| Novelty | 9/10 |

Problem:
在同一 R 上的 ModuleUp(M),(N),(P) setup 下，LinearMapCert(f:M→N) 与 LinearMapCert(g:N→P) 推出 LinearMapCert(g∘f)。

Local inputs:
- `papers/bedc/parts/concrete_instances/22_linearmap_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/21_module_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/19_commring_namecert_construction.tex`

Rationale:
Linearmap chapter is definition-only at the certificate level (carrier/source/classifier/stability) and BOARD has no morphism-level closure target for modules. Map-level analogue of B-11 (functor composition) and B-14 (nattrans composition), giving the missing structural-closure theorem for the linearmap layer and a natural sibling to the module-scalar targets B-08/B-23 without duplicating them.

---

### B-97 - Matrix multiplication associativity from finite folds

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | Matrix multiplication associativity from finite folds |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 9/10 |

Problem:
在 MatrixUp over RingUp(R) setup 下，匹配维度且 finite additive scalar fold 满足重排稳定性时，(A·B)·C ∼M A·(B·C)。

Local inputs:
- `papers/bedc/parts/concrete_instances/23_matrix_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/18_ring_namecert_construction.tex`

Rationale:
def:finite-additive-scalar-fold exists, indicating the fold infrastructure is already on paper, but no matrix theorem is on BOARD or in the paper-label set. Concrete implication tying ring distributivity + finite-fold rearrangement to matrix associativity at the classifier level. Distinct from polynomial multiplication (B-09 / B-22 / B-30) because the obligation is double-finite-sum reordering, not coefficient-tail trimming.

---

### B-98 - Metric ball budget composition

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | Metric ball budget composition |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 7/10 |

Problem:
在 MetricUp(X) setup 下，d(x,y)≤r 与 d(y,z)≤s 推出 d(x,z)≤r+s。

Local inputs:
- `papers/bedc/parts/concrete_instances/32_metric_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/31_interval_namecert_construction.tex`

Rationale:
Triangle-style obligation is presumably internal to the metric stability certificate, but no derived budget-composition theorem is on BOARD or surfaced as a paper label. Concrete classifier-level implication, sits in metric chapter, acts as the metric-side counterpart of B-10 (interval nested refinement) and is a genuine prerequisite for B-12 (continuous modulus composition) rather than a paraphrase of either.

---

### B-99 - Compact finite-refinement flattening

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | Compact finite-refinement flattening |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
在 CompactUp(K) setup 下，若 finite refinement chain 的每个 cell 又有 finite refinement chain，则 flatten 后仍为同一 source 的 finite refinement chain 且保持 locatedness classifier。

Local inputs:
- `papers/bedc/parts/concrete_instances/33_compact_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/32_metric_namecert_construction.tex`

Rationale:
Compact chapter exposes finite-refinement-chain, located-refinement-chain, finite-net, two-step-factor definitions but no multiscale-induction theorem is on BOARD. Concrete closure statement "two layers of finite refinement collapse to one" with locatedness preservation, distinct from continuous-modulus or metric-budget targets.

---

### B-100 - List append left cancellation with public prefix

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | List append left cancellation with public prefix |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
在 ListUp(A) setup 下，若 length(xs) 可公开读回且 xs++ys ∼L xs++zs，则 ys ∼L zs。

Local inputs:
- `papers/bedc/parts/concrete_instances/11_list_namecert_construction.tex`
- `papers/bedc/parts/core/03_relational_extension_and_continuation.tex`

Rationale:
Framed-list public-length readback and spine-representation are on paper as definitions, and cor:external-append-bit-tail-equality is bit-tail-specific rather than a general append cancellation. Concrete implication using public length to slice the spine and transport equality through the prefix; not duplicated by polynomial trim/zero-tail targets (B-21 / B-22 / B-30 / B-31), which are about coefficient-tail classifier behavior rather than spine-level cancellation.

---

### B-101 - Opposite category certificate

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | Opposite category certificate |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
在 CategoryUp(C) setup 下，反转 hom-carrier 与 composition 得到 CategoryUp(C^op)，identity 与 object classifier 不变。

Local inputs:
- `papers/bedc/parts/concrete_instances/36_category_namecert_construction.tex`

Rationale:
Category chapter is definition-only at the certificate level and BOARD only carries downstream functor (B-11) and nattrans (B-14) composition theorems, never a category-level structural construction. Concrete construction theorem reusing identity and associativity in the reversed direction, providing the duality scaffold under which future opposite-functor / opposite-nattrans targets become natural extensions rather than ad-hoc duplicates.

---

### B-102 - Matrix multiplication classifier congruence

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | Matrix multiplication classifier congruence |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |

Problem:
Under a Mat↑ setup with shared scalar source and dimension compatibility, if A∼A′ and B∼B′ as carrier-pointwise classifier equivalences, then AB and A′B′ are Mat↑ carriers and AB∼A′B′.

Local inputs:
- `papers/bedc/parts/concrete_instances/21_module_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/19_commring_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/17_abgroup_namecert_construction.tex`

Rationale:
Sibling of linear-map composition congruence at the matrix layer. Distinct because the proof must traverse finite-index aggregation, scalar multiplication, additive folds, and pointwise classifier ledger fields rather than function composition congruence. No existing BOARD entry covers Mat↑ and no paper label thm:matrix-* exists. Establishes a computable matrix-layer counterpart to LinMap stability.

---

### B-103 - Finite direct product module descent

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | Finite direct product module descent |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |

Problem:
Under Prod↑ and Module↑ certificates over a common scalar source, pointwise addition and scalar action make Prod↑(M,N) a Module↑ carrier, and componentwise classifier equivalences imply product-carrier classifier equivalence.

Local inputs:
- `papers/bedc/parts/concrete_instances/21_module_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/17_abgroup_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/19_commring_namecert_construction.tex`

Rationale:
Prerequisite for bilinear constructions, matrix column-vector semantics, and categorical product structure on modules. Distinct from B-08 / B-19 / B-23 (which all stay within a single module carrier) — this builds a new module out of two via the product classifier, exercising compatibility between Prod↑ and the algebraic stability fields. No existing BOARD entry covers product-of-modules.

---

### B-104 - Package-token pullback separation

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | Package-token pullback separation |
| Layer | proof_obligations |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
Under PackagePolicy(Π), GapPolicy(Π,D), and a classifier-preserving source map τ:D′→D, if two pulled-back gap ledgers intersect on the same D′-source, then their visible package tokens are psame in the original Π.

Local inputs:
- `papers/bedc/parts/proof_obligations/package_token_policy.tex`
- `papers/bedc/parts/proof_obligations/exact_globalize.tex`
- `papers/bedc/parts/core/08_typed_naming_certificates.tex`

Rationale:
Distinct from B-16 (concrete-term token reflection from package sameness): this candidate is about provenance stability under pullback of source domain via a classifier-preserving map, rather than reducing the abstract policy to a concrete predicate. Tests whether BEDC's provenance layer survives source-domain change exactly. Fills an explicit gap in the package_token_policy / exact_globalize obligation surface.

---

### B-105 - DescentCertificate composition for stable transformations

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | DescentCertificate composition for stable transformations |
| Layer | hardening |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
Under NameCert StableTransformation and DescentCertificate setups, if T:S→R and U:R→Q each preserve the corresponding source/target classifiers, then U∘T preserves the source-to-Q classifier and carries the composite ledger policy.

Local inputs:
- `papers/bedc/parts/core/08_typed_naming_certificates.tex`
- `papers/bedc/parts/concrete_instances/37_functor_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/38_nattrans_namecert_construction.tex`

Rationale:
General composition closure for descent certificates of function-like interfaces — the structural skeleton that B-11 (functor composition closure) and B-14 (nattrans composition naturality) both instantiate. Proving this once would let ContinuousMap↑, Functor↑, NatTrans↑ share the same descent-composition pattern without re-proving classifier preservation per interface. Distinct from B-11 / B-14 because it is the general theorem, not a categorical specialization.

---

### B-106 - Signature append residual exactness under known token component

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | Signature append residual exactness under known token component |
| Layer | core |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
Under BundleAskPolicy(Π,D), BundleAskPolicy(Θ,D), PackagePolicy(BAppend(Π,Θ)), and a known Π-component package token, if two sources have psame appended package tokens and psame Π-component tokens, then their Θ-signatures are sameSigΘ.

Local inputs:
- `papers/bedc/parts/core/08_typed_naming_certificates.tex`
- `papers/bedc/parts/proof_obligations/package_token_policy.tex`
- `papers/bedc/parts/proof_obligations/exact_globalize.tex`

Rationale:
Lifts signature append cancellation from the sameSig layer to the visible package-token layer, giving a residual exactness statement for finite-kernel globalization. No existing BOARD entry treats appended-token cancellation; the paper has bundle-append definitions but no thm/lem with this residual form. Direct downstream consumer for B-16 and the package_token_policy block.

---

### B-107 - Eventually constant complex sequence has constant limit

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (codex) |
| Object | Eventually constant complex sequence has constant limit |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |

Problem:
If a regular complex sequence $s$ is pointwise $\hsame$ to a complex history $z$ above a unary modulus $M$ (i.e. for all $n \geq M$, $s_n \hsame z$), then $\mathsf{CplxLim}(s, N, z, M)$ holds.

Local inputs:
- `papers/bedc/parts/concrete_instances/15_complex_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/13_real_namecert_construction.tex`
- `papers/bedc/parts/core/03_relational_extension_and_continuation.tex`

Rationale:
Lands directly in the existing complex-limit certificate surface (`def:cplx-lim` + classifier/pattern/source/ledger/stability fields are all present, but no proven sufficient condition exists). It supplies the simplest classifier-level entry into `\mathsf{CplxLim}` — a baseline witness construction that any later complex-analytic site (series convergence, holomorphy, Cauchy product) can call as a lemma. Distinct from B-15, which is about transporting `hsame` between two real points under a shared limit interface; here a single sequence collapses to a single classifier witness via pointwise sameness above the modulus, an existence statement rather than a transport. Concrete one-line implication, paper has no `thm:`/`lem:cplx-lim-*` label for this direction, and the modulus structure makes it a self-contained proof site.

---

### B-108 - Adjunction unit-counit carrier swap symmetry

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (codex) |
| Object | Adjunction unit-counit carrier swap symmetry |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 7/10 |
| Novelty | 7/10 |

Problem:
AdjunctionUnitCounitCarrier(p, q, a, unit, counit, left, right) implies AdjunctionUnitCounitCarrier(q, p, a, counit, unit, right, left), and vice versa.

Local inputs:
- `papers/bedc/parts/concrete_instances/37_functor_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/38_nattrans_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/36_category_namecert_construction.tex`

Rationale:
The paper defines `def:adjunction-unit-counit-carrier` and `def:adjunction-triangle-carrier` but no theorem records the standard left/right swap symmetry of an adjunction carrier (the involution that exchanges the role of unit/counit and the two functors). It fits the concrete_instances pattern alongside B-11 (functor composition) and B-14 (nattrans naturality), which similarly take chapters that are 100% definitions and add the first structural theorems. The claim is a single concrete biconditional, not a survey, and is distinct from every existing BOARD entry (none mention adjunctions). It is also not paraphrased by any existing BOARD entry. Risk is low-to-medium: depending on whether the carrier is pure data or carries triangle laws, the proof is either definitional unfolding or a dualization of the triangle equations — both are well-suited for a single deep-reasoning loop.

---

### B-109 - LinearMap identity certificate

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (codex) |
| Object | LinearMap identity certificate |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
Under any ModuleUp(R,M), the identity map on M satisfies LinearMapCert_R(M, M; id) with the inherited classifier and ledger policy.

Local inputs:
- `papers/bedc/parts/concrete_instances/23_linearmap_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/21_module_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/17_abgroup_namecert_construction.tex`

Rationale:
Chapter 23 currently only registers six \leandef definitions (def:linearmap-carrier, def:linearmap-certificate-obligations, def:linearmap-classifier-specification, def:linearmap-ledger-policy, def:linearmap-pattern-specification, def:linearmap-source-specification) with zero theorems. The identity-carries-certificate fact is the foundational counterpart that any category-of-modules style usage needs and is not implied by any module-side BOARD entry (B-08/B-19/B-20/B-23/B-24 are all about scalar associativity or representative transport, not about specific linear maps carrying the certificate). The claim is in single-implication form: ModuleUp(R,M) implies LinearMapCert_R(M,M;id), and lives squarely in concrete_instances. The existing linearmap chapter is already on the working tree (23_linearmap_namecert_construction.tex is modified), making this a natural extension slot.

---

### B-110 - LinearMap composition associativity certificate

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (codex) |
| Object | LinearMap composition associativity certificate |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |

Problem:
For LinearMapCert_R-certified maps f: M -> N, g: N -> P, k: P -> Q over a common scalar source, the two associations ((k . g) . f) and (k . (g . f)) are pointwise classified equal in Q's classifier and the composite carries the linearmap certificate.

Local inputs:
- `papers/bedc/parts/concrete_instances/23_linearmap_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/21_module_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/19_commring_namecert_construction.tex`

Rationale:
No existing BOARD entry covers linearmap composition. B-11 is the analogous theorem at the functor level (HomCarrier composition), but linear maps live one level down on a different carrier (module hom-sets, not category hom-carriers) and need their own pointwise classifier reasoning over the codomain module. The chapter has zero theorems, and composition associativity is a prerequisite for any later category-of-R-modules style construction. Concrete implication form: certified f, g, k imply pointwise classified equality of the two associations. Lands in concrete_instances and adjacent to existing module / linearmap definitions without duplicating module-side B-entries (which are about scalar action laws, not composition).

---

### B-111 - Opposite functor certificate

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (codex) |
| Object | Opposite functor certificate |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
Given a $\FunctorUp$ certificate $F:\mathcal C\to\mathcal D$, the same object and morphism maps yield a $\FunctorUp$ certificate $F^{\mathrm{op}}:\mathcal C^{\mathrm{op}}\to\mathcal D^{\mathrm{op}}$ over the opposite-category certificates.

Local inputs:
- `papers/bedc/parts/concrete_instances/36_category_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/37_functor_namecert_construction.tex`

Rationale:
Chapter 37 is 100% definition-only (per B-11 rationale: 7 def, 0 thm). Existing BOARD touches functors only via composition closure (B-11) and naturality (B-14); duality / opposite-category transport is absent from BOARD and from `paper_coverage` (no `def:category-opposite-*` or `def:functor-op-*` labels). Concrete one-line implication, lives squarely in chapter 37, and exercises the functor stability certificate fields under arrow-reversal — the canonical first duality test in the categorical layer.

---

### B-112 - Opposite natural transformation certificate

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (codex) |
| Object | Opposite natural transformation certificate |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |

Problem:
Given a $\NatTransUp$ certificate $\alpha:F\Rightarrow G$, the same component family yields a $\NatTransUp$ certificate $\alpha^{\mathrm{op}}:G^{\mathrm{op}}\Rightarrow F^{\mathrm{op}}$ over the opposite-functor certificates.

Local inputs:
- `papers/bedc/parts/concrete_instances/36_category_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/37_functor_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/38_nattrans_namecert_construction.tex`

Rationale:
Chapter 38 is also 100% definition-only (per B-14 rationale: 7 def, 0 thm). Sibling to the opposite-functor target but lands on a distinct stability layer: it tests that the naturality square certificate transports under simultaneous arrow-reversal of source and target functors, with $F$ and $G$ swapping roles. Not a paraphrase of B-14 (which is composition-naturality, not duality), and `paper_coverage` shows no existing nattrans-opposite label. Stands on its own as the canonical second duality theorem after the functor case.

---

### B-113 - Polynomial division algorithm well-foundedness

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | Polynomial division algorithm well-foundedness |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 9/10 |

Problem:
If $p, q$ are polynomial spines over a $\CommRingUp$ carrier with $\neg(\PolySame_R(q, \emp))$, then iterated leading-coefficient elimination of $q$ from $p$ terminates in finitely many steps with a quotient and remainder satisfying the standard polynomial division identity.

Local inputs:
- `papers/bedc/parts/concrete_instances/25_polynomial_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/19_commring_namecert_construction.tex`

Rationale:
Polynomial chapter (25_polynomial) currently covers add/multiply/normalize but has no division-with-remainder theorem. Existing polynomial BOARD entries (B-09, B-21, B-22, B-30, B-31) all concern normalization invariance and add/multiply commutativity; none touch on division. This is a foundational well-foundedness obligation requiring a length-decreasing measure under leading-coefficient elimination, and is a prerequisite for any future rational-function, GCD, or factorization work. No paper label of the form thm:polynomial-division exists.

---

### B-114 - CommRing zero-divisor product closure

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | CommRing zero-divisor product closure |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
Under a $\CommRingUp$ carrier with classifier $\sim_R$, if $a$ is a left zero divisor and $b$ is any ring element, then $ab$ is also a left zero divisor (or zero).

Local inputs:
- `papers/bedc/parts/concrete_instances/19_commring_namecert_construction.tex`

Rationale:
CommRing chapter (19_commring) carries the basic ring laws and commutativity but no zero-divisor / integral-domain structure theorems. No existing BOARD entry treats the zero-divisor predicate as a closed structure. This is a foundational closure law that future integral-domain certificates would need to invoke, derived from ring distributivity and classifier transport already provided by the CommRing certificate. No paper label like thm:zero-divisor-* is present.

---

### B-115 - TotalOrder finite minimum element existence

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | TotalOrder finite minimum element existence |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 7/10 |

Problem:
If $L$ is a finite nonempty list of $\TotalOrderUp$ elements, then there exists $m \in L$ such that for every $x \in L$, $m \le x$.

Local inputs:
- `papers/bedc/parts/concrete_instances/29_totalorder_namecert_construction.tex`

Rationale:
TotalOrder chapter (29_totalorder) has the trichotomy and classifier laws, but no theorem about minimum-element extraction from a finite list. B-13 covers trichotomy reduction of the classifier and B-29 covers lattice bound uniqueness — neither addresses list-minimum existence. The proof is constructive (induction on list spine + trichotomy at the cons step), entirely BEDC-clean, and is foundational for any sorting / scheduling / extremization development. No paper label of the form thm:totalorder-min exists.

---

### B-116 - AbGroup torsion element subgroup closure

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | AbGroup torsion element subgroup closure |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
Under an $\AbGroupUp$ carrier, if $a, b$ are torsion elements (each annihilated by some positive integer multiplication), then $a + b$ and $-a$ are also torsion elements.

Local inputs:
- `papers/bedc/parts/concrete_instances/17_abgroup_namecert_construction.tex`

Rationale:
AbGroup chapter (17_abgroup) provides the abelian group laws but contains no torsion-element / torsion-subgroup theorem. The proof requires a NatMul-style witness construction combining the two annihilator orders (lcm-style), which exercises the unary multiplication interface in a new direction. Foundational for any future divisible-group or torsion-free-quotient development. No paper label like thm:torsion-* exists.

---

### B-117 - Functor preserves split monomorphism

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | Functor preserves split monomorphism |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
If $F : \mathcal{C} \to \mathcal{D}$ is a $\FunctorUp$ certificate and $f$ has a left inverse in $\mathcal{C}$, then $F(f)$ has a left inverse in $\mathcal{D}$.

Local inputs:
- `papers/bedc/parts/concrete_instances/37_functor_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/36_category_namecert_construction.tex`

Rationale:
Functor chapter (37_functor) is currently definition-heavy (the basis for B-11's composition-closure target). No theorem covers preservation of split monomorphisms / split epimorphisms. Distinct from B-11 (composition closure of the hom-carrier classifier) and from the existing nat-trans naturality targets (B-14, etc.). The proof goes directly from $F(g \circ f) \sim F(g) \circ F(f)$ plus identity preservation. Pre-requisite for any later preservation-of-iso theorem. No paper label like thm:functor-split-mono exists.

---

### B-118 - Convergence radius monotonicity in coefficient ring inclusion

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | Convergence radius monotonicity in coefficient ring inclusion |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 9/10 |

Problem:
If $R \subseteq R'$ is a $\CommRingUp$ subring inclusion and $f$ is a power series with coefficients in $R$, then the convergence radius of $f$ viewed in $R'$ is at least the convergence radius of $f$ in $R$.

Local inputs:
- `papers/bedc/parts/concrete_instances/41_convergence_radius_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/19_commring_namecert_construction.tex`

Rationale:
Convergence-radius chapter (41_convergence_radius) provides the radius definition and existing convergence-radius targets concern internal stability under coefficient operations. No BOARD entry or paper label addresses transport of the radius along subring/superring inclusion. The witness transports via the inclusion homomorphism preserving partial sums. Genuinely new direction connecting the algebraic forgetful structure of CommRing to the analytic side, with no existing duplicate among the def:conv-rad-* labels (which are definition-only).

---

### B-119 - Pulled-back gap policy preserves coverage and separation

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (codex) |
| Object | Pulled-back gap policy preserves coverage and separation |
| Layer | proof_obligations |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
If GapPol(Π, D) holds and τ : D' → D has a classifier-preserving inverse-image ledger and preserves source admission, then the pulled-back ledger satisfies the coverage and separation obligations over D'.

Local inputs:
- `papers/bedc/parts/proof_obligations/exact_globalize.tex`
- `papers/bedc/parts/proof_obligations/package_token_policy.tex`
- `papers/bedc/parts/proof_obligations/verification_queue.tex`

Rationale:
Sits in proof_obligations alongside B-16 (concrete token reflection) but on a disjoint axis: it lifts an existing definitional primitive (def:classifier-preserving-pullback-ledger) into a coverage+separation transport theorem under a domain morphism. The paper currently defines pullback ledgers, gap policies, and domain-invariance of source admission as separate facts (def:gap-policy, def:classifier-preserving-pullback-ledger, cor:domain-invariance-of-concrete-source-admission), but never composes them into the obvious pullback theorem for GapPol. Concrete enough to drive a single-implication proof loop, and it activates the existing pullback-ledger definition that otherwise has no theorem consumer.

---

### B-120 - Adjunction carrier swap involution

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (codex) |
| Object | Adjunction carrier swap involution |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 7/10 |
| Novelty | 7/10 |

Problem:
Under an AdjunctionUp setup with unit-counit carriers, applying the unit-counit carrier swap twice returns the original carrier ordering up to the adjunction classifier.

Local inputs:
- `papers/bedc/parts/concrete_instances/36_category_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/37_functor_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/38_nattrans_namecert_construction.tex`

Rationale:
Adjunctions are present in the paper only as definitions (def:adjunction-unit-counit-carrier, def:adjunction-triangle-carrier) with zero theorems attached, paralleling the functor/nattrans definition-only chapters that already justified B-11 and B-14. A swap-involution lemma is the natural first structural theorem on the unit-counit carrier and is not a notation variant of any existing BOARD entry (B-11 is functor composition closure, B-14 is nattrans composition naturality, neither touches adjunction swap). The claim is a single equation under a concrete setup, satisfying the implication-form requirement, and gives the formalization lane a concrete site to attach \leanchecked once a Lean target lands.

---

### B-121 - LinearMap identity unit laws

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (codex) |
| Object | LinearMap identity unit laws |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 7/10 |
| Novelty | 6/10 |

Problem:
If LinearMapCert_R(M,N;f) holds, then id_N ∘ f and f ∘ id_M carry LinearMap certificates and are related to f by the pointwise LinearMap classifier.

Local inputs:
- `papers/bedc/parts/concrete_instances/23_linearmap_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/21_module_namecert_construction.tex`

Rationale:
Chapter 23 already proves id is a linear map (thm:module-linearmap-identity-certificate) and composition is a linear map (thm:module-linearmap-composition-certificate, thm:linmap-composition-classifier-congruence), but the explicit categorical unit laws id_N ∘ f ∼ f and f ∘ id_M ∼ f under the pointwise LinearMap classifier are not stated. This completes the categorical-unit fragment of the LinearMap certificate algebra in a way parallel to B-11 (functor composition closure) and B-14 (nattrans composition naturality), and is a clean follow-up to the identity and composition certificates already in the chapter. Proof reduces to point evaluation plus classifier reflexivity, but the standalone statement is currently absent. Borderline novelty because it is a thin corollary of existing theorems, but it fills a precise categorical-law gap.

---

### B-122 - Module faithful action characterization via annihilator

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | Module faithful action characterization via annihilator |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
Under a $\ModuleUp(R,M)$ certificate, the scalar action is faithful (distinct scalars induce classifier-distinguishable module endomorphisms) iff for every $r:R$, $(\forall m:M, r\cdot m \hsame_M 0_M) \implies r \hsame_R 0_R$.

Local inputs:
- `papers/bedc/parts/concrete_instances/21_module_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/19_commring_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/17_abgroup_namecert_construction.tex`

Rationale:
Module chapter (21_module) currently has scalar associativity/compatibility (B-08, B-19, B-23) and independence obstructions (B-20, B-24) but no theorem characterizing classifier-level faithfulness. The iff form is a clean implication-pair statable purely with existing $\hsame_R$ / $\hsame_M$ classifiers (no need to introduce ideal structure as a primitive — the annihilator can be left as the predicate body). It fills a structural gap orthogonal to all existing module BOARD entries and is a prerequisite for any later torsion-free / projective module obligations.

---

### B-123 - List length subadditivity under append

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | List length subadditivity under append |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 6/10 |

Problem:
For all unary-spine lists $\ell_1, \ell_2$ in the public list carrier, $\mathsf{length}(\mathsf{append}(\ell_1, \ell_2)) \hsame \mathsf{NatAdd}(\mathsf{length}(\ell_1), \mathsf{length}(\ell_2))$.

Local inputs:
- `papers/bedc/parts/concrete_instances/11_list_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/11_list_history_semantic_fields_source_refinement.tex`
- `papers/bedc/parts/concrete_instances/04_nat_namecert_construction.tex`

Rationale:
Public framed-list length readback (def:framed-list-public-length-readback) and append are defined, and Nat additive structure (chapter 04) is in place, but there is no theorem connecting list length to NatAdd under append. The identity is foundational for any future induction on list length and bridges the list and nat naming-certificate constructions. The proof is a short induction on $\ell_1$ using empty/cons cases, which makes it a low-risk but high-utility BOARD slot. Distinct from B-100 (list left-cancellation) which addresses head-equality, not length arithmetic.

---

### B-124 - Euclid's lemma: prime divides product implies prime divides factor

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | Euclid's lemma: prime divides product implies prime divides factor |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 7/10 |

Problem:
Under PrimeUp setup, if NatPrime(p) and NatDivides(p, q) where NatMul(a, b, q), then NatDivides(p, a) or NatDivides(p, b).

Local inputs:
- `papers/bedc/parts/concrete_instances/39_prime_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/04_nat_namecert_construction.tex`
- `lean4/BEDC/Derived/PrimeUp.lean`

Rationale:
Lands directly in concrete_instances/39_prime_namecert_construction.tex where the chapter already invokes 'Standard Euclid's-lemma argument' inside thm:ftoa-uniqueness and lists the lemma in def:prime-ledger-policy without giving it a labeled theorem. All prerequisites (NatDivides reflexivity/transitivity, prime-decidable, NatMul shape inversions) are in place. No existing BOARD entry covers prime divisibility distribution over products, and the paper_coverage list shows no `lem:euclid-lemma` or equivalent. Fills a concrete dependency gap that the FTOA chain already silently uses.

---

### B-125 - LinearMap kernel is a sub-module of the source

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | LinearMap kernel is a sub-module of the source |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 9/10 |

Problem:
Under LinearMapCert_R(M, N; f), the predicate Ker(f, x) := (f(x) ~_N 0_N) on carried x:M is closed under module addition, scalar action, and contains 0_M.

Local inputs:
- `papers/bedc/parts/concrete_instances/23_linearmap_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/21_module_namecert_construction.tex`
- `lean4/BEDC/Derived/LinearMapUp.lean`
- `lean4/BEDC/Derived/ModuleUp.lean`

Rationale:
Belongs in concrete_instances/23_linearmap_namecert_construction.tex. Existing chapter has thm:linearmap-zero-preservation-from-additivity and the additivity/scalar/zero rows of def:linearmap-stability-certificate but no labeled theorem stating the fiber over 0 forms a sub-module carrier. No BOARD entry currently addresses LinearMap kernel/image structure. The chapter's existing additivity, scalar-compatibility, and zero-preservation rows compose directly via M-classifier transitivity to give the three closure clauses — clean, scope-appropriate target.

---

### B-126 - LinearMap image is a sub-module of the target

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | LinearMap image is a sub-module of the target |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
Under LinearMapCert_R(M, N; f), the predicate Im(f, y) := (∃ carried x:M, f(x) ~_N y) on N is closed under module addition, scalar action, and contains 0_N.

Local inputs:
- `papers/bedc/parts/concrete_instances/23_linearmap_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/21_module_namecert_construction.tex`
- `lean4/BEDC/Derived/LinearMapUp.lean`

Rationale:
Parallel target to the kernel candidate, but on the codomain side. No paper_coverage label matches image/sub-module on linearmap, and no BOARD entry covers it. The witness composition uses M-side additive/scalar closure (def:module-stability-certificate) plus the f-row additivity and scalar-compatibility rows to produce N-side image closure, with zero-preservation giving 0_N ∈ Im(f). Distinct enough from the kernel target because the construction path is existential-witness composition rather than fiber-equation closure.

---

### B-127 - Subgroup intersection is a subgroup

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | Subgroup intersection is a subgroup |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 10/10 |
| Novelty | 8/10 |

Problem:
If H_1 and H_2 are SubgroupCert(G)-carriers of an ambient GroupUp(G), then their pointwise intersection H_1 ∩ H_2 is also a SubgroupCert(G)-carrier (closed under multiplication, inverse, contains identity).

Local inputs:
- `papers/bedc/parts/concrete_instances/58_subgroup_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/16_group_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/group/16_group_centralizer_normalizer.tex`

Rationale:
Lands in concrete_instances/58_subgroup_namecert_construction.tex which currently has only 3 theorems, all centralizer-specific. No BOARD entry covers general subgroup-closure constructions, and no paper_coverage label matches. The proof is conjunction-of-closure-clauses on each axiom; surrounding centralizer/normalizer machinery (thm:group-center-normal-subgroup) confirms the apparatus is ready. Useful as a foundational subgroup-construction theorem that will be reused by later subgroup targets.

---

### B-128 - TotalOrder finite maximum element existence

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (codex) |
| Object | TotalOrder finite maximum element existence |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |

Problem:
Under a concrete TotalOrderUp setup, every nonempty finite list of carrier elements admits an index whose entry is above every entry of the list under the order classifier.

Local inputs:
- `papers/bedc/parts/concrete_instances/29_totalorder_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/28_poset_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/11_list_namecert_construction.tex`

Rationale:
Chapter 29 (concrete totalorder) currently has only definition-level content (def:concrete-singleton-history-totalorder-instance, def:concrete-unary-prefix-totalorder-instance, def:concrete-unary-prefix-totalorder-successor-package) and no labeled theorem stating finite-list operational consequences of the trichotomy/antisymmetry fields. Finite-max existence is the canonical first operational theorem at a totalorder certificate: it consumes only trichotomy and reflexivity, exercises the carrier classifier on a list spine, and produces an index witness usable downstream by sorting/selection certificates. Distinct from B-13 (which reduces classifier fields via trichotomy) and from B-25/B-26 (which target lattice meet/join laws, not totalorder finite-list operations).

---

### B-129 - TotalOrder finite minimum classifier uniqueness

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (codex) |
| Object | TotalOrder finite minimum classifier uniqueness |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 7/10 |
| Novelty | 6/10 |

Problem:
Under a concrete TotalOrderUp setup, any two minimum witnesses of the same nonempty finite carrier list are classifier-equal.

Local inputs:
- `papers/bedc/parts/concrete_instances/29_totalorder_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/28_poset_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/11_list_namecert_construction.tex`

Rationale:
Parallels B-29 (lattice GLB/LUB uniqueness from directional certificates) but in the totalorder + finite-list setting rather than the lattice + binary-meet/join setting: the witness shape is an index of a finite list satisfying a universal lower-bound predicate, and the proof uses trichotomy + antisymmetry rather than directional bound fields. With B-13 occupying the trichotomy-reduction site and the candidate-1 existence theorem occupying the production site, this uniqueness theorem closes the standard existence/uniqueness pair at the totalorder finite-list interface and gives downstream selection/sort interfaces a classifier-stable readback. Borderline novelty against B-29 due to the shared antisymmetry-uniqueness pattern, but the chapter, setup, and witness type all differ.

---

### B-130 - Functor preserves split epimorphism

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (codex) |
| Object | Functor preserves split epimorphism |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 7/10 |

Problem:
If $F:\mathcal C\to\mathcal D$ is a $\FunctorUp$ certificate and $f$ has a right-inverse witness in the source category, then $F_1(f)$ has the mapped right-inverse witness in the codomain category.

Local inputs:
- `papers/bedc/parts/concrete_instances/37_functor_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/36_category_namecert_construction.tex`

Rationale:
Chapter 37 (functor namecert) is currently 100% definition-only (B-11 rationale notes 7 def, 0 thm). The paper already has `def:category-split-monomorphism` so the dual notion of split epimorphism via right-inverse witnesses is natural to introduce, and a Functor preserving such witnesses is a foundational theorem distinct from B-11 (which is about composition of functors preserving the hom-carrier classifier, not about morphism-class preservation). It directly fills a known structural gap in the functor chapter.

---

### B-131 - Functor preserves isomorphism witnesses

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (codex) |
| Object | Functor preserves isomorphism witnesses |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 6/10 |

Problem:
If $f$ carries both a split-monomorphism witness and a split-epimorphism witness in a $\FunctorUp$ source category, then $F_1(f)$ carries the mapped split-monomorphism and split-epimorphism witnesses in the codomain category.

Local inputs:
- `papers/bedc/parts/concrete_instances/37_functor_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/36_category_namecert_construction.tex`

Rationale:
Distinct enough from the split-epi target above because in BEDC's witness style the isomorphism case is the joint preservation of two oriented witness fields rather than the bare conjunction; the proof packages both inverse-side certificate transports together and is the natural target site for `\leanchecked` once the split-mono and split-epi preservation lemmas are in place. Sits in the same definition-only Chapter 37 zone, so it adds usable theorem mass without duplicating B-11 composition or the split-epi target.

---

### B-132 - CommRing subring inclusion via operation-preserving carrier reflection

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (codex) |
| Object | CommRing subring inclusion via operation-preserving carrier reflection |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 7/10 |
| Novelty | 7/10 |

Problem:
If a carrier-reflecting map between two CommRingUp certificates preserves +, ×, 0, 1 up to the target classifier, then it induces a subring-inclusion name certificate over the target package.

Local inputs:
- `papers/bedc/parts/concrete_instances/19_commring_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/18_ring_namecert_construction.tex`
- `papers/bedc/parts/core/08_typed_naming_certificates.tex`

Rationale:
BEDC's concrete_instances layer has many namecerts (Ring, CommRing, Module, Field, Polynomial, …) but very few theorems about morphisms BETWEEN namecerts. The only existing morphism-flavored entry is B-28 (CommRing-to-Ring forgetful projection), which drops multiplicative commutativity over the same carrier. A subring-inclusion certificate is a different and complementary direction: same structure level, smaller carrier, classifier-respecting. It would be the first inclusion-style structural theorem on the board and would supply a reusable construction that downstream targets (e.g., field-of-fractions denominator subring fragments already drafted in def:field-rat-denominator-*) could cite. Grep of paper_coverage shows no thm/lem/cor labeled for subring-inclusion namecerts. Acceptable as a single implication: (carrier-reflecting ∧ operation-preserving map between two CommRingUp packages) ⇒ subring-inclusion namecert over the target.

---

### B-133 - Adjunction triangle carrier-swap involution

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (codex) |
| Object | Adjunction triangle carrier-swap involution |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
Under an adjunction triangle setup, applying the carrier-swap classifier twice to a triangle display yields a display componentwise classifier-same to the original.

Local inputs:
- `papers/bedc/parts/concrete_instances/36_category_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/37_functor_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/38_nattrans_namecert_construction.tex`

Rationale:
The paper introduces def:adjunction-triangle-carrier, def:adjunction-unit-counit-carrier, and def:adjunction-unit-counit-carrier-swap-classifier as definitions, but the paper coverage list contains no theorem/lemma/cor stating that the swap is involutive up to the classifier. Involutivity of the carrier-swap is a basic structural property analogous to B-11 (functor composition closure) and B-14 (NT composition naturality) but for adjunction-level structure, and it does not duplicate any existing BOARD entry. It is a single-implication concrete claim, lands cleanly in concrete_instances, and fills a real gap left by the swap-classifier definition.

---

### B-134 - Monad adjunction-endomorphism semantic name certificate

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Monad adjunction-endomorphism semantic name certificate |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
For a unary prefix history $p$ and unary object $a$, the predicate $M_{p,a}(unit,counit,left,right) :\Leftrightarrow \mathrm{AdjunctionUnitCounitCarrier}(p,p,a,unit,counit,left,right)$ carries a $\mathrm{SemanticNameCert}$ with source = pattern = ledger = $M_{p,a}$ and classifier the componentwise conjunction of $\hsame$ on $unit$, $counit$, $left$, $right$.

Local inputs:
- `papers/bedc/parts/concrete_instances/86_monad_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/85_adjunction_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/38_nattrans_namecert_construction.tex`
- `papers/bedc/parts/core/08_typed_naming_certificates.tex`

Rationale:
86_monad has 11 carrier theorems (lines 9-204) about adjunction-endomorphism degenerate cases (unit, counit, triangle results all collapse to $\emp$ under same-prefix endomorphism), but `\section{The certificate}` at lines 206-208 is *literally empty*. Mirrors the exact pattern that successfully closed for Unit (93:153), Empty, Yoneda (87:178), EquivCat (88:213), and Homology (76:188) — all of which had carrier theorems followed by a single terminal `SemanticNameCert` packaging theorem. Loop has done 5 SemanticNameCert wrap-ups in adjacent chapters but never opened 86_monad — see write counts: monad=0, adjunction=2, nattrans=2.

---

### B-135 - Cohomology cocycle predicate semantic name certificate

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Cohomology cocycle predicate semantic name certificate |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 10/10 |
| Novelty | 9/10 |

Problem:
Under bilateral cocycle axis-cancel (\autoref{thm:cohomology-cocycle-bilateral-axis-cancel}) and cocycle append closure (\autoref{thm:cohomology-cocycle-append-closed}), the cocycle predicate $C_d$ carries a $\mathrm{SemanticNameCert}$ with source = pattern = ledger = $C_d$ and classifier $\hsame$.

Local inputs:
- `papers/bedc/parts/concrete_instances/77_cohomology_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/76_homology_namecert_construction.tex`
- `papers/bedc/parts/core/08_typed_naming_certificates.tex`

Rationale:
77_cohomology has 18 cocycle theorems (axis-cancel left/right/context/bilateral, append closure, prepend axis closure, transport variants) at lines 9-280, but `\section{The certificate}` at lines 282-284 is *literally empty*. Direct dual structure to 76_homology, where the loop did produce `thm:homology-singleton-cycle-semantic-name-certificate` (line 188). Loop has touched cohomology chapter zero times despite 18 already-checked sub-theorems sitting ready for the certificate roll-up.

---

### B-136 - TotalOrder finite maximum classifier uniqueness

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (codex) |
| Object | TotalOrder finite maximum classifier uniqueness |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
Under TotalOrderUp(C), any two finite-maximum witnesses of the same nonempty finite carried spine are classifier-equal.

Local inputs:
- `papers/bedc/parts/concrete_instances/29_totalorder_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/28_poset_namecert_construction.tex`

Rationale:
Lands cleanly in chapter 29 (totalorder namecert), which currently has only definitions plus B-13 (trichotomy classifier reduction). Finite-max uniqueness is a distinct, foundational total-order theorem — it is the antisymmetric upper-bound uniqueness applied to a finite spine, not the trichotomy reduction of B-13 nor the general lattice GLB/LUB uniqueness of B-29 (different setup: totalorder finite spine vs lattice directional bounds). It fills a real gap on the totalorder side and is naturally expressible as a single implication. Risk is low-medium because the proof reduces to antisymmetry on a finite enumeration.

---

### B-137 - Functor preserves isomorphism witness

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (codex) |
| Object | Functor preserves isomorphism witness |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
Under a CategoryUp source and CategoryUp codomain with a FunctorUp F between them, if a source morphism f has paired left-inverse and right-inverse witnesses g, h satisfying g ∘ f ∼C 1 and f ∘ h ∼C 1 in the source, then F(f) has F(g), F(h) as left- and right-inverse witnesses in the codomain up to the codomain hom classifier.

Local inputs:
- `papers/bedc/parts/concrete_instances/36_category_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/37_functor_namecert_construction.tex`

Rationale:
Chapter 37 functor_namecert is currently 100% definition-only (per B-11 rationale: 7 def, 0 thm), so theorem sites that exercise the functor stability certificate are scarce and high-value. The candidate is a clean classifier-level preservation statement, distinct from B-11 (which covers hom-carrier composition closure under functor composition) and not a paraphrase of any existing functor-related entry. Iso/split-mono/split-epi witnesses already have definition-side surface (def:category-split-epimorphism, def:category-split-monomorphism) but no theorem proves their functor image carries the mapped witnesses, so this directly fills a known gap and feeds cleanly into the codex_formalize.py lane.

---

### B-138 - Euclid's lemma for prime divisibility (p | a·b → p | a ∨ p | b)

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Euclid's lemma for prime divisibility (p | a·b → p | a ∨ p | b) |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 10/10 |
| Novelty | 8/10 |

Problem:
If p : NatPrime and a, b : Nat with NatDivides(p, NatMul(a, b)), then NatDivides(p, a) ∨ NatDivides(p, b), proved by induction on the unary representation of a together with the prime classifier and trial-division decidability.

Local inputs:
- `papers/bedc/parts/concrete_instances/39_prime_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/04_nat_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/05_add_namecert_construction.tex`
- `lean4/BEDC/Derived/PrimeUp.lean`

Rationale:
Belongs in chapter 39 (concrete-instances/prime). This is exactly Hardy & Wright "An Introduction to the Theory of Numbers" Theorem 3 (Ch.II §3): the cornerstone of unique factorization. The chapter's own proof of \thm:ftoa-uniqueness invokes Euclid's lemma in prose at line 411 ("Standard Euclid's-lemma argument: if a prime p divides a product a·b, then p divides a or p divides b, proved by induction on the unary representation of a") but never states or labels it as its own theorem. The chapter already has \def:nat-prime, \def:nat-divides, \thm:prime-decidable, \lem:divides-transitive, and the unary multiplication kit (lem:nat-mul-functional, lem:nat-mul-result-unary), so the prerequisites for a clean classifier-stable statement are all present. The proof inducts on the unary list of a using divides-transport (\thm:nat-divides-divisor-hsame-transport) and the trial-division witness; ≤ 3 deep-reasoning rounds is realistic. Every introductory number-theory text states this as a separate theorem; not stating it leaves a textbook-level gap directly under FTOA.

---

### B-139 - Lattice distributivity implies modular law (x ≤ z ⇒ x ∨ (y ∧ z) ∼ (x ∨ y) ∧ z)

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Lattice distributivity implies modular law (x ≤ z ⇒ x ∨ (y ∧ z) ∼ (x ∨ y) ∧ z) |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 9/10 |

Problem:
Under a LatticeUp setup with directional meet/join bound fields, if the distributive identity x ∧ (y ∨ z) ∼_C (x ∧ y) ∨ (x ∧ z) holds for all x, y, z, then for any x, y, z with x ≤_C z, x ∨ (y ∧ z) ∼_C (x ∨ y) ∧ z (Dedekind modular law).

Local inputs:
- `papers/bedc/parts/concrete_instances/30_lattice_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/30_lattice_directed_associativity.tex`
- `papers/bedc/parts/concrete_instances/28_poset_namecert_construction.tex`
- `lean4/BEDC/Derived/LatticeUp.lean`

Rationale:
Belongs in chapter 30 (concrete-instances/lattice). This is Birkhoff "Lattice Theory" Ch.I §6 (also Davey & Priestley Ch.4): every distributive lattice is modular — a one-line classical pivot between the two main lattice-theoretic axes. Chapter 30 currently labels idempotence/absorption/commutativity/opposite-absorption/bound-uniqueness from the directional bound certificate (\thm:lattice-idempotence-absorption-from-bound-characterization, \thm:lattice-commutativity-from-directional-bounds, etc.) but contains zero theorems naming the words "distributive" or "modular" (verified: grep -i 'distributive\|modular' on 30_lattice_namecert_construction.tex returns no theorem environments). BOARD entries B-07/B-25/B-26/B-27/B-29 cover only the bound-direction laws, not distributivity vs. modularity. The proof uses absorption (already proved in B-07) plus the directional join-leastness field — closeable in 1-2 rounds. This is precisely the curricular gap a Birkhoff-style chapter must fill before any Boolean / Heyting algebra extension.

---

### B-140 - Determinant multiplicativity det(A·B) ∼ det(A)·det(B)

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Determinant multiplicativity det(A·B) ∼ det(A)·det(B) |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 10/10 |
| Novelty | 9/10 |

Problem:
Under a CommRingUp(R) scalar package and a fixed matrix dimension, for square matrices A, B carrying matrix certificates and a determinant function defined as the Leibniz signed permutation fold, det(MatMul(A, B)) ∼_R MatMul(det(A), det(B)) up to the scalar classifier.

Local inputs:
- `papers/bedc/parts/concrete_instances/62_determinant_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/24_matrix_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/19_commring_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/94_permutation_namecert_construction.tex`
- `lean4/BEDC/Derived/DeterminantUp.lean`

Rationale:
Belongs in chapter 62 (concrete-instances/determinant). This is Hungerford "Algebra" Ch.VII Theorem 4.7 / Lang "Algebra" Ch.XIII §4 — the single most classical theorem about determinants. Chapter 62 currently has only three labeled theorems (\thm:singleton-matrix-determinant-endpoint-correspondence, \thm:determinant-singleton-det-append-pair-scalar-classifier, \thm:determinant-singleton-classifier-semantic-namecert — verified by grep on 62_determinant_namecert_construction.tex). Chapter 24 (matrix) already provides \thm:matrix-multiplication-associativity-finite-folds and \thm:matrix-multiplication-classifier-congruence; chapter 94 supplies a Permutation namecert; chapter 19 supplies the commring fields needed to expand the Leibniz product-of-folds. The result is deeper than 1-round but tightly bounded: the standard Cauchy-Binet style proof reduces to two finite-fold reorderings (sum over composed permutations), each of which is a finite-fold congruence already adjacent to existing matrix machinery. Strong textbook standard, no overlap with BOARD.

---

### B-141 - Lagrange's theorem: |G| ∼ |H| · [G:H] for a finite group with subgroup

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Lagrange's theorem: |G| ∼ |H| · [G:H] for a finite group with subgroup |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 10/10 |

Problem:
Under a finite GroupUp(G) carrier with a SubgroupUp(H ≤ G) carrier, the group cardinality classifier decomposes as a NatMul of the subgroup cardinality and the right-coset index, NatMul(|H|, [G:H]) ∼_Nat |G|, derived from the right-coset partition supplied by the subgroup centralizer right-coset classifier.

Local inputs:
- `papers/bedc/parts/concrete_instances/58_subgroup_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/16_group_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/60_quotientgroup_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/04_nat_namecert_construction.tex`
- `lean4/BEDC/Derived/SubgroupUp.lean`
- `lean4/BEDC/Derived/GroupUp.lean`

Rationale:
Belongs in chapter 58 (concrete-instances/subgroup) or 60 (concrete-instances/quotientgroup). Hungerford "Algebra" Ch.II §4 Theorem 4.6 — the most cited finite-group theorem in any first algebra course. Chapter 58 already has \thm:subgroup-centralizer-right-coset-classifier-hsame-transport and \thm:subgroup-centralizer-right-coset-classifier-trans-from-empty-unit, plus \def:quotientgroup-centralizer-coset-carrier in chapter 60, so the right-coset classifier is on hand. There are zero hits for "Lagrange" anywhere under papers/bedc/parts/. The chapter framework expresses cardinalities as unary Nat lengths, so the theorem becomes: the carrier index is a NatMul fold over coset representatives. The proof uses the right-coset classifier's trans+hsame-transport to show each coset has the same cardinality as H, then a finite-fold finalization. This is the natural next theorem the chapter is set up for; high textbook fit, no overlap with BOARD entries.

---

### B-142 - Polynomial evaluation is an additive homomorphism: eval_α(p ⊕ q) ∼ eval_α(p) +_R eval_α(q)

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Polynomial evaluation is an additive homomorphism: eval_α(p ⊕ q) ∼ eval_α(p) +_R eval_α(q) |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 9/10 |

Problem:
Under a CommRingUp(R) scalar package and a chosen point α : R, the Horner-style evaluation eval_α : PolynomialCarrier(R) → R satisfies eval_α(PolyAdd(p, q)) ∼_R Add_R(eval_α(p), eval_α(q)) for all coefficient lists p, q, up to the scalar classifier.

Local inputs:
- `papers/bedc/parts/concrete_instances/25_polynomial_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/19_commring_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/11_list_namecert_construction.tex`
- `lean4/BEDC/Derived/PolynomialUp.lean`

Rationale:
Belongs in chapter 25 (concrete-instances/polynomial). Hungerford "Algebra" Ch.III §6 Theorem 6.5 / Lang "Algebra" Ch.IV §1 — the substitution principle on which factor-theorem and Hilbert-Nullstellensatz culture rests. Chapter 25 has \def:polynomial-carrier, polynomial addition (\def:polynomial-raw-add-comparison-data), normalization and trim-zero infrastructure (B-09, B-21, B-30), and \thm:finite-additive-fold-congruence-coefficient-lists, but contains no theorem nor definition naming evaluation/eval_α (verified: grep -i 'evaluate\|eval_\|Horner' on 25_polynomial_namecert_construction.tex returns 0). The new block introduces eval_α via Horner recursion (a commring-side use of the existing finite-additive-fold) and proves the additive-homomorphism row only — closeable in 2 rounds since both sides reduce to the same fold via the additive-fold congruence already labeled in the chapter. The multiplicative-homomorphism case is left for a future block; the additive case alone is a complete textbook theorem. No overlap with BOARD entries B-09/B-21/B-22/B-30/B-31, which all concern normalize-vs-raw rather than evaluation.

---

### B-143 - Identity functor name certificate: 1_C : C → C carries the FunctorUp obligations

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Identity functor name certificate: 1_C : C → C carries the FunctorUp obligations |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
Under a CategoryUp(C) carrier, the identity functor 1_C with object map x ↦ x and morphism map f ↦ f satisfies the FunctorUp(C, C) certificate: it preserves composition (1_C(g∘f) ∼ 1_C(g)∘1_C(f)), preserves identity (1_C(id_x) ∼ id_{1_C(x)}), and respects the morphism classifier endpoint-by-endpoint.

Local inputs:
- `papers/bedc/parts/concrete_instances/37_functor_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/36_category_namecert_construction.tex`
- `lean4/BEDC/Derived/FunctorUp.lean`
- `lean4/BEDC/Derived/CategoryUp.lean`

Rationale:
Belongs in chapter 37 (concrete-instances/functor). Mac Lane "Categories for the Working Mathematician" Ch.I §3 — the very first concrete functor every textbook constructs; identity 1_C and composition F∘G together generate the category Cat. Chapter 37 has 39 labeled theorems mostly about prefix-hom-carrier preserves/reflects/composition, plus chapter 36 has \thm:category-hom-carrier-unary-prefix-iff and \thm:category-unary-continuation-stability-law-package, but there is no labeled identity-functor name certificate (verified: grep 'identity-functor\|id-functor\|functor-identity' returns only \thm:functor-prefix-hom-carrier-empty-identity-iff, which is a different statement about what happens when a functor's image of an identity is empty). BOARD entry B-11 covers functor *composition* preserving the hom-carrier classifier, not the identity functor. The proof is straightforward: every classifier obligation reduces by reflexivity of ∼ on the carrier; closeable in 1 round. Pedagogically, having no identity-functor instance is the most visible textbook gap in the category chapter cluster.

---

### B-144 - AbGroup divisible-subgroup closure

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | AbGroup divisible-subgroup closure |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
Under an AbGroupUp(G) carrier, the predicate Divisible(a) := "for every n : Nat with n nonempty there exists b : G with NatScale(n, b) ∼_G a" is closed under the abelian-group addition and inverse: Divisible(a) ∧ Divisible(c) → Divisible(a +_G c) and Divisible(a) → Divisible(-_G a), and Divisible(0_G) holds.

Local inputs:
- `papers/bedc/parts/concrete_instances/17_abgroup_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/04_nat_namecert_construction.tex`
- `lean4/BEDC/Derived/AbGroupUp.lean`

Rationale:
Belongs in chapter 17 (concrete-instances/abgroup). Hungerford "Algebra" Ch.II §3 / Kaplansky "Infinite Abelian Groups" §1 — the dual pair to the torsion subgroup. Chapter 17 already labels \thm:abgroup-torsion-subgroup-closure (line ≈ near end), so the *torsion* side of the textbook dyad is in place; the *divisible* side is missing entirely (verified: grep -i 'divisible' on 17_abgroup_namecert_construction.tex returns 0 hits). The proof uses \thm:abgroup-mul-common-left-factor-collect (existing) to combine two n-th-root witnesses for a + c, and inverse closure follows from \thm:abgroup-inverse-mul. The new block can introduce the Divisible predicate inline (in the theorem statement) and prove the three closure rows in a single proof, mirroring the torsion-closure block. Closeable in 1-2 rounds. Strong textbook standard; not in BOARD.

---

### B-145 - Double opposite category certificate is data-equal to original

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Double opposite category certificate is data-equal to original |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 10/10 |
| Novelty | 9/10 |

Problem:
If a CategoryUp certificate C satisfies the obligations of def:opposite-category-certificate-data, then iterating the opposite construction twice yields a CategoryUp certificate whose object carrier, object classifier, hom-carrier predicate, morphism classifier, identity witnesses, and composition relation are componentwise identical to those of C.

Local inputs:
- `papers/bedc/parts/concrete_instances/36_category_namecert_construction.tex`
- `lean4/BEDC/Derived/CategoryUp.lean`

Rationale:
Definition `def:opposite-category-certificate-data` is at 36_category_namecert_construction.tex:223-242, and `thm:opposite-category-certificate` proves the construction yields a valid CategoryUp at 36_category_namecert_construction.tex:245-318. There is NO theorem stating the construction is involutive (C^op^op = C). Grep `"opposite.*opposite|double.*opposite|opop|involution|reverse.*reverse"` over all of papers/bedc/parts/concrete_instances/ returned only references to `inverse involution` (a different concept inside chapters 17 abgroup, 58 subgroup, 20 field), `nattrans/vertical_and_opposite_extras.tex` (different chapter, only proving the single opposite construction), `adjunction-unit-counit-carrier-swap-involution` at 85_adjunction:342-376 (about coordinate-swap, not opposite-opposite), and a filename `category/certificate_and_visible_cases_core_double_endpoint_tail` (`double endpoint tail` is unrelated). The natural BEDC proof is unfolding twice: opposite swaps endpoints in HomCarrier and arguments in Comp; doing it twice yields identity on every field. The same gap exists in `papers/bedc/parts/concrete_instances/functor/certificate_obligations.tex:67-149` (def+thm for opposite functor) and `papers/bedc/parts/concrete_instances/nattrans/vertical_and_opposite_extras.tex:22-79` (def+thm for opposite nattrans), but the category-level statement is foundational and is the cleanest of the three to formalize first.

---

### B-146 - Double opposite functor certificate is data-equal to original

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Double opposite functor certificate is data-equal to original |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
If F:C->D is a FunctorUp certificate satisfying the obligations of def:functor-certificate-obligations and def:opposite-functor-certificate-data is applied twice, the resulting functor F^op^op:C^op^op->D^op^op has object map, morphism map, and stability fields componentwise identical to F (modulo the C^op^op = C identity at the source/target level).

Local inputs:
- `papers/bedc/parts/concrete_instances/functor/certificate_obligations.tex`
- `papers/bedc/parts/concrete_instances/36_category_namecert_construction.tex`
- `lean4/BEDC/Derived/FunctorUp.lean`

Rationale:
Definition `def:opposite-functor-certificate-data` at functor/certificate_obligations.tex:67-84 sets F^op object map = F_0 and morphism map = F_1, only the hom-carrier endpoints are read through opposite category convention. Theorem `thm:opposite-functor-certificate` at functor/certificate_obligations.tex:86-149 verifies the construction is valid. Grep `double|involution|second.*opposite` in functor/ returned no matches. Iterating the construction twice should restore F since the object/morphism maps are unchanged by each opposite step. This is an independent target from the category-level double opposite (different Lean theorem on FunctorUp.lean) and depends on the category-level result for endpoint reasoning.

---

### B-147 - Choice as term-stratum instance of the meta-closure schema

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | Choice as term-stratum instance of the meta-closure schema |
| Layer | capstones |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
Under the meta-closure operation of def:three-axioms-meta-closure-operation read at the term stratum, the schematic move 'accept an unwitnessed positive existential and use the accepted value as oracle' is equivalent to AC: ∀i∈I,∃x_i∈A_i ⇒ ∃f:I→⊔A_i with f(i)∈A_i.

Local inputs:
- `papers/bedc/parts/capstones/three_axioms_one_closure.tex`

Rationale:
Directly fills a known Sketch-proof gap in thm:three-axioms-unification (capstones/three_axioms_one_closure.tex). The infrastructure (def:three-axioms-meta-closure-operation, ex:three-axioms-choice) already exists and the equivalence is currently stated only informally. This is the term-stratum component of a triad with #2 and #3 supporting the unification theorem; once all three exist the Sketch can be replaced with a structured proof. No BOARD entry, no theorem-level paper label covers this. Stepping-stone scope.

---

### B-148 - Quot.sound as type-stratum instance of the meta-closure schema

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | Quot.sound as type-stratum instance of the meta-closure schema |
| Layer | capstones |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
Under the meta-closure operation of def:three-axioms-meta-closure-operation read at the type stratum, the schematic move is equivalent to Quot-soundness: from an equivalence R on A, conclude there exists a type A/R with a section A/R→A choosing a canonical representative.

Local inputs:
- `papers/bedc/parts/capstones/three_axioms_one_closure.tex`

Rationale:
Type-stratum sister of #1; supports the Sketch proof of thm:three-axioms-unification. ex:three-axioms-quot-sound states the equivalence informally; this lemma formalizes it. Connects to def:three-axioms-replacement-quot which uses NameCert/psame-transport as the BEDC replacement, making this the lemma that justifies the replacement at the schema level. No BOARD or paper duplicate. Distinct from #5 which proves the structural soundness of the replacement, not the equivalence schema-side.

---

### B-149 - Propext as proposition-stratum instance of the meta-closure schema

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | Propext as proposition-stratum instance of the meta-closure schema |
| Layer | capstones |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 7/10 |

Problem:
Under the meta-closure operation of def:three-axioms-meta-closure-operation read at the proposition stratum, the schematic move is equivalent to propext: from P⇔Q conclude P=Q at the proposition level.

Local inputs:
- `papers/bedc/parts/capstones/three_axioms_one_closure.tex`

Rationale:
Proposition-stratum third of the equivalence triad behind thm:three-axioms-unification's Sketch proof. ex:three-axioms-propext states the schema informally; formalizing the proposition-level instantiation closes the third gap and makes the unification proof structured rather than sketched. No paper-level theorem label covers this. Belongs in capstones alongside #1 and #2.

---

### B-150 - Countable choice constructs explicit witness function from N-indexed family

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | Countable choice constructs explicit witness function from N-indexed family |
| Layer | capstones |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |

Problem:
Given a family A:N→Type with w:∀n,A(n), there is an explicit f:N→⊔A(n) defined by primitive recursion satisfying f(n)∈A(n), without invoking Classical.choice.

Local inputs:
- `papers/bedc/parts/capstones/three_axioms_one_closure.tex`

Rationale:
def:three-axioms-replacement-choice names countable choice as the BEDC replacement for term-stratum meta closure but only states it definitionally — the explicit recursive construction is missing. This is the term-stratum component of thm:three-axioms-replacements-suffice's currently-Sketch proof. Distinct from #1 which proves the equivalence schema; this proves the constructive replacement is realizable. Closes quickly because primitive recursion is already kernel-level.

---

### B-151 - NameCert psame-transport replaces Quot.sound use

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | NameCert psame-transport replaces Quot.sound use |
| Layer | capstones |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 7/10 |

Problem:
For any classifier-respecting operation φ:A→B and a,a' with a∼A a', φ(a)∼B φ(a') — without invoking Quot.sound to identify a and a' at the type level.

Local inputs:
- `papers/bedc/parts/capstones/three_axioms_one_closure.tex`
- `papers/bedc/parts/core/08_typed_naming_certificates.tex`

Rationale:
def:three-axioms-replacement-quot declares NameCert + psame-transport as the BEDC replacement for type-stratum meta closure but the structural soundness lemma showing this replacement preserves the classifier-respecting operations Quot.sound enables is missing. Type-stratum component of thm:three-axioms-replacements-suffice's Sketch. Slightly lower novelty than oracle's 8 because generic psame-transport machinery exists in core (ch:core-typed-naming-certificates), but the capstones-specific replacement-soundness framing is new and distinct from generic transport. Distinct from #2 (equivalence schema) and from existing core transport lemmas.

---

### B-152 - hsame transport bypasses propext at the proposition level

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | hsame transport bypasses propext at the proposition level |
| Layer | capstones |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |

Problem:
For any kernel construction Φ consuming a proposition P, and propositions P,Q with P⇔Q (equivalently an hsame-transport between P and Q), there is a parameterized form Φ[P→Q] consuming Q via the bidirectional implication, without invoking propext.

Local inputs:
- `papers/bedc/parts/capstones/three_axioms_one_closure.tex`

Rationale:
def:three-axioms-replacement-propext names hsame/psame transport as the BEDC replacement for proposition-stratum meta closure but no structural lemma states the replacement is sound. Proposition-stratum third of thm:three-axioms-replacements-suffice's Sketch components, completing the triad with #4 (term) and #5 (type). After all three land, the chapter's claim that BEDC's certified content is closed under the three replacements becomes a structured proof.

---

### B-153 - Term-stratum meta-closure drops per-index witness structure

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | Term-stratum meta-closure drops per-index witness structure |
| Layer | capstones |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 9/10 |

Problem:
Under the meta-closure schema of \autoref{def:three-axioms-meta-closure-operation} read at the term stratum, the input data carries a per-index witness family i \mapsto w_i as constructor data, but the output term f : I \to \bigsqcup A_i exposes only f i \in A_i as a property and does not expose the per-index recipe binding i \mapsto w_i.

Local inputs:
- `papers/bedc/parts/capstones/three_axioms_one_closure.tex`

Rationale:
Belongs in capstones/three_axioms_one_closure.tex. The chapter currently states the meta-closure schema (def:three-axioms-meta-closure-operation) and gives Choice as a term-stratum example (ex:three-axioms-choice) but does not pin down what specifically is lost. This proposition is a single concrete implication-form claim about constructor data dropped at the term stratum, expressible as a `\begin{theorem|lemma}` site with a clear Lean-side obligation about destructured non-exposure of the witness family. No BOARD entry covers meta-closure / three-axioms territory; no paper label of the form thm:/lem:/cor:three-axioms-* appears in coverage. Stepping-stone scope.

---

### B-154 - Type-stratum meta-closure drops the equivalence derivation

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | Type-stratum meta-closure drops the equivalence derivation |
| Layer | capstones |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 9/10 |

Problem:
Under the meta-closure schema read at the type stratum, the input data carries a kernel-level derivation tree witnessing a \sim_R b under reflexivity / symmetry / transitivity, but the output identification [a] = [b] in A/R exposes only equality at the type level and does not expose the witnessing R-derivation.

Local inputs:
- `papers/bedc/parts/capstones/three_axioms_one_closure.tex`

Rationale:
Companion to the term-stratum proposition, sited in the same capstones chapter. ex:three-axioms-quot-sound states the schematic move at the type stratum but no lemma pins the dropped derivation tree. The companion def:three-axioms-replacement-quot (NameCert + psame transport) only makes sense as a contrast once the loss is named. Concrete single-implication form, no BOARD overlap, no matching paper label, in scope for capstones. Distinct from candidate 1 because Quot.sound's input data is a derivation tree rather than a per-index witness family — the dropped structure has different shape and so warrants its own loop.

---

### B-155 - Proposition-stratum meta-closure drops the implication direction

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | Proposition-stratum meta-closure drops the implication direction |
| Layer | capstones |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
Under the meta-closure schema read at the proposition stratum, the input data is a pair of distinct implications (\pi_1 : P \to Q, \pi_2 : Q \to P) with their internal proof structures, but the output identification P = Q exposes neither which direction was used at any subsequent application site nor the internal structure of \pi_1 or \pi_2.

Local inputs:
- `papers/bedc/parts/capstones/three_axioms_one_closure.tex`

Rationale:
Third stratum-specific loss proposition, sited in capstones/three_axioms_one_closure.tex. ex:three-axioms-propext schematizes propext as proposition-stratum meta-closure but no lemma names what propext drops. The replacement def:three-axioms-replacement-propext parameterizes kernel constructions over the implication pair — that move is only motivated once the directional + structural loss is on record. Concrete single-implication claim, distinct from candidates 1 and 2 because the dropped structure is a directed pair of implications rather than a witness family or derivation tree. No BOARD overlap, no matching paper label.

---

### B-156 - Tensor product singleton factor source-target swap

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Tensor product singleton factor source-target swap |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 9/10 |

Problem:
For histories l, r, t with TensorProductSingletonFactor(l, r, t), then TensorProductSingletonFactor(r, l, t) holds.

Local inputs:
- `papers/bedc/parts/concrete_instances/65_tensorproduct_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/21_module_namecert_construction.tex`

Rationale:
Chapter 65_tensorproduct has 9 theorem labels but ZERO BOARD entries (verified: grep -i 'tensor' tools/bedc-deep/BOARD.md returns no hits). The chapter is entirely about TensorProductSingletonCarrier and TensorProductSingletonFactor, with thm:tensorproduct-singleton-factor-hsame-transport (65_tensorproduct:138-150) handling componentwise hsame transport but no theorem stating the basic source-target swap symmetry of the bilinear factor — a textbook tensor-product symmetry that lives one step away from the existing transport theorem. Closes immediately because the singleton-factor predicate forces l, r, t all to be empty, making Cont(l,r,t) and Cont(r,l,t) both reduce to Cont(emp,emp,emp). This is the missing 'flip' theorem that any later non-singleton tensor-symmetry argument depends on.

---

### B-157 - L-function Dirichlet partial-sum result hsame transport

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | L-function Dirichlet partial-sum result hsame transport |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
For Dirichlet term operation term, parameter s, index n, and histories S, S' with DirichletPartSum(term, s, n, S) and S ~ S', then DirichletPartSum(term, s, n, S').

Local inputs:
- `papers/bedc/parts/concrete_instances/81_lfunction_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/45_dirichlet_series_namecert_construction.tex`

Rationale:
Chapter 81_lfunction has 11 theorem labels but ZERO BOARD entries (verified via grep). All eleven theorems concern the inductive structure of DirichletPartSum at the successor index (positive-index, previous-unique, deterministic, zero-term-stable, etc.), but there is no transport theorem for hsame on the sum result S itself. Without this, every later certificate that wants to rebuild a DirichletPartSum after an hsame substitution has to recurse on the constructor — exactly the gap that chapters 11_list and 13_real already filled with explicit transport theorems. Closes by induction on the partial-sum constructor, transporting the continuation result field at the step case.

---

### B-158 - EqType class carrier hsame transport along the anchor

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | EqType class carrier hsame transport along the anchor |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
For histories anchor, anchor', h with EqtypeClassCarrier anchored at anchor holding for h and anchor ~ anchor', the EqtypeClassCarrier anchored at anchor' holds for h.

Local inputs:
- `papers/bedc/parts/concrete_instances/109_eqtype_namecert_construction.tex`
- `papers/bedc/parts/proof_obligations/psame_design.tex`

Rationale:
Chapter 109_eqtype has 12 theorem labels but ZERO BOARD entries (verified via grep). Existing theorems are e0/e1 anchor-tail readbacks, anchor pair determinism, visible-context absurdity, and the terminal SemanticNameCert (thm:eqtype-identity-semantic-namecert). Transport of the EqtypeClassCarrier under hsame on the *anchor* (rather than on h) is the dual to the anchor-pair-deterministic theorem and is the precise lemma a downstream psame transport at the type stratum (capstones B-151 NameCert psame-transport replaces Quot.sound use) would invoke. Single-implication, closes by composing the carrier comparison with the anchor's hsame witness via classifier transitivity.

---

### B-159 - Functor composition identity unit laws

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (codex) |
| Object | Functor composition identity unit laws |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |

Problem:
Under a FunctorUp setup, for any certified functor F : C -> D, the composites F . 1_C and 1_D . F classify pointwise with F under the FunctorUp classifier.

Local inputs:
- `papers/bedc/parts/concrete_instances/37_functor_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/36_category_namecert_construction.tex`

Rationale:
Chapter 37 (Functor namecert construction) is 100% definition-only, as flagged by B-11's rationale. B-11 covers composition closure (G . F carries the composed hom-carrier classifier), but no existing BOARD entry or paper label addresses the identity unit laws on either side. The paper already has def:identity-functor-certificate-data, so the identity functor is defined but its unit laws against arbitrary certified functors are not stated. This is the natural sibling theorem to B-11: together they form the minimal categorical-coherence package for the functor certificate (associativity + identity), and it is expressible as a clean implication on the FunctorUp classifier without leaving BEDC scope.

---

### B-160 - Monoid forgets to Semigroup certificate

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Monoid forgets to Semigroup certificate |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
If MonoidUp(C) holds, then dropping the left- and right-identity stability fields yields a SemigroupUp(C) certificate over the same carrier, multiplication, and classifier.

Local inputs:
- `papers/bedc/parts/concrete_instances/15_monoid_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/57_semigroup_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/group/16_group_certificate_tail.tex`

Rationale:
The board carries the entire forgetful chain B-28 (CommRing→Ring), B-53 (AbGroup→Group), B-67 (VecSpace→Module), B-68 (Lattice→Poset), B-69 (Module→AbGroup), B-71 (Field→CommRing), B-72 (Ring→AbGroup), B-73 (Module→Ring), B-74 (POSet→Preorder), B-75 (TotalOrder→POSet), B-76 (Group→Monoid). The next link Group→Monoid lands at prop:group-forgets-monoid-certificate (concrete_instances/group/16_group_certificate_tail.tex:103), but the chain stops there. MonoidUp stability fields at 15_monoid_namecert_construction.tex:89-99 list six items (reflexivity, transitivity, associativity, left identity, right identity, multiplication congruence); SemigroupUp's semantic certificate at 57_semigroup_namecert_construction.tex:117-124 lists exactly the same fields minus the two identity laws. Grep `'monoid.*forgets.*semigroup\|forgets.*semigroup'` over papers/bedc/parts/ returns 0 matches and grep on BOARD.md returns 0 matches. This is the next missing rung of the algebraic-ladder forget chain that B-76's rationale (line 1908 of BOARD.md) explicitly names as the canonical pattern.

---

### B-161 - Semigroup forgets to Magma certificate

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Semigroup forgets to Magma certificate |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
If SemigroupUp(C) holds, then dropping the associativity stability field yields a MagmaUp(C) certificate over the same carrier, multiplication, and classifier.

Local inputs:
- `papers/bedc/parts/concrete_instances/57_semigroup_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/56_magma_namecert_construction.tex`

Rationale:
Bottom rung of the same forgetful chain. SemigroupUp's semantic-certificate field list at 57_semigroup_namecert_construction.tex:117-124 reads: classifier reflexivity/symmetry/transitivity, multiplication closure, multiplication congruence, associativity, ledger. Magma chapter intro at 56_magma_namecert_construction.tex:4 says "MagmaUp packages a carrier endowed with a single binary operation, with no associativity, identity, or inverse demands" — i.e. exactly the SemigroupUp field list minus associativity. Grep `'semigroup.*forgets\|forgets.*magma'` across papers/bedc/parts/ returns 0 hits. B-78 (auto-spawned 'Concrete unary-history magma classifier carrier-aware reflexivity') touches 56_magma but at the carrier-reflexivity level, not the certificate projection. Distinct from B-76 (Group→Monoid) by being two layers lower in the algebraic ladder. Closes the algebraic-ladder forget chain at its terminal end, which the rationale of B-78 (BOARD.md:1966) flags as a deliberate blindspot.

---

### B-162 - Matrix multiplication left-distributes over matrix addition

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Matrix multiplication left-distributes over matrix addition |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
Under MatrixUp over a RingUp scalar source, for matrices A:n×m and B,C:m×p of compatible dimensions, A·(B+C) is matrix-classifier equal to A·B + A·C.

Local inputs:
- `papers/bedc/parts/concrete_instances/24_matrix_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/matrix/the_certificate.tex`
- `papers/bedc/parts/concrete_instances/matrix/finite_fold_multiplication_laws.tex`
- `papers/bedc/parts/concrete_instances/18_ring_namecert_construction.tex`

Rationale:
Matrix stability certificate at concrete_instances/matrix/the_certificate.tex:18-29 lists 'addition closure by scalar addition' (item 4) and 'multiplication closure by finite scalar sums and products' (item 5), but distributivity at the matrix level is only described as a *consequence* in 24_matrix_namecert_construction.tex:4 ('Matrix addition and multiplication are derived operations governed by the ring's certificate fields'), never proved. The board entries for matrix are B-84 (identity unit), B-97 (associativity from finite folds), B-102 (multiplication classifier congruence), B-140 (det multiplicative). Grep of `'matrix.*distrib\|distrib.*matrix'` across BOARD.md returns 0 matches; grep of `'\\label{thm:.*matrix.*distrib'` across papers/bedc/parts/ returns 0 hits. The supporting lemma already exists: matrix/finite_fold_multiplication_laws.tex:175 lem:scalar-product-distributes-across-finite-additive-folds, which proves the *scalar-times-fold* version that this matrix-level theorem invokes pointwise at each (i,j). The chapter is actively missing the standalone matrix-level distributivity theorem that 18_ring_namecert_construction.tex's 'left/right distributivity' fields explicitly enable. Single-implication, fits the 'concrete_instances' chapter, and serves as a prerequisite for B-08 / B-23 module-action and tensor-product theorems already on the board.

---

### B-163 - Matrix multiplication right-distributes over matrix addition

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Matrix multiplication right-distributes over matrix addition |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |

Problem:
Under MatrixUp over a RingUp scalar source, for matrices A,B:n×m and C:m×p of compatible dimensions, (A+B)·C is matrix-classifier equal to A·C + B·C.

Local inputs:
- `papers/bedc/parts/concrete_instances/24_matrix_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/matrix/the_certificate.tex`
- `papers/bedc/parts/concrete_instances/matrix/finite_fold_multiplication_laws.tex`
- `papers/bedc/parts/concrete_instances/18_ring_namecert_construction.tex`

Rationale:
Companion theorem to the left-distributivity candidate above; in BEDC the two directions need separate fold-rearrangement proofs because the fold over the contraction index sits on different sides of the scalar product. Matrix stability certificate at concrete_instances/matrix/the_certificate.tex:18-29 enumerates closure obligations but, like for the left direction, never lifts right-distributivity to a labeled theorem. Grep `'\\label{thm:.*matrix.*right.*distrib\|matrix.*right.*distribut'` returns 0 hits across papers/bedc/parts/. The dual finite-fold lemma at matrix/finite_fold_multiplication_laws.tex:203 ('left distributivity applied to c · (a + fold(xs'))') is invoked for matrix-multiplication associativity (B-97) but never for the right-distributivity claim itself. Distinct from candidate 3 because the fold-pivot is the contracted index of A vs B, requiring a different rearrangement of `lem:scalar-product-distributes-across-finite-additive-folds`. Slightly lower novelty than the left direction since it shares the supporting machinery; lands in concrete_instances cleanly.

---

### B-164 - LinearMap pointwise sum is a LinearMap

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | LinearMap pointwise sum is a LinearMap |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 9/10 |

Problem:
If LinearMapCert_R(M, N; f) and LinearMapCert_R(M, N; g) both hold, then LinearMapCert_R(M, N; h) holds for the pointwise sum function h(x) := f(x) +_N g(x).

Local inputs:
- `papers/bedc/parts/concrete_instances/23_linearmap_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/linearmap/the_certificate.tex`
- `papers/bedc/parts/concrete_instances/linearmap/module_linearmap_certificates.tex`
- `papers/bedc/parts/concrete_instances/21_module_namecert_construction.tex`

Rationale:
LinearMap stability certificate at concrete_instances/linearmap/the_certificate.tex:18-29 enumerates six fields: pointwise classifier reflexivity, transitivity, zero preservation, additivity preservation, scalar-compatibility, identity/composition closure. There is NO closure clause for *pointwise sum* of two linear maps — the field list stops at composition. Existing LinearMap board entries — B-82 (zero from additivity), B-83/B-96 (composition certificate), B-109 (identity certificate), B-110 (composition associativity), B-121 (identity unit laws), B-125 (kernel submodule), B-126 (image submodule) — all live inside the chapter but none of them lift the Hom-set to an abelian group. Grep `'\\label{thm:.*linearmap.*sum\|hom.*group.*structure'` over papers/bedc/parts/ returns 0 matches; grep `'pointwise sum'` of LinearMap on BOARD.md returns 0 matches. This is the foundational closure that turns Hom_R(M, N) into an AbGroupUp under pointwise addition and is a strict prerequisite for any later 'category of R-modules is enriched in AbGroupUp' construction. Concrete single-implication form, fits concrete_instances, distinct from B-110/B-121 which are about composition algebra rather than additive closure of Hom.

---

### B-165 - Tensor product singleton factor swap symmetry

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Tensor product singleton factor swap symmetry |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 7/10 |
| Novelty | 7/10 |

Problem:
If TensorProductSingletonFactor(l, r, t) holds for histories l, r, t, then TensorProductSingletonFactor(r, l, t) also holds.

Local inputs:
- `papers/bedc/parts/concrete_instances/65_tensorproduct_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/21_module_namecert_construction.tex`

Rationale:
Chapter 65 has 9 labeled theorems plus 2 definitions (verified by grep: 9 `\begin{theorem}` + def:tensorproduct-singleton-carrier at line 9, def:tensorproduct-singleton-factor at line 110). All 9 theorems are about singleton-carrier characterizations (empty-iff, empty-endpoint-iff, result-empty continuation, suffix carrier, prefix carrier, factor witness, hsame transport, semantic name certificate). No theorem swaps the left/right factor arguments. Grep `'tensor.*swap\|tensor.*symm\|tensor.*commut'` over papers/bedc/parts/ returns 0 matches; grep over BOARD.md returns 0 matches. The chapter intro at 65_tensorproduct_namecert_construction.tex:4 frames TensorProductUp as 'universal bilinear factorization', and bilinearity in the symmetric tensor case includes the swap that this theorem makes explicit. Single implication, lands in concrete_instances chapter 65. Lower fit than the matrix and forget candidates because singleton-carrier swap is mathematically trivial under the empty-history collapse, but it is still a missing labeled theorem and would license downstream symmetric-tensor / exterior-power theorems to refer to a swap symmetry by autoref instead of unfolding the factor predicate again.

---

### B-166 - Double opposite functor certificate data identity

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (codex) |
| Object | Double opposite functor certificate data identity |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
If F is a FunctorUp certificate over CategoryUp source and target, then the certificate data obtained by applying the opposite-functor construction twice is componentwise identical to the original F (object map, morphism map, classifier rows, preservation witnesses).

Local inputs:
- `papers/bedc/parts/concrete_instances/functor/certificate_obligations.tex`
- `papers/bedc/parts/concrete_instances/36_category_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/37_functor_namecert_construction.tex`

Rationale:
The paper already proves the category-level analogue at thm:double-opposite-category-certificate-data-identity (36_category_namecert_construction.tex:352) and defines the opposite-functor certificate at def:opposite-functor-certificate-data plus thm:opposite-functor-certificate (functor/certificate_obligations.tex:271,290). The functor-level double-opposite identity is the immediate sibling of the certified category-level theorem; it has nothing to invent and goes by two unfoldings of the same definitional swap, like the category proof. It belongs in concrete_instances/functor and lifts the chapter from definition-only into the involution row of the established hierarchy. No existing BOARD entry covers double-opposite for functor (B-11 is composition closure, not involution).

---

### B-167 - Double opposite natural transformation certificate data identity

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (codex) |
| Object | Double opposite natural transformation certificate data identity |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
If alpha:F=>G is a NatTransUp certificate, then the certificate data obtained by applying the opposite-natural-transformation construction twice yields component family and naturality rows componentwise identical to alpha.

Local inputs:
- `papers/bedc/parts/concrete_instances/nattrans/vertical_and_opposite_extras.tex`
- `papers/bedc/parts/concrete_instances/functor/certificate_obligations.tex`
- `papers/bedc/parts/concrete_instances/36_category_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/38_nattrans_namecert_construction.tex`

Rationale:
The opposite natural transformation is already certified at def:opposite-nattrans-certificate-data and thm:opposite-natural-transformation-certificate (nattrans/vertical_and_opposite_extras.tex:23,37). The double-opposite identity completes a three-tier series begun at the category level (thm:double-opposite-category-certificate-data-identity); together with the functor candidate above it closes the involution row across CategoryUp / FunctorUp / NatTransUp. Distinct from B-14 (which is naturality preservation under vertical composition, not involution). The proof structure is two unfoldings of the same data swap, rather than a new constructive definition, which makes the loop low-risk and clearly in scope of concrete_instances/nattrans.

---

### B-168 - Polynomial evaluation respects the polynomial classifier

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (codex) |
| Object | Polynomial evaluation respects the polynomial classifier |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
Under a CommRingUp(R) setup with a polynomial-evaluation operation Eval_alpha at a point alpha:R, PolySame_R(p,q) implies Eval_alpha,R(p) ~_R Eval_alpha,R(q).

Local inputs:
- `papers/bedc/parts/concrete_instances/25_polynomial_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/19_commring_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/11_list_namecert_construction.tex`

Rationale:
All existing polynomial BOARD entries (B-09, B-21, B-22, B-30, B-31) and the chapter 25 paper coverage operate purely on the coefficient-list side: trim, normalize, raw add/multiply, zero-tail invariance. None of them carry the polynomial classifier through to a value in R. This is the natural representative-stability theorem for any evaluation map: classifier-equal coefficient lists must produce ring-classifier-equal values under any well-defined Eval. It is the one-line implication form, sits cleanly in concrete_instances/25, and unblocks any later theorem that wants to reason about polynomial roots, identities, or specializations through the certificate. It is also a prerequisite for candidate 2 (multiplicativity of Eval), giving it independent value as a foundation rather than redundancy.

---

### B-169 - Polynomial evaluation is multiplicative

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (codex) |
| Object | Polynomial evaluation is multiplicative |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |

Problem:
Under a CommRingUp(R) setup with polynomial multiplication PolyMul_R and evaluation Eval_alpha at a point alpha:R, Eval_alpha,R(PolyMul_R(p,q)) ~_R Eval_alpha,R(p) *_R Eval_alpha,R(q).

Local inputs:
- `papers/bedc/parts/concrete_instances/25_polynomial_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/19_commring_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/11_list_namecert_construction.tex`

Rationale:
The multiplicativity-of-evaluation law is the canonical compatibility theorem between Cauchy convolution on coefficient lists and ring multiplication on values. None of the existing BOARD polynomial entries cover this — B-09 stays at normalize/add/multiply commutation on the list side, and B-22/B-30/B-31 deal with zero-tail/trim. Paper coverage shows no eval-multiplicative label. It is a single classifier-level implication, sits in concrete_instances/25, and is the kind of structural law downstream targets (factor theorem, root counting, resultants) would expect. Novelty is slightly lower than candidate 1 because the two are in the same evaluation cluster, but the proof obligations are genuinely distinct — multiplicativity needs finite-sum manipulation through ring distributivity, which the classifier-respect theorem does not.

---

### B-170 - Functor composition associativity classifier law

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (codex) |
| Object | Functor composition associativity classifier law |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
Under a FunctorUp setup, for certified functors F, G, H, the composites (H∘G)∘F and H∘(G∘F) are classifier-equal pointwise on objects and on hom-carriers.

Local inputs:
- `papers/bedc/parts/concrete_instances/37_functor_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/36_category_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/38_nattrans_namecert_construction.tex`

Rationale:
The functor chapter (37) is currently definition-only with no theorems, and B-11 only covers hom-carrier closure under a single composition step, not associativity across triple composition. Functor associativity is a foundational structural law that any FunctorUp certificate must support before NatTrans-level theorems (B-14) can compose along functor changes. The claim is a clean single-implication statement under a known setup, fits squarely in concrete_instances, and is not paraphrased by any current BOARD card or paper label. Different mechanism from B-11 (closure under one composition vs. two triple-composition associates classifying equally), so it spawns its own proof obligation rather than duplicating existing work.

---

### B-171 - LinearMap pointwise inverse is a LinearMap

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (codex) |
| Object | LinearMap pointwise inverse is a LinearMap |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |

Problem:
If LinearMapCert_R(M, N; f) holds for a module homomorphism f: M -> N, then the pointwise additive inverse x |-> -_N f(x) carries LinearMapCert_R(M, N; -f).

Local inputs:
- `papers/bedc/parts/concrete_instances/linearmap/module_linearmap_certificates.tex`
- `papers/bedc/parts/concrete_instances/21_module_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/17_abgroup_namecert_construction.tex`

Rationale:
This is a concrete sibling closure theorem on the LinearMap certificate. The current branch is actively editing module_linearmap_certificates.tex, indicating LinearMap is a live working surface, but no BOARD entry covers pointwise additive-inverse closure (B-08, B-19, B-20, B-23, B-24 are all about scalar action / module compatibility rather than about the LinearMap-of-modules level). It is a needed lemma for any AbGroupUp construction on Hom_R(M, N) and stands alone as a single-implication, classifier-respecting closure obligation that the LinearMap chapter does not yet prove explicitly.

---

### B-172 - Hom_R(M,N) carries AbGroup certificate via pointwise structure

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (codex) |
| Object | Hom_R(M,N) carries AbGroup certificate via pointwise structure |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 9/10 |

Problem:
Under LinearMapCert_R(M, N; -) for module homomorphisms, the pointwise zero, pointwise sum, pointwise inverse, associativity, commutativity, and unit rows assemble into an AbGroupUp certificate on Hom_R(M, N).

Local inputs:
- `papers/bedc/parts/concrete_instances/linearmap/module_linearmap_certificates.tex`
- `papers/bedc/parts/concrete_instances/17_abgroup_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/21_module_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/65_tensorproduct_namecert_construction.tex`

Rationale:
This is a structural extension theorem: the Hom-set of R-linear maps inherits an abelian-group certificate built from per-pointwise data. No existing BOARD entry constructs a higher-level AbGroupUp on a function space; the surrounding entries B-08/B-19/B-20/B-23/B-24 stay inside Module/Ring scalar-action territory, while B-11/B-14 stay inside Functor/NatTrans hom-carrier territory. Building AbGroup on Hom_R(M, N) is the natural next theorem after the pointwise-inverse closure and is a prerequisite for any later Hom-as-Module or tensor-Hom adjunction work that the active linearmap/tensorproduct edits will need.

---

### B-173 - SemanticNameCert fiber-product closure

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | SemanticNameCert fiber-product closure |
| Layer | core |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 9/10 |

Problem:
Under a common source S, if SemanticNameCert S P1 L1 C1 and SemanticNameCert S P2 L2 C2 hold, then the conjunction predicates P1∧P2 and L1∧L2 form a SemanticNameCert for the meet/product classifier C1∧C2.

Local inputs:
- `papers/bedc/parts/core/08_typed_naming_certificates.tex`
- `papers/bedc/parts/core/03_relational_extension_and_continuation.tex`

Rationale:
A structural closure theorem at the SemanticNameCert record level: B-17 weakens an existing presentation, but no existing BOARD entry or paper label combines two certificates over a shared source into a meet/product certificate. Grep over `paper_coverage` finds no thm matching fiber/conjunction/combine-cert/meet-cert at the certificate layer (the only `fiber` hits are concrete group/quotient/field theorems unrelated to this construction). It would supply a reusable bridge for any later product, intersection, or multi-obligation certificate.

---

### B-174 - Module: scalar negation distributes over scalar action

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Module: scalar negation distributes over scalar action |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
Under a ModuleUp(R, M) certificate, for every carried scalar r:R and carried module element m:M, ((-r) odot_M m) sim_M -_M (r odot_M m).

Local inputs:
- `papers/bedc/parts/concrete_instances/21_module_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/18_ring_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/ring/18_ring_certificate_and_additive_laws.tex`

Rationale:
Belongs in chapter 21 (Module). Standard textbook stepping stone in Hungerford ch.IV §1 (Modules) and Dummit & Foote §10.1 (Module axioms): negation of a scalar acts as additive inverse of the scalar action. Verified absent: grep across 21_module_namecert_construction.tex shows only thm:module-zero-action-annihilation (591) for 0_R odot m and r odot 0_M, and lem:module-scalar-action-additive-inverse (linearmap/module_linearmap_certificates.tex:428) for the SYMMETRIC `-_N(r odot y) sim r odot (-_N y)` (negation pulled to the module side); the negation pulled to the SCALAR side is not stated. Closes in 1-2 codex rounds: scalar distributivity over scalar addition (def:module-stability-certificate item 6) gives `(r +_R (-r)) odot m sim_M (r odot m) +_M ((-r) odot m)`; ring additive right inverse `r +_R (-r) sim_R 0_R` (thm:ring-add-right-inverse, ring/18_ring_certificate_and_additive_laws.tex:33) plus scalar-action congruence and thm:module-zero-action-annihilation give `(r +_R (-r)) odot m sim_M 0_M`; group inverse uniqueness (thm:group-left-right-inverse-uniqueness, group/namecert_construction_core/02_certificate.tex:70) closes the goal. All cited prerequisites already exist.

---

### B-175 - Module: scalar -1 acts as module additive inverse

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Module: scalar -1 acts as module additive inverse |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
Under a ModuleUp(R, M) certificate with scalar one 1_R, for every carried module element m:M, ((-1_R) odot_M m) sim_M -_M m.

Local inputs:
- `papers/bedc/parts/concrete_instances/21_module_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/18_ring_namecert_construction.tex`

Rationale:
Belongs in chapter 21 (Module). Standard textbook stepping stone in Hungerford ch.IV §1 and Dummit & Foote §10.1: the scalar -1 is recognized as the module-side negation operator. Verified absent: grep `module.*minus-one|module-neg-one` across papers/bedc/parts returns no matches; module chapter has zero-action annihilation but not unit-action negation. Closes in 1-2 rounds using only premises already in the chapter: scalar unit law (def:module-stability-certificate item 7) gives `1_R odot m sim_M m`; scalar distributivity over scalar addition gives `(1_R +_R (-1_R)) odot m sim_M (1_R odot m) +_M ((-1_R) odot m)`; ring additive right inverse `1_R +_R (-1_R) sim_R 0_R` plus thm:module-zero-action-annihilation give the LHS sim 0_M; substituting unit law on the first summand and applying group inverse uniqueness (thm:group-left-right-inverse-uniqueness) closes. All prerequisites exist locally.

---

### B-176 - Ring: left distributivity over subtraction

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Ring: left distributivity over subtraction |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 10/10 |
| Novelty | 7/10 |

Problem:
Under a RingUp(R) certificate, for all carried a,b,c:R, (a cdot_R (b -_R c)) sim_R ((a cdot_R b) -_R (a cdot_R c)), where x -_R y abbreviates x +_R (-_R y).

Local inputs:
- `papers/bedc/parts/concrete_instances/18_ring_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/ring/18_ring_zero_product_and_signed_square.tex`
- `papers/bedc/parts/concrete_instances/ring/18_ring_certificate_and_additive_laws.tex`

Rationale:
Belongs in chapter 18 (Ring). Standard textbook stepping stone in Hungerford ch.III §1 (Rings) and Dummit & Foote §7.1: distribution over subtraction follows immediately from distribution over addition plus the sign rule. Verified absent: grep `distribut.*subtract|distribut.*minus` across papers/bedc/parts returns NO matches; the chapter has full left distributivity (def:ring-stability-certificate) and the sign rules thm:ring-mul-neg-left-eq-neg-mul (line 238) and thm:ring-mul-neg-right-eq-neg-mul (line 260), and thm:ring-additive-difference-zero-exact (line 170) confirms `b -_R c` is sugar for `b +_R (-c)`, but no theorem extracts the subtraction-distribution corollary. Closes in 1 round: apply left distributivity to a cdot_R (b +_R (-c)) yielding (a cdot_R b) +_R (a cdot_R (-c)); apply thm:ring-mul-neg-right-eq-neg-mul to rewrite a cdot_R (-c) sim -_R (a cdot_R c); classifier transitivity finishes. The symmetric right-distributivity-over-subtraction is the obvious follow-up.

---

### B-177 - LinearMap: linear map preserves additive negation

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | LinearMap: linear map preserves additive negation |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 10/10 |
| Novelty | 8/10 |

Problem:
Under VecSpaceUp(F,V) and VecSpaceUp(F,W) certificates and a carried LinearMapUp(V,W) map f, for every carried m:V, (f(-_V m)) sim_W -_W (f(m)).

Local inputs:
- `papers/bedc/parts/concrete_instances/23_linearmap_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/linearmap/module_linearmap_certificates.tex`

Rationale:
Belongs in chapter 23 (LinearMap). Standard textbook stepping stone in Hungerford ch.IV §2 and Dummit & Foote §10.2 (linear transformations): every linear map sends -m to -f(m). Verified absent for ARBITRARY linear maps: grep `f\(-|negation.*linear|linear.*negation|linearmap-neg` returns no matching theorem statements. The chapter HAS thm:linearmap-zero-preservation-from-additivity (module_linearmap_certificates.tex:21) and thm:module-linearmap-pointwise-inverse-certificate (line 482, which CONSTRUCTS h(x) := -f(x) and shows h is linear — a different proposition), but the direct equality `f(-m) sim -f(m)` for arbitrary linear f is not stated. Closes in 1-2 rounds: source right-inverse `m +_V (-_V m) sim_V 0_V`; descent of f and additive-preservation row give `f(m) +_W f(-_V m) sim_W f(m +_V (-_V m)) sim_W f(0_V) sim_W 0_W` via thm:linearmap-zero-preservation-from-additivity; group inverse uniqueness closes. All prerequisites in chapter 23/group.

---

### B-178 - Polynomial: evaluation at scalar zero returns the constant term

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Polynomial: evaluation at scalar zero returns the constant term |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 9/10 |

Problem:
Under RingUp(R) and the polynomial Horner evaluation of def:polynomial-horner-evaluation, for every carried scalar a:R and every coefficient list t, (Eval_{0_R, R}(cons(a, t))) sim_R a.

Local inputs:
- `papers/bedc/parts/concrete_instances/25_polynomial_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/25_polynomial_literal_addtrim.tex`
- `papers/bedc/parts/concrete_instances/ring/18_ring_zero_absorption_from_distributivity.tex`

Rationale:
Belongs in chapter 25 (Polynomial). Standard textbook stepping stone in Hungerford ch.III §6 (Polynomial Rings) and Dummit & Foote §9.1: a polynomial evaluated at zero returns its constant term. Verified absent: grep `eval.*at.*zero|eval-zero-alpha|polynomial-eval-zero|polynomial-constant-term` across papers/bedc/parts returns NO matching theorem labels. The chapter has the Horner recursion (def:polynomial-horner-evaluation, line 27) `eval_α(cons(a, t)) := α · eval_α(t) + a` and lem:horner-evaluation-zero-tail-invariance and the additive/multiplicative homomorphism theorems but never specializes to α = 0_R. Closes in 1 round: the Horner cons clause at α = 0_R unfolds to `0_R cdot_R eval_{0_R, R}(t) +_R a`; thm:ring-mul-zero-absorption (ring/18_ring_zero_product_and_signed_square.tex:20) gives the multiplicand sim 0_R; thm:ring-add-right-zero (or ring additive left-unit row) gives 0_R +_R a sim_R a. All cited prerequisites already exist.

---

### B-179 - CommRing: square of a product equals product of squares

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | CommRing: square of a product equals product of squares |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 7/10 |

Problem:
Under a CommRingUp(R) certificate, for every carried a,b:R, ((a cdot_R b) cdot_R (a cdot_R b)) sim_R ((a cdot_R a) cdot_R (b cdot_R b)).

Local inputs:
- `papers/bedc/parts/concrete_instances/19_commring_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/commring/19_commring_algebraic_consequences.tex`
- `papers/bedc/parts/concrete_instances/commring/19_commring_core.tex`

Rationale:
Belongs in chapter 19 (CommRing). Standard textbook stepping stone in Hungerford ch.III §1 (Commutative Rings) and Dummit & Foote §7.3: in a commutative ring (ab)^2 = a^2 b^2. Verified absent: grep `commring.*sq.*prod|sq.*of.*prod|commring-sq-mul|mul-square|product.*square` returns NO matching theorem labels. The chapter HAS thm:commring-square-add-expand (square of a sum), thm:commring-square-signed-difference-expand (square of a difference), thm:commring-difference-of-squares, and thm:commring-parallelogram-square-sum, but not the square-of-product identity. Closes in 1 round: by multiplicative associativity, (ab)(ab) sim a(b(ab)); by commutativity (the multiplicative-commutativity field of commring stability certificate), b(ab) sim (ab)b; by associativity twice, this reaches a((ba)b) sim a(a(bb)) sim (aa)(bb). Uses only the multiplicative monoid and commutativity fields already in def:commring-stability-certificate.

---

### B-180 - Ring forgets to Monoid certificate

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Ring forgets to Monoid certificate |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 9/10 |

Problem:
If R carries a RingUp(R) certificate, then dropping the additive carrier (0_R, +_R, (-)_R, distributivity rows, additive-abelian-group stability rows, and ledger entries whose provenance uses + or unary minus) yields a MonoidUp(R) certificate over R with operation mul_R, identity 1_R, and the ring's classifier.

Local inputs:
- `papers/bedc/parts/concrete_instances/18_ring_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/ring/18_ring_certificate_and_additive_laws.tex`
- `papers/bedc/parts/concrete_instances/ring/18_ring_zero_product_and_signed_square.tex`
- `papers/bedc/parts/concrete_instances/15_monoid_namecert_construction.tex`

Rationale:
The dual companion to the previous candidate. ring/18_ring_certificate_and_additive_laws.tex:19 (def:ring-stability-certificate) names multiplicative-monoid laws (associativity, identity, congruence) as ring obligations, and these are realized by the singleton-empty-history ring instance at ring/18_ring_intro_and_singletons.tex. 15_monoid_namecert_construction.tex:104 (def:monoid-stability-certificate) and 15_monoid:523 (def:monoid-certificate-obligations) are the target obligations. `grep -rn 'ring-forgets-monoid\|ring-multiplicative-carrier' papers/bedc/parts/ --include='*.tex'` returns 0 matches, so the multiplicative reduct is genuinely unstated even though all the law fields it would project are already proved (cf. prop:monoid-forgets-semigroup-certificate at 57_semigroup:158 for the proof template).

---

### B-181 - TotalOrder forgets to Lattice certificate

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | TotalOrder forgets to Lattice certificate |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 10/10 |

Problem:
If C carries a TotalOrderUp(C) certificate, then defining x ∧ y as the trichotomy-selected lesser endpoint and x ∨ y as the trichotomy-selected greater endpoint yields a LatticeUp(C) certificate whose meet and join classifier-equal the trichotomy selectors.

Local inputs:
- `papers/bedc/parts/concrete_instances/29_totalorder_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/29_totalorder_namecert_carriers_and_unary_selectors.tex`
- `papers/bedc/parts/concrete_instances/29_totalorder_namecert_unary_context_laws.tex`
- `papers/bedc/parts/concrete_instances/30_lattice_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/lattice/the_certificate.tex`

Rationale:
Unlike the simpler downward forget projections, this one runs sideways and EXHIBITS lattice meet/join from totalorder selectors. The selector machinery is already in place: 29_totalorder_namecert_carriers_and_unary_selectors.tex:237 (thm:totalorder-prefix-least-upper-selector) and 29_totalorder_namecert_unary_context_laws.tex:2 (thm:totalorder-prefix-greatest-lower-selector) exhibit GLB and LUB witnesses on the unary-prefix model. lattice/the_certificate.tex:18 (def:lattice-stability-certificate) requires only those bound-characterization rows, which the trichotomy-driven selectors directly supply (cf. lem:lattice-meet-idempotence-from-bounds at lattice/the_certificate.tex:45 — its hypothesis IS the GLB rule). `grep -rn 'totalorder-forgets-lattice\|totalorder.*lattice.*forget' papers/bedc/parts/ --include='*.tex'` returns 0 hits. This is the natural classifier-level promotion theorem missing from the order/lattice chapter chain.

---

### B-182 - Field forgets to Ring certificate

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Field forgets to Ring certificate |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |

Problem:
If F carries a FieldUp(F) certificate, then composing the existing field→commring projection with the existing commring→ring projection yields a RingUp(F) certificate over the same scalar carrier, classifier, +_F, 0_F, (-)_F, mul_F, and 1_F.

Local inputs:
- `papers/bedc/parts/concrete_instances/20_field_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/field/20_field_certificate_record.tex`
- `papers/bedc/parts/concrete_instances/19_commring_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/commring/19_commring_core.tex`
- `papers/bedc/parts/concrete_instances/18_ring_namecert_construction.tex`

Rationale:
field/20_field_certificate_record.tex:206 (thm:field-certificate-forgets-commring-certificate) and commring/19_commring_core.tex:229 (prop:commring-forgets-ring-certificate) both exist; the natural composite is the direct Field → Ring projection, but `grep -rn 'field-forgets-ring\|field-ring-projection' papers/bedc/parts/ --include='*.tex'` returns 0 hits. The corresponding two-step composite is exactly the construction used implicitly throughout 22_vecspace_namecert_construction.tex:495 (cor:vecspace-additive-carrier-projection) — the ring-side reduct of a field-side certificate. Promoting that implicit composite to a labeled corollary unblocks consumer chapters (vecspace, linearmap, polynomial) that currently re-derive the projection in prose.

---

### B-183 - AbGroup forgets to Monoid certificate

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | AbGroup forgets to Monoid certificate |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |

Problem:
If C carries an AbGroupUp(C) certificate, then dropping the additive-inverse field, the commutativity field, and inverse-witness ledger entries yields a MonoidUp(C) certificate over the same carrier, classifier, addition operation, and zero element.

Local inputs:
- `papers/bedc/parts/concrete_instances/17_abgroup_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/16_group_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/group/16_group_certificate_tail.tex`
- `papers/bedc/parts/concrete_instances/15_monoid_namecert_construction.tex`

Rationale:
prop:abgroup-forgets-group-certificate (17_abgroup:722) and prop:group-forgets-monoid-certificate (group/16_group_certificate_tail.tex:103) both exist; the direct AbGroup → Monoid projection (skipping Group) is unstated. `grep -rn 'abgroup-forgets-monoid\|abgroup-monoid-projection' papers/bedc/parts/ --include='*.tex'` returns 0 hits. This is the additive analogue of the field-forgets-ring candidate above and uses the same composite-corollary pattern. Justification for separateness: 21_module_namecert_construction.tex:553 explicitly relies on 'the additive abelian-group laws' as a single bundle but never names this bundle through the monoid certificate, and the linearmap chapter (linearmap/module_linearmap_certificates.tex:13) re-derives the additive monoid each time it needs a unit-and-associativity reduct.

---

### B-184 - Opposite ring carries a Ring certificate

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Opposite ring carries a Ring certificate |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 9/10 |

Problem:
If C carries a RingUp(C) certificate with addition +, multiplication ·, additive identity 0, multiplicative identity 1, additive inverse −, and classifier ~_C, then defining ·^op by a ·^op b := b · a and reusing all other data yields a RingUp(C) certificate with the same carrier C, addition +, additive identity 0, multiplicative identity 1, additive inverse −, classifier ~_C, and reversed multiplication ·^op.

Local inputs:
- `papers/bedc/parts/concrete_instances/ring/18_ring_certificate_and_additive_laws.tex`
- `papers/bedc/parts/concrete_instances/ring/18_ring_intro_and_singletons.tex`
- `papers/bedc/parts/concrete_instances/functor/certificate_obligations.tex`

Rationale:
An opposite-ring construction is a canonical algebraic invariant that mirrors the well-developed opposite-functor and opposite-category constructions in the same project: `Opposite functor certificate` exists at functor/certificate_obligations.tex:326 and `Double opposite functor certificate data identity` at functor/certificate_obligations.tex:641; analogously `Double opposite category certificate data identity` exists at 36_category_namecert_construction.tex:352. Yet no opposite-ring construction exists: grep `opposite.*ring|ring.*opposite|R\^op|opp.*ring` across parts/ returns zero matches (only category/functor/nattrans hits and 'integer canonical opposite-sign' which is unrelated). The construction reuses the AbGroup additive structure unchanged and reverses multiplication, with associativity (b·a)·c = b·(a·c) → c·(b·a) = (c·b)·a being symmetric, and distributivity reversing direction (left↔right). Additionally a CommRing→CommRing^op = CommRing identity follows immediately and would parallel the double-opposite identity for functors and categories. The ring intro (ring/18_ring_intro_and_singletons.tex:4) emphasizes ring is licensed by AbGroup+Monoid+distributivity, all of which transport cleanly under multiplication reversal.

---

### B-185 - Group commutator symmetry: inv(comm(a,b)) hsame comm(b,a)

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Group commutator symmetry: inv(comm(a,b)) hsame comm(b,a) |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
Under group laws (associativity, two-sided identity, multiplication congruence, two-sided inverses), for all a,b in BHist, hsame(inv(comm(a,b)), comm(b,a)).

Local inputs:
- `papers/bedc/parts/concrete_instances/group/namecert_construction_core/02_certificate.tex`
- `papers/bedc/parts/concrete_instances/16_group_namecert_construction.tex`
- `lean4/BEDC/Derived/GroupUp/`

Rationale:
Hungerford ch.I.4 / Dummit-Foote 5.4: [a,b]^{-1} = [b,a] is a one-line consequence of inverse-reversal. comm(a,b) = ab(a^{-1}b^{-1}); apply thm:group-inverse-mul-reverse twice and thm:group-left-inverse-involutive twice. Verified absent: grep 'commutator-symm|commutator.*inverse|comm\(b,a\)' inside group/ returns no theorem. All prerequisites already \leanchecked at 02_certificate.tex lines 33-185. 1-round closeable.

---

### B-186 - Ring negation classifier exactness: -x hsame -y iff x hsame y

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Ring negation classifier exactness: -x hsame -y iff x hsame y |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
Under additive group laws (associativity, commutativity, left-zero, left-inverse, addition congruence, additive-inverse congruence) on BHist, for every x,y: hsame(neg(x), neg(y)) iff hsame(x, y).

Local inputs:
- `papers/bedc/parts/concrete_instances/ring/18_ring_certificate_and_additive_laws.tex`
- `papers/bedc/parts/concrete_instances/18_ring_namecert_construction.tex`
- `lean4/BEDC/Derived/RingUp/`

Rationale:
Hungerford ch.III §1 / Dummit-Foote §7.1: 'in any abelian group / ring, additive inverse is injective.' Grep confirms no neg-injectivity / neg-classifier-exact theorem exists in ring/, commring/, or field/. Forward: from -x ~ -y and x + (-x) ~ 0, additive cancellation gives x ~ y. Reverse: additive-inverse congruence transports x ~ y across neg directly. Both directions short. Pairs naturally with thm:ring-additive-difference-zero-exact already in the same file. 1-round closeable.

---

### B-187 - Composition of split monomorphisms is a split monomorphism

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Composition of split monomorphisms is a split monomorphism |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 9/10 |

Problem:
In any CategoryUp certificate, if f:a->b and g:b->c both carry split-monomorphism witnesses with left inverses f' and g' respectively, then g comp f : a -> c carries a split-monomorphism witness whose left inverse is f' comp g'.

Local inputs:
- `papers/bedc/parts/concrete_instances/functor/certificate_obligations.tex`
- `papers/bedc/parts/concrete_instances/36_category_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/category/`

Rationale:
Mac Lane CWM I.5 Prop 1 / Riehl 1.2.10: closure of split-mono under composition by associativity and unit law. Verified: def:category-split-monomorphism exists at functor/certificate_obligations.tex line 391 and thm:functor-preserves-split-monomorphism exists at line 391+, but no closure-under-composition theorem. Prerequisites all present (composition closure, associativity, identity-square via cor:category-hom-carrier-stability-law-package). Distinct from B-11 (functor preserves hom-carrier under composition). 1-round closeable.

---

### B-188 - ListPublicAppend left-identity at the nil-represented endpoint

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | ListPublicAppend left-identity at the nil-represented endpoint |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
If e:BHist satisfies ListSpineRep_A(e, nil) and h satisfies ListHistoryCarrier_A(h), then ListPublicAppend_A(e, h, h).

Local inputs:
- `papers/bedc/parts/concrete_instances/list/11_represented_spine_append_context.tex`
- `papers/bedc/parts/concrete_instances/11_list_namecert_construction.tex`
- `lean4/BEDC/Derived/ListUp/`

Rationale:
Bird-Wadler / Pierce TAPL §3 / introductory algebra (Birkhoff-Mac Lane): nil ++ xs = xs is the very first algebraic law for ++ in any free-monoid presentation. Currently the chapter states ListPublicAppend totality + congruence + length-additivity, but the explicit unit law ListPublicAppend(nil, h, h) is missing — grep across list/ returns no `nil_append`, `append_left_unit`, or `append_right_unit` matches. Closure: append/spine-rep machinery is fully present (nil ListSpineRep clause + lem:list-spine-append-representation-construction). 1-round closeable. Sister to thm:preorder-prefix-empty-left-iff-unary already stated in chapter 27.

---

### B-189 - Identity natural transformation as a full NatTransUp certificate

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Identity natural transformation as a full NatTransUp certificate |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
For any FunctorUp certificate F : C -> D, there is a NatTransUp certificate id_F : F => F whose component at every object x is the D-identity id_(F_0(x)) and whose naturality square at every source morphism u : a -> b is the identity-naturality witness via category identity-square closure.

Local inputs:
- `papers/bedc/parts/concrete_instances/nattrans/vertical_and_opposite_extras.tex`
- `papers/bedc/parts/concrete_instances/38_nattrans_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/37_functor_namecert_construction.tex`

Rationale:
Mac Lane CWM II.4 Prop 1 / Riehl 1.4.1: identity nat-trans is a NatTransUp certificate. Currently thm:nattrans-prefix-identity-naturality-square exists at the prefix-component level only (line 697 of 38_nattrans_namecert_construction.tex); the abstract certificate-level wrapper packaging this as a full NatTransUp instance from F to F is missing. The opposite-natural-transformation chapter implicitly assumes such an instance exists. Closes the gap before vertical composition with itself (degenerate case). 1-round closeable.

---

### B-190 - Module scalar negation acts as additive inverse of scalar action

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (codex) |
| Object | Module scalar negation acts as additive inverse of scalar action |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |

Problem:
Under a $\ModuleUp(R,M)$ certificate, for carried $r:R$ and $m:M$, $((-_R r)\odot_M m)+_M(r\odot_M m)\sim_M 0_M$.

Local inputs:
- `papers/bedc/parts/concrete_instances/21_module_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/19_commring_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/18_ring_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/17_abgroup_namecert_construction.tex`

Rationale:
Cleanly fits chapter 21 (module name certificate) as a sibling to the scalar associativity and additivity targets already on the board (B-08, B-19, B-20, B-23, B-24). The existing module entries all probe associativity, additivity, congruence, and unit obligations — none address how the ring's negation transports through the scalar action to produce the module's additive inverse. The claim is a single concrete implication 'P implies Q under setup S' (setup: $\ModuleUp(R,M)$; conclusion: classifier-equality $\sim_M$), and it surfaces a missing piece of module-certificate behavior that future ring-module bridge work will need. No matching theorem label in `paper_coverage` (closest is `def:abgroup-unary-scalar-torsion`, which is structurally distinct).

---

### B-191 - Ring right distributivity over subtraction

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (codex) |
| Object | Ring right distributivity over subtraction |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 7/10 |
| Novelty | 6/10 |

Problem:
Under RingUp(R), for any a, b, c in R, (a -_R b) *_R c is history-same to (a *_R c) -_R (b *_R c) up to the ring classifier.

Local inputs:
- `papers/bedc/parts/concrete_instances/18_ring_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/19_commring_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/17_abgroup_namecert_construction.tex`

Rationale:
Concrete derived theorem at the same granularity as B-07 (lattice idempotence/absorption), B-08 (module scalar associativity), and B-09 (polynomial normalize commutativity): ring chapter records distributivity and additive-inverse fields as obligations, but no labeled theorem in the visible coverage proves the subtraction-form right distributivity. The proof routes through right distributivity over addition plus the (-b)*c = -(b*c) lemma — itself unproven on the board — making this a concrete certificate-projection target rather than a paraphrase of an existing entry. Distinct from B-08 (module scalar action), B-09 (polynomial normalization), B-23 (module representative transport), and B-28 (CommRing→Ring forgetful), which all treat different ring-adjacent obligations. Fits cleanly in concrete_instances/18_ring_namecert_construction.tex.

---

### B-192 - Polynomial raw addition commutativity from scalar additive commutativity

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Polynomial raw addition commutativity from scalar additive commutativity |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 10/10 |
| Novelty | 8/10 |

Problem:
Under a RingUp scalar carrier with classifier $\sim_R$, addition $+$, and additive abelian-group fields, for all finite coefficient spines $p,q:\mathsf{ListCarrier}(R)$, $\mathsf{PolySame}_R(\mathsf{radd}_R(p,q),\mathsf{radd}_R(q,p))$.

Local inputs:
- `papers/bedc/parts/concrete_instances/25_polynomial_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/ring/18_ring_certificate_and_additive_laws.tex`
- `papers/bedc/parts/concrete_instances/11_list_namecert_construction.tex`

Rationale:
Concrete instance / chapter 25 polynomial. Review category 4 (missing companion result). Chapter 25:5 says 'Polynomial addition and multiplication are derived operations governed by the ring's certificate fields' but no theorem states that radd commutes; the chapter has trim compatibility (thm:polynomial-raw-add-two-sided-trim-compatibility, line 685), zero-tail invariance (prop:polynomial-raw-add-right-zero-tail-invariance, line 716), and even Horner additivity (lem:horner-evaluation-raw-additive), yet grep for 'PolySame.*radd.*radd' returns only directional trim/zero-tail forms — never the symmetric input swap. Distinct from B-09 (normalize commutes with add+mul on inputs), B-30 (two-sided trim compatibility), and B-31 (right zero-tail). Required prerequisites all exist: RingUp additive commutativity is a stability field (def:ring-stability-certificate, item 1, abelian-group laws), addition congruence is a stability field, the radd recursion is fixed in def:polynomial-raw-add-comparison-data, ListClassifierSpec transitivity is in 11_list_namecert_construction. Closeable in 1-2 rounds via simultaneous induction on the cons-cons / nil-cons / cons-nil / nil-nil branches of the radd recursion, applying additive commutativity in the cons-cons head case and the additive zero laws in the boundary cases.

---

### B-193 - Polynomial raw addition associativity from scalar additive associativity

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Polynomial raw addition associativity from scalar additive associativity |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
Under a RingUp scalar carrier with classifier $\sim_R$, additive abelian-group fields, and addition congruence, for all finite coefficient spines $p,q,r:\mathsf{ListCarrier}(R)$, $\mathsf{PolySame}_R(\mathsf{radd}_R(\mathsf{radd}_R(p,q),r),\mathsf{radd}_R(p,\mathsf{radd}_R(q,r)))$.

Local inputs:
- `papers/bedc/parts/concrete_instances/25_polynomial_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/ring/18_ring_certificate_and_additive_laws.tex`
- `papers/bedc/parts/concrete_instances/11_list_namecert_construction.tex`

Rationale:
Concrete instance / chapter 25 polynomial. Review category 4 (missing companion). The chapter introduces radd to express the abelian-group law of polynomial addition, and Horner evaluation is shown additive (thm:polynomial-evaluation-additive-homomorphism), yet associativity of radd itself is never stated — grep 'radd.*assoc|polynomial.*assoc' returns no hit in chapter 25 and in the polynomial subdirectory. The companion to B-09/B-30/B-31, which develop normalize-trim compatibility, is the underlying associativity from which those compatibilities are usually derived; without it the chapter relies on an implicit appeal. Required prerequisites all present: ring additive associativity is in def:ring-stability-certificate item 1 (abelian-group laws), addition congruence is item 3, list classifier transitivity is in 11_list_namecert. Closeable in 1-2 rounds via outer induction on $p$ following the radd recursion, with the cons-cons-cons head case using additive associativity once and addition congruence on the tail induction step.

---

### B-194 - Polynomial raw multiplication commutativity from CommRing scalar commutativity

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Polynomial raw multiplication commutativity from CommRing scalar commutativity |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 9/10 |

Problem:
Under a CommRingUp scalar carrier with classifier $\sim_R$ and multiplicative commutativity field, for all finite coefficient spines $p,q:\mathsf{ListCarrier}(R)$, $\mathsf{PolySame}_R(\mathsf{rmul}_R(p,q),\mathsf{rmul}_R(q,p))$.

Local inputs:
- `papers/bedc/parts/concrete_instances/25_polynomial_literal_addtrim.tex`
- `papers/bedc/parts/concrete_instances/25_polynomial_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/19_commring_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/ring/18_ring_certificate_and_additive_laws.tex`

Rationale:
Concrete instance / chapter 25 polynomial. Review category 4 (missing companion). The chapter defines the raw Cauchy product rmul_R (def:polynomial-raw-cauchy-product, line 199), proves multiplicative Horner homomorphism (thm:polynomial-evaluation-multiplicative-homomorphism, line 321), and the introduction text on line 4 states polynomial multiplication is governed by the ring's certificate fields. But no theorem states symbolic commutativity of rmul itself — grep 'rmul.*comm|polynomial.*mult.*comm' returns 0 hits. Distinct from B-22 (zero-tail invariance for multiplication, a one-sided length-extension invariant) and from B-09 (which conjoins normalize-commutes-with-mul, an input-normalization claim). Required prerequisites all present: CommRingUp multiplicative commutativity is in def:commring-stability-certificate (used in lem:horner-evaluation-raw-scalar-product, line 245), rscale_R and shift_R recursion in def:polynomial-raw-cauchy-product, raw additivity is the proven lem:horner-evaluation-raw-additive. Closeable in 2-3 rounds via outer induction on the left input through the rscale-shift-radd recursion, then a paired inner induction over the right input swapping coefficient orders by scalar commutativity, with the shift-coefficient interaction unfolded through the right distributive field.

---

### B-195 - Bundle append membership commutativity

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Bundle append membership commutativity |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 6/10 |

Problem:
For probe $p$ and bundles $\Pi,\Theta$, $p\in\BAppend(\Pi,\Theta)\Longleftrightarrow p\in\BAppend(\Theta,\Pi)$.

Local inputs:
- `papers/bedc/parts/core/probe_bundles/01_bundle_grammar.tex`
- `lean4/BEDC/FKernel/Bundle.lean`

Rationale:
Core / probe_bundles. Review category 7 (composite consequence). Chapter 05/01_bundle_grammar has thm:bundle-append-membership (line 249, $p\in\BAppend(\Pi,\Theta)\iff p\in\Pi\lor p\in\Theta$, \leanchecked) and thm:bundle-ask-policy-append-comm (line 396, BundleAskPolicy under append swap, \leanchecked) but the simpler theorem stating the membership predicate itself is symmetric under append swap is absent — grep 'bundleAppend.*comm|append.*membership.*comm' returns 0 dedicated theorems. The companion to BundleAskPolicy commutation, at the membership layer, is the missing piece: BundleAskPolicy commutation pulls back along the membership commutation but currently has to rebuild via two append-membership applications inline. Required infrastructure all proven and \leanchecked. Closeable in 1 round via thm:bundle-append-membership applied to both directions and disjunction commutativity.

---

### B-196 - Opposite monoid carries a Monoid certificate

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (codex) |
| Object | Opposite monoid carries a Monoid certificate |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |

Problem:
If C carries MonoidUp(C) with multiplication \cdot, then C with multiplication a \cdot^{op} b := b \cdot a carries MonoidUp(C).

Local inputs:
- `papers/bedc/parts/concrete_instances/05_add_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/17_abgroup_namecert_construction.tex`
- `papers/bedc/parts/core/08_typed_naming_certificates.tex`

Rationale:
Opposite-structure constructions are a foundational concrete_instances theorem and currently have no presence on the BOARD or in paper labels. The result is non-trivial in the certificate framework: associativity must be transported (a \cdot^{op} b) \cdot^{op} c = c \cdot (b \cdot a) = (c \cdot b) \cdot a = a \cdot^{op} (b \cdot^{op} c), unit fields must transfer on both sides, and pattern/ledger/classifier rows must be re-verified for the swapped operation. Distinct from B-28 (forgetful CommRing→Ring) — that is structure-projection, this is structure-reversal. Establishes the prerequisite for any later opposite-Ring or opposite-Category sibling work.

---

### B-197 - Opposite semigroup carries a Semigroup certificate

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (codex) |
| Object | Opposite semigroup carries a Semigroup certificate |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
If a carrier C with multiplication ∗ has SemigroupUp(C, ∗), then C with the reversed multiplication x⋆y := y∗x has SemigroupUp(C, ⋆) on the same carrier and classifier.

Local inputs:
- `papers/bedc/parts/concrete_instances/15_semigroup_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/14_monoid_namecert_construction.tex`
- `papers/bedc/parts/core/08_typed_naming_certificates.tex`

Rationale:
BEDC's semigroup certificate is currently asserted in only one orientation — every existing concrete-instances theorem on the BOARD lives at the lattice / module / polynomial / category layer, and no entry exercises the symmetry of the associativity / pattern / ledger fields under reversal of the binary operation. The claim is a clean implication 'SemigroupUp(C,∗) ⇒ SemigroupUp(C,⋆)' that exposes which certificate fields are intrinsically reversal-symmetric (associativity, same-source determinacy, pattern soundness) and which would need restatement (any handed obligations). It is foundational for downstream opposite-monoid / opposite-group theorems and would not duplicate any existing BOARD entry or paper-side `\label`. Fit is high because it sits squarely in concrete_instances next to the existing semigroup namecert construction; novelty is high because the opposite-construction theme is entirely absent from the current BOARD and paper coverage.

---

### B-198 - Opposite group carries a Group certificate

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (codex) |
| Object | Opposite group carries a Group certificate |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |

Problem:
If GroupUp(C, ∗, e, (·)⁻¹) holds, then GroupUp(C, ⋆, e, (·)⁻¹) holds, where x⋆y := y∗x and the identity and inverse data are unchanged.

Local inputs:
- `papers/bedc/parts/concrete_instances/16_group_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/17_abgroup_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/15_semigroup_namecert_construction.tex`
- `papers/bedc/parts/core/08_typed_naming_certificates.tex`

Rationale:
This is the group-level counterpart to the opposite-semigroup theorem and is independently meaningful because the GroupUp certificate carries inverse-and-identity stability fields beyond the semigroup ones. The substantive content is that the existing inverse-and-unit obligations (left/right cancellation, e as two-sided unit, x⁻¹ as two-sided inverse) survive multiplication reversal without re-choosing the inverse map — i.e. the inverse data itself is reversal-invariant. No existing BOARD entry treats opposite groups, no paper `\label` matches (only direct group certificate definitions appear), and the result is a foundational stepping stone for any later opposite-monoid / opposite-ring instance. Fit is high in concrete_instances; novelty is somewhat reduced because of adjacency to the opposite-semigroup candidate, but the inverse / identity content is independent enough to warrant its own loop slot, in line with how the BOARD already separates B-25 and B-26 for lattice commutativity vs. associativity.

---

### B-199 - Kernel and image inherit module classifiers

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | Kernel and image inherit module classifiers |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 9/10 |

Problem:
Under LinearmapUp(f:M→N), the predicate-defined Kernel(f) and Image(f) carriers close under 0, addition, negation, and scalar action, and therefore inherit the ModuleUp classifier.

Local inputs:
- `papers/bedc/parts/concrete_instances/22_linearmap_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/21_module_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/17_abgroup_namecert_construction.tex`

Rationale:
The linearmap chapter has predicate definitions for kernel and image but no labeled theorem promoting them to inherited module certificates. This is the canonical sub-object closure result for linear maps and is structurally distinct from B-08/B-23 (which are about scalar associativity transport on the ambient module), so it does not duplicate any existing BOARD slot or paper label.

---

### B-200 - Matrix product associativity from scalar folds

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | Matrix product associativity from scalar folds |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 9/10 |

Problem:
Under MatrixUp over RingUp(R), if matrix multiplication is defined by finite additive scalar folds and ring multiplication, then for matching dimensions (A·B)·C ∼ A·(B·C) holds under the entrywise matrix classifier.

Local inputs:
- `papers/bedc/parts/concrete_instances/23_matrix_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/18_ring_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/19_commring_namecert_construction.tex`

Rationale:
The matrix chapter currently only carries carrier/source/pattern/classifier/stability definitions without any labeled theorem proving the central structural law of matrix multiplication. The proof must connect ring distributivity, ring associativity, and finite scalar fold reindexing — a soundness theorem that is not addressed by the polynomial-convolution targets B-09/B-22.

---

### B-201 - Metric ball budgets compose

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | Metric ball budgets compose |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 7/10 |

Problem:
Under MetricUp(X,d), if Ball_r(x,y) and Ball_s(y,z) hold, then Ball_{r+s}(x,z) follows from the metric classifier and the triangle stability field.

Local inputs:
- `papers/bedc/parts/concrete_instances/32_metric_namecert_construction.tex`

Rationale:
The metric chapter defines metric-ball-budget-predicate, classifier, and stability certificate, but no labeled theorem promotes triangle stability into a ball-budget transitivity statement. It is a small but reusable closure lemma for multiscale arguments, distinct from B-12 (continuous modulus composition) which targets uniform continuity moduli rather than ball budgets.

---

### B-202 - Compact two-step finite-net gluing

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | Compact two-step finite-net gluing |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 9/10 |

Problem:
Under CompactUp(K) with finite-net setup, if N is an ε-net for K and each local block B(n,ε) has a finite δ-net N_n, then the union ⋃_{n∈N} N_n is a finite (ε+δ)-net for K.

Local inputs:
- `papers/bedc/parts/concrete_instances/33_compact_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/32_metric_namecert_construction.tex`

Rationale:
The compact chapter defines compact-finite-refinement-chain, compact-net-two-step-factor, and uniform finite-net data, but no labeled theorem packages the two-step factor as a multiscale finite-net gluing principle. This is a high-value local-to-global closure theorem provable from finite unions plus the metric ball-budget triangle, and it does not duplicate any existing BOARD entry.

---

### B-203 - Strict zero divisor obstructs FieldUp

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | Strict zero divisor obstructs FieldUp |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 10/10 |
| Novelty | 9/10 |

Problem:
Under CommRingUp(R), if there exist strict zero-divisor witnesses a,b with a≠0, b≠0, and a·b∼0, then no FieldUp upgrade exists that preserves the same 0, 1, multiplication, classifier, and apartness.

Local inputs:
- `papers/bedc/parts/concrete_instances/19_commring_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/20_field_namecert_construction.tex`

Rationale:
The commring chapter already encodes strict zero-divisor data and the field chapter encodes zero-apartness, but the BOARD only has the forgetful positive direction (cor:field-certificate-forgets-to-ring-certificate). A negative obstruction theorem is the natural counterpart: short to prove (multiply b's inverse on both sides of a·b∼0 to derive a∼0, contradicting apartness), high-value as an explicit boundary on field-upgrade admissibility.

---

### B-204 - Opposite category certificate involution

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | Opposite category certificate involution |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
Under CategoryUp(C) with opposite-category certificate data, the doubly-opposite (C^op)^op has the same objects, hom-carrier classifier, identity, and composition classifier as C.

Local inputs:
- `papers/bedc/parts/concrete_instances/36_category_namecert_construction.tex`

Rationale:
The category chapter defines opposite-category-certificate-data but no theorem promotes the double opposite to a certificate-level identification. This is the rigidity/representation theorem missing from the otherwise definition-heavy category chapters and is orthogonal to B-11 (functor composition) and B-14 (nattrans composition).

---

### B-205 - Preorder quotient yields PosetUp

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | Preorder quotient yields PosetUp |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 9/10 |

Problem:
Under PreorderUp(X,≤), defining x≈y iff x≤y and y≤x and equipping the quotient carrier with the induced order yields a PosetUp whose quotient classifier exactly classifies ≈-equivalence classes.

Local inputs:
- `papers/bedc/parts/concrete_instances/27_preorder_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/28_poset_namecert_construction.tex`

Rationale:
Both preorder and poset chapters carry certificate definitions, but the canonical exactness theorem connecting them — preorder-to-poset quotient — is missing from the BOARD and the paper labels. It is a foundational structural result that explains where poset antisymmetry concretely arises and is independent of the lattice/totalorder targets already on the board.

---

### B-206 - Normalizer quotient conjugation is well-defined

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | Normalizer quotient conjugation is well-defined |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 9/10 |

Problem:
Under GroupUp(G) with sub-carrier S, for n,n'∈N_G(S): n^{-1}n'∈C_G(S) implies n s n^{-1} ∼ n' s n'^{-1} for all s∈S, and conversely pointwise equal conjugation implies n^{-1}n'∈C_G(S).

Local inputs:
- `papers/bedc/parts/concrete_instances/16_group_namecert_construction.tex`

Rationale:
The group chapter has definitions for center, centralizer, normalizer, the centralizer-normalizer quotient classifier, and the orbit relation, but no labeled theorem promoting the quotient-action data to a well-definedness/kernel-classification statement. This is the substantive group-theoretic soundness theorem behind those definitions and uses only group inverses, associativity, and conjugation stability.

---

### B-207 - CommRing subring inclusion transitivity

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | CommRing subring inclusion transitivity |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |

Problem:
Under CommRingUp(A), CommRingUp(B), CommRingUp(C), if A→B and B→C each carry a subring-inclusion name certificate preserving 0, 1, addition, multiplication, and classifier, then the composite A→C carries a subring-inclusion name certificate of the same form.

Local inputs:
- `papers/bedc/parts/concrete_instances/19_commring_namecert_construction.tex`

Rationale:
The commring chapter defines commring-subring-inclusion-name-certificate, but no labeled theorem records closure of inclusion certificates under composition. It is a short transitive-closure result that is genuinely distinct from B-28 (the CommRing→Ring forgetful projection) and is needed to justify chained subring constructions throughout concrete_instances.

---

### B-208 - Opposite preorder certificate

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Opposite preorder certificate |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 7/10 |

Problem:
If (C, sim_C, le_C) satisfies the PreorderUp certificate obligations, then the data (C, sim_C, le_C^op) with a le_C^op b := b le_C a also satisfies the PreorderUp certificate obligations.

Local inputs:
- `papers/bedc/parts/concrete_instances/27_preorder_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/15_monoid_namecert_construction.tex`

Rationale:
Belongs in the Preorder chapter (`27_preorder_namecert_construction.tex`). Textbook-standard order theory (Davey-Priestley ch.1 'Order theory and lattices': every preorder has a dual). Proof template already used 7 times in the manuscript: monoid (`thm:opposite-monoid-certificate` at `15_monoid_namecert_construction.tex:550`), semigroup (`prop:opposite-semigroup-certificate` at `57_semigroup_namecert_construction.tex:226`), group (`thm:opposite-group-certificate` at `group/16_group_certificate_tail.tex:132`), ring (`thm:opposite-ring-certificate` at `ring/18_ring_certificate_and_additive_laws.tex:202`), category, functor, nattrans. Verified absent: grep for `opposite-preorder` returns 0 labeled theorems anywhere under `papers/bedc/parts/`. All proof obligations exist: preorder reflexivity/transitivity rows in `def:preorder-stability-certificate`, classifier symmetry in the carrier classifier core. Closes in 1-2 rounds because the proof is a literal 5-field projection: pattern stays 'comparison expression formation', classifier unchanged, stability fields just exchange the two arguments of transitivity.

---

### B-209 - Opposite poset certificate

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Opposite poset certificate |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 7/10 |

Problem:
If (C, sim_C, le_C) satisfies the PosetUp certificate obligations, then the data (C, sim_C, le_C^op) with a le_C^op b := b le_C a also satisfies the PosetUp certificate obligations.

Local inputs:
- `papers/bedc/parts/concrete_instances/28_poset_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/15_monoid_namecert_construction.tex`

Rationale:
Belongs in the Poset chapter (`28_poset_namecert_construction.tex`). Textbook-standard: every poset has a dual poset (Davey-Priestley ch.1; Stanley EC1 §3.1). Proof template is the same opposite-X-certificate template used 7 times (see Opposite preorder rationale for sites). Verified absent: grep for `opposite-poset` / `dual-poset` in `papers/bedc/parts/concrete_instances/` returns 0 labeled theorems; the only 'opposite' content in poset-related chapters is `thm:lattice-opposite-absorption-from-directional-bounds` which is a partial absorption-orientation swap, not the full dual poset. Closes in 1-2 rounds: extends the preorder-opposite proof with one extra paragraph showing antisymmetry is symmetric in its two comparison witnesses (if a le b and b le a then sim, and the same holds with arguments swapped). All needed fields are in `def:poset-stability-certificate` (line 21+ of `28_poset_namecert_construction.tex`).

---

### B-210 - Opposite lattice certificate (full duality)

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Opposite lattice certificate (full duality) |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 10/10 |
| Novelty | 8/10 |

Problem:
If (C, sim_C, le_C, meet_C, join_C) satisfies the LatticeUp certificate obligations, then the data (C, sim_C, le_C^op, join_C, meet_C) with le^op reversed and meet/join swapped also satisfies the LatticeUp certificate obligations.

Local inputs:
- `papers/bedc/parts/concrete_instances/lattice/the_certificate.tex`
- `papers/bedc/parts/concrete_instances/30_lattice_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/15_monoid_namecert_construction.tex`

Rationale:
Belongs in the Lattice chapter (`lattice/the_certificate.tex`). Textbook-standard duality (Birkhoff Lattice Theory ch.I §6 'Duality principle'; Davey-Priestley §1.18). Proof template same as opposite-monoid. The board's B-27 ('Lattice opposite absorption from directional bounds') is the partial absorption-only orientation swap; the full duality theorem is distinct because it transports the entire LatticeUp certificate (le, meet, join, all stability fields) and depends on the proposed Opposite poset certificate above. Verified absent: `grep 'opposite-lattice'` in `papers/bedc/parts/concrete_instances/` returns only `lattice-opposite-absorption-from-directional-bounds`, which is the four absorption orientations, not the dual lattice as a whole. Closes in 2-3 rounds: meet upper-bound rows of the dual become the original join lower-bound rows (greatest lower bound under reversed order = least upper bound under original); each of the six bound-characterization fields in `def:lattice-stability-certificate:21-28` swaps. All needed lemmas exist (`lem:lattice-meet-idempotence-from-bounds`, etc.).

---

### B-211 - FPS addition commutativity from scalar additive commutativity

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | FPS addition commutativity from scalar additive commutativity |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 7/10 |

Problem:
Under FormalPowerSeriesUp(R) over a scalar ring R whose additive operation +_R is commutative, the FPS addition F oplus G is classifier-equal to G oplus F: for every unary index n, (F oplus G)_n sim_R (G oplus F)_n, hence F oplus G sim_fps G oplus F.

Local inputs:
- `papers/bedc/parts/concrete_instances/26_fps_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/18_ring_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/25_polynomial_literal_addtrim.tex`

Rationale:
Belongs in the FPS chapter (`26_fps_namecert_construction.tex`). Textbook-standard (Niven Zuckerman Montgomery ch.II 'Formal power series form a commutative ring'; Wilf generatingfunctionology §2.2). The polynomial chapter has the exact direct analog: `thm:polynomial-raw-add-commutativity-from-scalar-additive-commutativity` at `25_polynomial_literal_addtrim.tex:475`. The FPS chapter has only `thm:fps-cauchy-product-classifier-congruence` at line 339; no addition-commutativity theorem. Verified absent: `grep 'fps.*add.*comm\|fps-addition-commutativity'` returns 0 labeled theorems. Closes in 1-2 rounds: the FPS addition is defined pointwise, so commutativity is exactly the pointwise scalar additive commutativity row of `def:ring-stability-certificate`; the FPS classifier is the pointwise classifier of `def:fps-classifier-specification`, and the proof uniformly quantifies over n. No new infrastructure; the polynomial proof at `25_polynomial_literal_addtrim.tex:475` is the line-by-line template.

---

### B-212 - FPS Cauchy product commutativity from CommRing scalars

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | FPS Cauchy product commutativity from CommRing scalars |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 7/10 |

Problem:
Under FormalPowerSeriesUp(R) where R carries a CommRingUp certificate, for every unary index n the n-th coefficient of F odot G is classifier-equal to the n-th coefficient of G odot F, hence F odot G sim_fps G odot F.

Local inputs:
- `papers/bedc/parts/concrete_instances/26_fps_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/19_commring_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/25_polynomial_literal_addtrim.tex`

Rationale:
Belongs in the FPS chapter (`26_fps_namecert_construction.tex`). Textbook-standard: for commutative scalars, the Cauchy product on formal power series is commutative (Wilf generatingfunctionology §2.2; Niven-Zuckerman-Montgomery ch.II). The polynomial chapter has the direct analog: `thm:polynomial-raw-multiplication-commutativity-from-commring-scalars` at `25_polynomial_literal_addtrim.tex:565`. Verified absent: grep for `fps.*cauchy.*comm\|fps-cauchy-product-commut` returns 0 labeled theorems; FPS chapter has only the congruence theorem. Closes in 1-2 rounds: the Cauchy product `(F odot G)_n = fold_+ (CauchySp_n(F,G))` from `def:fps-cauchy-coefficient-spine` is symmetric in F and G when scalar multiplication commutes, since the spine `Split(n) = {(i,j) : i+j=n}` is symmetric under (i,j) -> (j,i). All needed lemmas exist: `thm:finite-additive-fold-congruence-coefficient-lists` at `25_polynomial_namecert_construction.tex:513`, `prop:commring-forgets-ring-certificate` at `commring/19_commring_core.tex:231`.

---

### B-213 - Ring forgets to AbGroup certificate (additive)

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Ring forgets to AbGroup certificate (additive) |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 7/10 |

Problem:
If R carries a RingUp(R) certificate, then dropping the multiplicative-monoid package, the multiplication operation, the multiplicative one, the multiplicative monoid stability rows, the distributivity rows, and the zero-multiplication rows leaves a retained carrier, source, additive pattern, classifier, additive stability fields, and additive ledger that form an AbGroupUp(R) certificate over the same carrier and classifier.

Local inputs:
- `papers/bedc/parts/concrete_instances/ring/18_ring_certificate_and_additive_laws.tex`
- `papers/bedc/parts/concrete_instances/ring/18_ring_zero_product_and_signed_square.tex`
- `papers/bedc/parts/concrete_instances/17_abgroup_namecert_construction.tex`

Rationale:
Ring source spec at ring/18_ring_certificate_and_additive_laws.tex:3-6 explicitly says 'additive AbGroupUp + multiplicative MonoidUp on the same carrier'. The multiplicative side has an explicit forgetful proposition `Ring forgets to Monoid certificate` at ring/18_ring_zero_product_and_signed_square.tex:463 (prop:ring-forgets-monoid-certificate), but the dual additive forgetful proposition does not exist. Grep `ring-forgets-abgroup` and `Ring forgets.*AbGroup` across papers/bedc/parts/ returns 0 hits. The proof is structurally analogous to `prop:abgroup-forgets-group-certificate` (17_abgroup:721) and `prop:module-forgets-abgroup-certificate` (21_module:581): drop the multiplicative coordinates, retain the additive ones, and verify obligation-by-obligation against def:abgroup-certificate-obligations. Existing Module->AbGroup proof at 21_module:583-600 supplies the template. The gap is genuine because the chain Ring->AbGroup is currently invoked only implicitly via Module->AbGroup composed with some module instance, which a Ring user does not have.

---

### B-214 - Lattice meet-join distributive duality

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Lattice meet-join distributive duality |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 9/10 |

Problem:
If A carries a LatticeUp(A) certificate with classifier symmetry, transitivity, both meet and join classifier-congruence rows, the inherited POSet antisymmetry field, and the directional meet and join bound-characterization fields, and if the meet-distributes-over-join law a wedge (b vee c) sim_C (a wedge b) vee (a wedge c) holds for all a,b,c in A, then the dual law a vee (b wedge c) sim_C (a vee b) wedge (a vee c) holds for all a,b,c in A.

Local inputs:
- `papers/bedc/parts/concrete_instances/30_lattice_directed_associativity.tex`
- `papers/bedc/parts/concrete_instances/lattice/the_certificate.tex`

Rationale:
30_lattice_directed_associativity.tex:127 has thm:lattice-distributivity-implies-modular-law: assuming meet-distributes-over-join, the modular law follows. But the classical 'distributive duality' (meet-distributive iff join-distributive in any lattice) is genuinely missing. Grep `distributive` across papers/bedc/parts/concrete_instances/lattice/ and 30_lattice*.tex returns only the modular-law theorem (line 127) plus the orienting paragraph in 30_lattice_namecert_construction.tex:4 listing 'idempotence, commutativity, associativity, and absorption' as derived from bound characterizations -- distributivity is not in that list and is treated only as a hypothesis when needed. The proof can be assembled from existing tools in the chapter: thm:lattice-commutativity-from-directional-bounds (lattice/the_certificate.tex:193, B-25, already proven), the absorption laws (lattice/the_certificate.tex:168 and 254, B-07/B-27, already proven), and bound greatestness/leastness, all of which are already lifted to theorems. The gap is genuine and high-value because it converts the existing one-sided distributivity hypothesis into a self-dual property usable in either form.

---

### B-215 - Polynomial multiplication associativity over CommRing scalars

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Polynomial multiplication associativity over CommRing scalars |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
If R carries a CommRingUp(R) certificate, read as a RingUp(R) certificate by prop:commring-forgets-ring-certificate, with classifier sim_R, zero 0_R, addition +, multiplication dot, raw Cauchy product rmul_R from def:polynomial-raw-cauchy-product, normalization trim_R from def:polynomial-stability-certificate, and PolyMul_R from def:polynomial-multiplication-on-coefficient-spines, then for all finite coefficient spines p,q,r:ListCarrier(R), PolySame_R(PolyMul_R(PolyMul_R(p,q),r), PolyMul_R(p,PolyMul_R(q,r))) holds.

Local inputs:
- `papers/bedc/parts/concrete_instances/25_polynomial_literal_addtrim.tex`
- `papers/bedc/parts/concrete_instances/25_polynomial_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/19_commring_namecert_construction.tex`

Rationale:
25_polynomial_literal_addtrim.tex defines PolyMul_R at line 221 (PolyMul_R(x,y) := trim_R(rmul_R(trim_R(x), trim_R(y)))). It also has thm:polynomial-raw-addition-associativity (line 539) for addition and thm:polynomial-raw-multiplication-commutativity-from-commring-scalars (line 565) for raw multiplication commutativity. Multiplication associativity is conspicuously absent. Grep `polynomial.*multiplication.*assoc`, `PolyMul.*assoc`, `thm:polynomial.*assoc`, and `rmul.*rmul` across papers/bedc/parts/ returns only the addition-associativity theorem (line 539) and commutativity occurrence at line 568 -- no associativity over rmul or PolyMul. The proof requires Cauchy convolution associativity sum_{i+j=n} (sum_{a+b=i} p_a q_b) r_j = sum_{a+j+l=n} p_a q_b r_l = sum_{a+k=n} p_a (sum_{b+l=k} q_b r_l), which uses double-finite-fold reindexing similar to the matrix associativity proof at matrix/finite_fold_multiplication_laws.tex:210, plus trim-multiplication compatibility lemmas already in the chapter. The gap is genuine: the polynomial certificate cannot honestly claim ring-of-polynomials structure without it, and the existing zero-tail invariance (B-22) and trim invariance (B-21) lemmas on the board are the natural prerequisites.

---

### B-216 - Analytic continuation predicate is symmetric in its two domains

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Analytic continuation predicate is symmetric in its two domains |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
If \mathsf{AnaCont}(f, D_1, g, D_2, h) holds with \mathsf{DomCompat}(D_1, D_2, U), then \mathsf{AnaCont}(g, D_2, f, D_1, h) holds (under the symmetric \mathsf{DomCompat}(D_2, D_1, U)).

Local inputs:
- `papers/bedc/parts/concrete_instances/50_analytic_continuation_operation.tex`
- `papers/bedc/parts/concrete_instances/43_holomorphic_namecert_construction.tex`

Rationale:
Chapter 50 (concrete_instances/50_analytic_continuation_operation.tex). Review category 4 (Missing companion). Definition def:ana-cont (line ~30) phrases the predicate symmetrically — clauses 1 and 2 swap the roles of (f, D_1) and (g, D_2), and clause 3 is symmetric in U. The chapter proves uniqueness (thm:ana-cont-unique:34) and 2-chain composition (thm:chain-continuation:44) but never names the trivial symmetry. A senior referee would flag that the operation laws section is incomplete without it and that thm:chain-continuation implicitly relies on swap symmetry through DomCompat. Closes in 1 round: definition unfolding plus DomCompat symmetry of overlap region U.

---

### B-217 - Analytic continuation triple-chain associativity

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Analytic continuation triple-chain associativity |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 9/10 |

Problem:
If \mathsf{AnaCont}(f_1, D_1, f_2, D_2, h_{12}), \mathsf{AnaCont}(f_2, D_2, f_3, D_3, h_{23}), and \mathsf{AnaCont}(h_{12}, D_1\cup D_2, f_3, D_3, h_{(12)3}) all hold, then \mathsf{AnaCont}(f_1, D_1, h_{23}, D_2\cup D_3, h_{1(23)}) is witnessed and \hsame(h_{(12)3}, h_{1(23)}) on D_1\cup D_2\cup D_3.

Local inputs:
- `papers/bedc/parts/concrete_instances/50_analytic_continuation_operation.tex`
- `papers/bedc/parts/concrete_instances/43_holomorphic_namecert_construction.tex`

Rationale:
Chapter 50. Review category 7 (Composite consequence). The chapter labels thm:chain-continuation (line 44) for the 2-chain case but the 1→2→3 reassociation identity — a referee's first follow-up question after seeing 2-chain composition — is missing. Local prerequisites are exactly thm:ana-cont-unique:34 and two applications of thm:chain-continuation:44 plus union-set commutativity. Closes in 2 rounds (build the (12)3 witness, build the 1(23) witness, identify by uniqueness). Distinct from B-15: real history-sameness limit transport in core/concrete is about Bishop reals, not holomorphic chain associativity.

---

### B-218 - Contour integral closure under combined affine-concatenation

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Contour integral closure under combined affine-concatenation |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
If \gamma=\gamma_1\ast\gamma_2 (sharing endpoint per lem:pl-contour-concat) and \mathsf{ContInt}(f, \gamma_1, I_1^f), \mathsf{ContInt}(f, \gamma_2, I_2^f), \mathsf{ContInt}(g, \gamma_1, I_1^g), \mathsf{ContInt}(g, \gamma_2, I_2^g) all hold, then for any complex histories a, b, \mathsf{ContInt}(a f + b g, \gamma, a(I_1^f + I_2^f) + b(I_1^g + I_2^g)).

Local inputs:
- `papers/bedc/parts/concrete_instances/49_contour_integral_operation.tex`

Rationale:
Chapter 49 (concrete_instances/49_contour_integral_operation.tex). Review category 7 (Composite consequence). The chapter labels lem:cont-int-linear:93 (linearity in integrand only), lem:cont-int-concat:101 (concat for fixed integrand), lem:cont-int-reversal:109, and lem:cont-int-reparameterization:117 separately, but the combined affine-on-integrand-and-concat-on-contour closure is not stated. This composite is what one wants for the standard partition-and-bound argument inside Cauchy proofs (thm:cauchy-triangle:127, thm:cauchy-integral-formula:143) and is currently re-derived ad hoc. Closes in 1 round by chaining lem:cont-int-linear and lem:cont-int-concat.

---

### B-219 - Centralizer-coset multiplication closure under representative product

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Centralizer-coset multiplication closure under representative product |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 9/10 |

Problem:
If centralizer-coset carrier \mathsf{CentralizerCosetCarrier}(\mathsf{mul}, a, x, h_1) and \mathsf{CentralizerCosetCarrier}(\mathsf{mul}, a, y, h_2) hold (for representatives x, y centralizing a), then \mathsf{CentralizerCosetCarrier}(\mathsf{mul}, a, \mathsf{mul}(x,y), \mathsf{mul}(h_1, h_2)).

Local inputs:
- `papers/bedc/parts/concrete_instances/quotientgroup/concrete_namecert_carrier.tex`
- `papers/bedc/parts/concrete_instances/quotientgroup/concrete_namecert_certificate.tex`
- `papers/bedc/parts/concrete_instances/16_group_namecert_construction.tex`

Rationale:
Chapter 60 (concrete_instances/quotientgroup/). Review category 1 (Closure under composition). The chapter labels many transport theorems — thm:quotientgroup-centralizer-normalizer-empty-representative-transport:96, thm:quotientgroup-centralizer-coset-empty-representative-transport:127, thm:quotientgroup-centralizer-normalizer-orbit-kernel-equivalence:119 — but never states that two coset memberships compose to a coset of the product of representatives. Without this closure, the chapter's quotient is only a set, not a group: a senior referee's first question is 'is the operation well-defined on cosets?'. Closes in 2-3 rounds using mul congruence (group chapter), centralizer-product centralizer (group/16_group_centralizer_normalizer.tex line 59 already has GroupConjugationWord_product_composition leanchecked), and \hsame transport on mul.

---

### B-220 - Double opposite POSet data identity

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (codex) |
| Object | Double opposite POSet data identity |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 7/10 |
| Novelty | 7/10 |

Problem:
Under a POSet name-certificate setup with an opposite-data construction op(.), op(op(D)) equals D componentwise on carrier, classifier, ordering relation, and antisymmetry ledger.

Local inputs:
- `papers/bedc/parts/concrete_instances/28_poset_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/27_preorder_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/30_lattice_namecert_construction.tex`

Rationale:
Concrete single-implication theorem expressible as 'op(op(D)) = D componentwise' on the POSet certificate data tuple. Fits cleanly into the existing concrete_instances/28_poset_namecert_construction.tex surface, which currently has no opposite-construction theorem. Distinct from the lattice-direction entries B-25/B-26/B-27/B-29 (those concern bound-derived laws of meet/join, not order duality). No paper label matches: existing poset coverage is only the singleton-empty and unary-prefix instances. The theorem is small but foundational because it underpins later lattice-duality material (meet/join exchange under op) that B-25–B-29 implicitly assume; making the involution explicit at the POSet layer is the right place to anchor that duality.

---

### B-221 - Double-opposite monoid certificate data identity

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Double-opposite monoid certificate data identity |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 7/10 |

Problem:
If $(\mathcal{C},\sim_C,\cdot_C,e_C)$ satisfies the $\MonoidUp$ certificate obligations, then applying the opposite-monoid construction twice yields a $\MonoidUp$ certificate whose carrier, classifier, multiplication, and identity data are componentwise identical to the original.

Local inputs:
- `papers/bedc/parts/concrete_instances/15_monoid_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/28_poset_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/36_category_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/nattrans/vertical_and_opposite_extras.tex`

Rationale:
Chapter 15 (15_monoid_namecert_construction.tex:549) proves `thm:opposite-monoid-certificate` constructing the opposite monoid, but the chapter does NOT contain the parallel `double-opposite monoid certificate data identity` theorem that is present for poset (28_poset_namecert_construction.tex:435 `thm:double-opposite-poset-certificate-data-identity`), category (36_category_namecert_construction.tex:352, plus involution at :415), functor (functor/certificate_obligations.tex:670), and natural transformation (nattrans/vertical_and_opposite_extras.tex:140). Review category 4 (missing companion result): a coherence statement asserted by parallel pattern in the categorical chapters but never stated for monoid. Closes in 1-2 codex rounds because the proof skeleton is `unfold opposite twice, observe that exchange of inputs composed with itself is identity, copy the field-by-field reduction used in the poset/category proofs`; all required ingredients (opposite-monoid theorem, classifier reflexivity, no kernel rules) are local to chapter 15.

---

### B-222 - Limit respects pointwise difference of complex sequences

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Limit respects pointwise difference of complex sequences |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 7/10 |

Problem:
If $\mathsf{CplxLim}(s, N_s, z_s, M_s)$ and $\mathsf{CplxLim}(t, N_t, z_t, M_t)$, then $\mathsf{CplxLim}(s\ominus t, N', z_s - z_t, M')$ with explicit pasted modulus $M'(k):=\max(M_s(k+1), M_t(k+1))$, where $\ominus$ is componentwise rational-history subtraction continuation.

Local inputs:
- `papers/bedc/parts/concrete_instances/40_complex_limit_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/14_complex_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/13_real_namecert_construction.tex`

Rationale:
Chapter 40 has `thm:cplx-lim-sum` (line 538), `thm:cplx-lim-scalar` (line 546), `thm:cplx-lim-product` (line 554), and `thm:cplx-lim-unique` (line 320), but a grep for `cplx-lim-(neg|sub|diff|conj|abs|modulus)` returns 0 hits, while the chapter's distance definition itself is built from componentwise difference (line 15: `CplxDist(z,w,D) := CplxMod(z-w, D)`). Review category 4 (missing companion result): the difference operation is the most directly derivable companion to the sum and is more primitive than the product or scalar variants already proved. Closes in 1 round: triangle inequality on $\mathsf{CplxDist}((s\ominus t)(n), z_s - z_t, D)$ decomposes the bound into the sum of $s$- and $t$- bounds at level $k+1$, identical proof skeleton to `thm:cplx-lim-sum` with rational-history subtraction continuation in place of addition continuation.

---

### B-223 - Double-opposite lattice certificate data identity

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Double-opposite lattice certificate data identity |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |

Problem:
If $(\mathcal{C},\sim_C,\le_C,\wedge_C,\vee_C)$ satisfies the $\LatticeUp$ certificate obligations, then applying the opposite-lattice construction of `lattice/the_certificate.tex` twice yields a $\LatticeUp$ certificate whose order, meet, and join data are componentwise identical to the original.

Local inputs:
- `papers/bedc/parts/concrete_instances/lattice/the_certificate.tex`
- `papers/bedc/parts/concrete_instances/30_lattice_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/28_poset_namecert_construction.tex`

Rationale:
`lattice/the_certificate.tex:533-597` constructs the opposite-lattice certificate (swapping meet and join, reversing order), but the parallel `double-opposite lattice certificate data identity` theorem present for poset (28_poset_namecert_construction.tex:435) is missing — grep for `double.*opposite|opposite.*opposite` in lattice/ files returns 0 hits beyond the singular opposite construction. Review category 4 (missing companion result), parallel structure to candidate 1. Closes in 1-2 codex rounds: meet/join order exchange is involutive, classifier and order reverse twice to themselves, and the fielded reduction copies the poset double-opposite proof. The lattice certificate inherits POSet stability fields, so the inherited part already follows from the poset double-opposite theorem already in the paper.

---

### B-224 - Lattice meet two-sided monotonicity from directional bounds

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Lattice meet two-sided monotonicity from directional bounds |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 10/10 |
| Novelty | 8/10 |

Problem:
Under a LatticeUp setup with inherited preorder transitivity and antisymmetry plus the directional meet bound-characterization fields, if $a \le_C a'$ and $b \le_C b'$, then $a \wedge b \le_C a' \wedge b'$.

Local inputs:
- `papers/bedc/parts/concrete_instances/30_lattice_directed_associativity.tex`
- `papers/bedc/parts/concrete_instances/lattice/the_certificate.tex`
- `papers/bedc/parts/concrete_instances/28_poset_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/27_preorder_namecert_construction.tex`

Rationale:
Belongs to concrete_instances/lattice. This is the canonical 'lattice operations are monotone' lemma in every lattice-theory text (Davey-Priestley, Introduction to Lattices and Order, §2.8; Birkhoff, Lattice Theory, ch I §6 (P5)). Searched papers/bedc/parts/concrete_instances/lattice/ and 30_lattice_*.tex with grep for 'monoton|isoton|le.*meet|meet.*le' — zero matches. Existing chapter has idempotence, absorption, commutativity, opposite absorption, bound uniqueness, but never two-sided monotonicity. Proof uses only fields already present in def:lattice-stability-certificate: meet lower-left, meet lower-right, preorder transitivity (inherited from 27_preorder), and meet greatestness. Concretely: $a \wedge b \le_C a$ then transitivity to $a'$ gives $a \wedge b \le_C a'$; symmetrically $a \wedge b \le_C b'$; meet greatestness packages these as $a \wedge b \le_C a' \wedge b'$. Closes in 1 round — 10 lines like lem:lattice-meet-absorbs-smaller-ordered-endpoint at 30_lattice_directed_associativity.tex:53.

---

### B-225 - Lattice join two-sided monotonicity from directional bounds

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Lattice join two-sided monotonicity from directional bounds |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 10/10 |
| Novelty | 7/10 |

Problem:
Under a LatticeUp setup with inherited preorder transitivity and antisymmetry plus the directional join bound-characterization fields, if $a \le_C a'$ and $b \le_C b'$, then $a \vee b \le_C a' \vee b'$.

Local inputs:
- `papers/bedc/parts/concrete_instances/30_lattice_directed_associativity.tex`
- `papers/bedc/parts/concrete_instances/lattice/the_certificate.tex`
- `papers/bedc/parts/concrete_instances/28_poset_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/27_preorder_namecert_construction.tex`

Rationale:
Dual of the meet candidate above. Same textbook reference (Davey-Priestley §2.8 P5; Birkhoff ch I §6). Grep across lattice/ and 30_lattice_*.tex for 'join.*monoton|join.*le.*join' returns zero. The proof uses join upper-left, join upper-right, preorder transitivity, and join leastness, all present in def:lattice-stability-certificate. Step-by-step: $a \le_C a'$ composes with join upper-left $a' \le_C a' \vee b'$ to give $a \le_C a' \vee b'$; symmetrically $b \le_C a' \vee b'$; join leastness gives $a \vee b \le_C a' \vee b'$. 1-round closure, isomorphic to the meet companion.

---

### B-226 - Lattice meet monotonicity in the second argument

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Lattice meet monotonicity in the second argument |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 7/10 |

Problem:
Under a LatticeUp setup with inherited preorder reflexivity and transitivity plus the directional meet bound-characterization fields, for every $c$, if $b \le_C b'$, then $c \wedge b \le_C c \wedge b'$.

Local inputs:
- `papers/bedc/parts/concrete_instances/30_lattice_directed_associativity.tex`
- `papers/bedc/parts/concrete_instances/lattice/the_certificate.tex`
- `papers/bedc/parts/concrete_instances/27_preorder_namecert_construction.tex`

Rationale:
Single-argument refinement of the two-sided monotonicity: a separate stepping stone because Davey-Priestley and Roman, Lattices and Ordered Sets ch 2 both prove it as the building block (one-sided $\Rightarrow$ two-sided by composition). It is also the form most often cited downstream by chain arguments. Grep on 'meet.*monoton|monoton.*meet' across the chapter returns zero. Proof is 4 lines: $c \wedge b \le_C c$ (lower-left), $c \wedge b \le_C b \le_C b'$ (lower-right + transitivity), then meet greatestness with witness $c \wedge b$ and operands $c, b'$ gives $c \wedge b \le_C c \wedge b'$. Closes in 1 round; serves as the canonical lemma later for spectrum/Galois constructions.

---

### B-227 - NatTrans whiskering by a functor yields a natural transformation

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | NatTrans whiskering by a functor yields a natural transformation |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 10/10 |
| Novelty | 10/10 |

Problem:
If \alpha : F \Rightarrow G is a natural transformation between functors C \to D under \NameCert_{\NatTransUp} and H : D \to E is a functor under \NameCert_{\FunctorUp}, then the component family (H_1 \circ \alpha)_X := H_1(\alpha_X) is a natural transformation H \circ F \Rightarrow H \circ G satisfying the \NameCert_{\NatTransUp} carrier and naturality-square fields under the morphism classifier of E.

Local inputs:
- `papers/bedc/parts/concrete_instances/38_nattrans_namecert_carrier.tex`
- `papers/bedc/parts/concrete_instances/38_nattrans_namecert_certificate.tex`
- `papers/bedc/parts/concrete_instances/nattrans/vertical_and_opposite_extras.tex`
- `papers/bedc/parts/concrete_instances/functor/certificate_obligations.tex`
- `papers/bedc/parts/concrete_instances/functor/pipeline_composite_extras.tex`

Rationale:
Whiskering (post-composition of a natural transformation by a functor, often called horizontal composition's left or right unit) is a foundational categorical operation distinct from vertical composition (already covered in nattrans/vertical_and_opposite_extras.tex:59 thm:nattrans-vertical-composition-naturality, board entry B-14). Grep "horizontal\|whisker" across papers/bedc/parts/ AND lean4/BEDC/ returned 0 hits. Grep "thm:.*nattrans.*horizontal" returned 0 hits. The chapter has thm:identity-nattrans-certificate (vertical_and_opposite_extras.tex:212), thm:nattrans-vertical-composition-naturality (line 60), and thm:double-opposite-nattrans-certificate-data-identity (line 141), but no theorem proves that pre/post-composing with a functor preserves the natural-transformation structure. Builds directly on functor-classifier-replacement-stability (functor/certificate_obligations.tex) and existing nattrans naturality-square machinery.

---

### B-228 - Composition of adjunctions

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Composition of adjunctions |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 10/10 |
| Novelty | 10/10 |

Problem:
If \NameCert_{\AdjunctionUp} carriers F_1 \dashv G_1 between categories C and D and F_2 \dashv G_2 between D and E are given, with both unit-counit data satisfying \autoref{def:adjunction-unit-counit-carrier}, then the composite functors F_2 \circ F_1 and G_1 \circ G_2 form an adjunction F_2 \circ F_1 \dashv G_1 \circ G_2 between C and E whose unit and counit are obtained by whiskering and vertical composition of the input units and counits.

Local inputs:
- `papers/bedc/parts/concrete_instances/85_adjunction_namecert_carrier_and_alternating.tex`
- `papers/bedc/parts/concrete_instances/85_adjunction_namecert_certificate.tex`
- `papers/bedc/parts/concrete_instances/adjunction/carrier_swap_involutions.tex`
- `papers/bedc/parts/concrete_instances/functor/pipeline_composite_extras.tex`

Rationale:
Composition of adjunctions is a core fact of category theory and is expected at the same level of derivedness as functor composition (B-11 on the board). Grep "adjunction.*compos\|compos.*adjunction" finds only thm:adjunction-prefix-unit-counit-composite-empty (85_adjunction_namecert_certificate.tex:5) and thm:monad-adjunction-endomorphism-triangle-composite-empty (86_monad...:175); both concern empty triangle composites WITHIN a single adjunction, not the composition of two distinct adjunctions. Grep "adjunction.*natural.*isomorph\|adjunction.*uniqu" returned 0 hits. Existing infrastructure includes thm:adjunction-unit-counit-carrier-swap-involution and full triangle-result determinism (85_...carrier_and_alternating.tex:160 thm:adjunction-unit-counit-triangle-results-deterministic), which give the classifier transport this composition theorem needs.

---

### B-229 - Composite pullback gap-policy preserves coverage and separation

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Composite pullback gap-policy preserves coverage and separation |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 9/10 |

Problem:
Assume \GapPol(\Pi,D). If \tau_1 : D' \to D and \tau_2 : D'' \to D' each carry a classifier-preserving pullback ledger over \Pi in the sense of \autoref{def:classifier-preserving-pullback-ledger}, then the composite history operation \tau_1 \circ \tau_2 : D'' \to D carries a classifier-preserving pullback ledger whose pulled-back membership predicate satisfies the coverage and separation obligations on D''.

Local inputs:
- `papers/bedc/parts/proof_obligations/gap_policy.tex`
- `papers/bedc/parts/core/07_gap_policies_coverage_separation_and_composition.tex`
- `papers/bedc/parts/proof_standing/04_package_gap_proof_spine.tex`

Rationale:
gap_policy.tex proves single-pullback theorems thm:package-token-pullback-separation (line 127) and thm:pulled-back-gap-policy-preserves-coverage-and-separation (line 151), but the composition of two pullback ledgers is not lifted to a theorem. Grep "pullback.*compos\|compos.*pullback" across papers/bedc/parts/ returned only one hit, in core/07_gap_policies...:182, which discusses composite COMPRESSION ledgers (compositional gap-ledger structure inside a SINGLE \GapPol), not the iteration of \tau-pullbacks across nested domains. The composition of two classifier-preserving pullback ledgers is implicitly required for nested cross-observation chains but never formalized. Standing as a corollary of the existing single-pullback theorem composed with itself, but the explicit statement and dependency wiring (token-policy preservation across two stages) is missing.

---

### B-230 - FPS Cauchy product associativity over a commutative ring

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | FPS Cauchy product associativity over a commutative ring |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 9/10 |

Problem:
Let R be a \CommRingUp certificate read through \autoref{prop:commring-forgets-ring-certificate} as a \RingUp certificate. For coefficient sequences F, G, H : \NatUp \to R as in \autoref{def:fps-carrier} with the Cauchy product \odot_{\mathrm{fps}} of \autoref{def:fps-cauchy-coefficient-spine}, the FPS classifier identifies (F \odot_{\mathrm{fps}} G) \odot_{\mathrm{fps}} H with F \odot_{\mathrm{fps}} (G \odot_{\mathrm{fps}} H).

Local inputs:
- `papers/bedc/parts/concrete_instances/26_fps_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/19_commring_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/18_ring_namecert_construction.tex`

Rationale:
Chapter 26 (FPS) has labeled theorems for singleton instance laws (thm:singleton-zero-fps-laws line 45), Cauchy product congruence (thm:fps-cauchy-product-classifier-congruence line 339), addition commutativity (thm:fps-addition-commutativity-from-scalar-additive-commutativity line 393), and Cauchy product commutativity from commring scalars (thm:fps-cauchy-product-commutativity-from-commring-scalars line 490). It does NOT have a Cauchy product associativity theorem: grep "fps.*associat\|cauchy.*associat" across papers/bedc/parts/ returned 0 hits. Distinct from board entry B-09 (polynomial chapter 25), since FPS over \NatUp \to R has different normalization semantics than coefficient-list polynomials. The required two-index finite fold swap (cf. matrix/finite_fold_multiplication_laws.tex thm:matrix-multiplication-associativity-finite-folds line 211) is already in the toolkit, so the proof is constructible from existing infrastructure but the theorem is currently absent.

---

### B-231 - FPS Cauchy product distributes over FPS addition

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | FPS Cauchy product distributes over FPS addition |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
Let R be a \RingUp certificate. For coefficient sequences F, G, H : \NatUp \to R as in \autoref{def:fps-carrier} with addition \oplus_{\mathrm{fps}} and Cauchy product \odot_{\mathrm{fps}} from \autoref{def:fps-cauchy-coefficient-spine}, the FPS classifier identifies F \odot_{\mathrm{fps}} (G \oplus_{\mathrm{fps}} H) with (F \odot_{\mathrm{fps}} G) \oplus_{\mathrm{fps}} (F \odot_{\mathrm{fps}} H), and similarly for the right side.

Local inputs:
- `papers/bedc/parts/concrete_instances/26_fps_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/18_ring_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/matrix/finite_fold_multiplication_laws.tex`

Rationale:
Companion to candidate #4. Chapter 26 has labeled theorems through line 522 (last labeled thm:fps-cauchy-product-commutativity-from-commring-scalars at line 490), but grep "fps.*distrib\|distrib.*fps" across papers/bedc/parts/ returned 0 hits and grep "fps.*right.*unit\|fps.*left.*unit\|fps.*one.*unit" returned 0 hits. The singleton instance handles the trivial case (thm:singleton-zero-fps-laws collapses all operations to \emp), but no theorem distributes generic-ring Cauchy product over generic-ring addition pointwise on coefficients. The required machinery (finite additive fold splits pointwise sums, lem:finite-additive-fold-splits-pointwise-sums in matrix/finite_fold_multiplication_laws.tex line 563) already exists. Distinct from the polynomial chapter 25 board entries (B-09, B-22, B-30, B-31) because FPS has no normalization step.

---

### B-232 - Right adjoint uniqueness up to natural isomorphism

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Right adjoint uniqueness up to natural isomorphism |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 9/10 |

Problem:
Suppose \NameCert_{\AdjunctionUp} carriers F \dashv G_1 and F \dashv G_2 are both displayed between the same categories C and D in the sense of \autoref{def:adjunction-unit-counit-carrier}. Then there is a natural-transformation pair \eta : G_1 \Rightarrow G_2 and \eta' : G_2 \Rightarrow G_1 whose vertical composites are the identity natural transformations on G_1 and G_2 under \NameCert_{\NatTransUp}.

Local inputs:
- `papers/bedc/parts/concrete_instances/85_adjunction_namecert_carrier_and_alternating.tex`
- `papers/bedc/parts/concrete_instances/85_adjunction_namecert_certificate.tex`
- `papers/bedc/parts/concrete_instances/adjunction/carrier_swap_involutions.tex`
- `papers/bedc/parts/concrete_instances/nattrans/vertical_and_opposite_extras.tex`

Rationale:
Right (and left) adjoint uniqueness up to natural iso is a standard categorical result that BEDC's existing adjunction infrastructure should support but currently does not state. Grep "adjunction.*uniqu\|adjunction.*natural.*isomorph\|adjunction.*equival" across papers/bedc/parts/ returned 0 results except a description-level remark in 85_adjunction_namecert_carrier_and_alternating.tex:4 about 'natural-isomorphism witness on hom-sets', which is the input data, not the uniqueness theorem. The adjunction chapter has thm:adjunction-unit-counit-triangle-results-deterministic (carrier_and_alternating.tex:160), thm:adjunction-unit-counit-carrier-swap-involution, and full triangle-result symmetry, all of which feed this uniqueness derivation. Genuinely distinct from candidate #2 (composition of adjunctions): uniqueness compares two adjunctions sharing F, while composition combines two adjunctions over different category pairs.

---

### B-233 - Complex limit respects pointwise negation

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (codex) |
| Object | Complex limit respects pointwise negation |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |

Problem:
If CplxLim(s, N, z, M) holds, then the pointwise additive-inverse sequence -s satisfies CplxLim(-s, N, -z, M) with the same limit modulus.

Local inputs:
- `papers/bedc/parts/concrete_instances/40_complex_limit_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/12_complex_namecert_construction.tex`

Rationale:
The complex-limit chapter (definitions def:cplx-lim, def:cplx-pointwise-difference, def:cplx-pointwise-sum) already records pointwise negation/sum/difference as carrier operations, but the paper coverage shows no theorem stating that CplxLim transports across pointwise negation. This is a clean unary classifier-transport theorem — a single implication using only the additive-inverse field of the complex carrier and the unchanged modulus N. It is the simplest closure-under-arithmetic property of complex limits and forms a natural prerequisite/lemma for stronger results (sum, affine combinations). It does not duplicate any existing B-target — none of B-06..B-31 is about complex limits or arithmetic transport — and it lives squarely in concrete_instances chapter 40 (complex limit namecert).

---

### B-234 - Complex limit respects binary affine combinations

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (codex) |
| Object | Complex limit respects binary affine combinations |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
If CplxLim(s, N_s, z_s, M_s) and CplxLim(t, N_t, z_t, M_t) hold, then a·s + b·t satisfies CplxLim(a·s+b·t, N_{ab}, a·z_s + b·z_t, M_{ab}) under the pasted scalar-shift modulus.

Local inputs:
- `papers/bedc/parts/concrete_instances/40_complex_limit_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/12_complex_namecert_construction.tex`

Rationale:
The complex-limit certificate has pointwise sum and scalar-multiplication carrier operations defined (def:cplx-pointwise-sum, def:cplx-power), but paper coverage exhibits no theorem expressing the linearity of complex limits as a single classifier-transport statement. An affine-combination theorem captures linearity in one strike (sum + scalar shift, with pasted modulus N_{ab} = max(N_s, N_t) shifted by |a|+|b|). It is a foundational closure property of CplxLim that downstream targets (Cauchy product convergence, conv-rad, holomorphic stability) rely on implicitly. It is genuinely distinct from the negation target above because it requires both pointwise sum and scalar-multiplication classifier fields, plus modulus pasting — a fundamentally different proof obligation. No overlap with B-06..B-31 or with any existing thm/lem/cor label in the coverage list.

---

### B-235 - Lattice operation monotonicity from directional bounds

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (codex) |
| Object | Lattice operation monotonicity from directional bounds |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
Under the LatticeUp directional bound setup, if $a\le_C a'$ then $a\wedge c\le_C a'\wedge c$ and $c\wedge a\le_C c\wedge a'$, and if $b\le_C b'$ then $b\vee c\le_C b'\vee c$ and $c\vee b\le_C c\vee b'$.

Local inputs:
- `papers/bedc/parts/concrete_instances/30_lattice_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/28_poset_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/27_preorder_namecert_construction.tex`

Rationale:
Monotonicity is the missing structural law in the lattice directional-bound family on BOARD. Existing entries cover idempotence/absorption (B-07), commutativity (B-25), associativity (B-26), opposite absorption (B-27), and bound uniqueness (B-29), but none state that meet and join are order-preserving in their arguments. Following the BOARD precedent set by B-25/B-26/B-27 (one entry per law family, covering both meet and join), the two codex sub-claims are consolidated into a single monotonicity entry covering all four argument slots. The proof reuses the same directional GLB/LUB and inherited preorder transitivity ingredients already invoked by B-26, so it lands cleanly in chapter 30.

---

### B-236 - NatTrans prewhiskering by a functor yields a natural transformation

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (codex) |
| Object | NatTrans prewhiskering by a functor yields a natural transformation |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
If $\alpha:F\Rightarrow G$ is a $\NatTransUp$ certificate over $\mathcal C\to\mathcal D$ and $K:\mathcal B\to\mathcal C$ is a $\FunctorUp$ certificate, then $\alpha\ast K:F\circ K\Rightarrow G\circ K$ is a $\NatTransUp$ carrier.

Local inputs:
- `papers/bedc/parts/concrete_instances/38_nattrans_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/37_functor_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/36_category_namecert_construction.tex`

Rationale:
Chapter 38 (nattrans) is currently 100% definitions / 0 theorems, exactly the structural gap B-14 already identified. The paper carries `def:functor-whiskered-nattrans-certificate-data` as a definition site, but no theorem upgrades the whiskered data to a NatTransUp carrier. Prewhiskering is the most elementary categorical operation on natural transformations beyond plain vertical composition — it is strictly weaker than horizontal composition (the other accepted candidate) and uses only the source FunctorUp certificate's morphism action. Distinct from B-14 (vertical β∘α along a shared middle functor) and from B-11 (functor composition's hom-carrier classifier), so no BOARD overlap. A natural standalone target for the loop because the proof obligation reduces to chasing the naturality square along $K(f)$ for $f$ in $\mathcal B$, exposing exactly which FunctorUp fields the NatTransUp certificate transports through.

---

### B-237 - Horizontal composition of natural transformations

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (codex) |
| Object | Horizontal composition of natural transformations |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 9/10 |

Problem:
If $\alpha:F\Rightarrow G$ between $\mathcal C\to\mathcal D$ and $\beta:H\Rightarrow K$ between $\mathcal D\to\mathcal E$ are composable $\NatTransUp$ certificates, then the component family $\beta_{G(X)}\circ H_1(\alpha_X)$ forms a $\NatTransUp$ carrier $H\circ F\Rightarrow K\circ G$.

Local inputs:
- `papers/bedc/parts/concrete_instances/38_nattrans_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/37_functor_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/36_category_namecert_construction.tex`

Rationale:
B-14 covers the vertical composite $\beta\circ\alpha$ along a shared middle functor $G$; horizontal composition has different source/target functors and a fundamentally different naturality square (it depends on both functor's morphism actions, plus the interchange equality $\beta_{G(X)}\circ H_1(\alpha_X) = K_1(\alpha_X)\circ\beta_{F(X)}$). Independent of the accepted prewhiskering target: horizontal composition is the symmetric general case, prewhiskering is the special case where $\beta$ is the identity on a functor. Sits in the same 0-theorem chapter as B-14, addressing a different proof obligation. The claim is stated as a single implication on certificate data and is squarely in concrete_instances scope; not present in paper_coverage (no `\label{thm:nattrans-horizontal-...}` or similar exists).

---

### B-238 - FPS Cauchy product associativity over RingUp scalars

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (codex) |
| Object | FPS Cauchy product associativity over RingUp scalars |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
Under a RingUp scalar package with scalar associativity, left/right distributivity, finite additive folds, and the threefold split-spine fold swap, the FPS Cauchy product on coefficient lists is associative up to the FPS classifier.

Local inputs:
- `papers/bedc/parts/concrete_instances/fps_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/18_ring_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/19_commring_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/25_polynomial_namecert_construction.tex`

Rationale:
FPS chapter currently exposes only definitions (def:fps-carrier, def:fps-cauchy-coefficient-spine, def:fps-threefold-cauchy-split-spines, def:fps-pointwise-addition-coefficient, def:fps-stability-certificate, etc.) with no labeled theorems on Cauchy product algebraic laws. Associativity of the Cauchy product is the canonical multiplicative law for FPS and exactly what the threefold split-spine fold-swap definition was prepared to support, so a dedicated target consumes existing scaffolding rather than introducing new primitives. It is distinct from polynomial-side targets B-09 (normalize commutes with add/multiply), B-22 (poly multiplication zero-tail invariance), B-30/B-31 (poly addition trim/zero-tail), which all live under the polynomial chapter with normalization/trimming, whereas FPS works on full coefficient streams without trimming. It is also distinct from B-21 (trim invariance) which is normalization-shape, not bilinear associativity. The hypotheses are stated as classifier obligations on the scalar RingUp, matching how other concrete-instance theorems on this BOARD are framed.

---

### B-239 - Left adjoint uniqueness up to natural isomorphism

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (codex) |
| Object | Left adjoint uniqueness up to natural isomorphism |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
If two adjunction unit-counit displays share the same right-adjoint prefix, their left-adjoint prefixes are connected by mutually inverse NatTransUp comparison components, giving uniqueness of left adjoints up to natural isomorphism in the BEDC adjunction certificate.

Local inputs:
- `papers/bedc/parts/concrete_instances/adjunction/carrier_swap_involutions.tex`
- `papers/bedc/parts/concrete_instances/38_nattrans_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/37_functor_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/36_category_namecert_construction.tex`

Rationale:
Adjunction is an established BEDC topic with multiple definitions in the paper (def:adjunction-triangle-carrier, def:adjunction-unit-counit-carrier, def:adjunction-unit-counit-carrier-swap-classifier) and active work in papers/bedc/parts/concrete_instances/adjunction/, but no theorem currently captures the structural uniqueness of left adjoints relative to a fixed right adjoint. Existing BOARD entries on functors (B-11) and natural transformations (B-14) cover composition and naturality, not adjoint uniqueness, so this is a clean adjacent gap. The claim is a single implication in BEDC certificate form (NatTransUp inverse-pair witnessing) rather than a generic categorical platitude, and it requires combining the unit-counit triangle laws with NatTransUp composition naturality, which makes it a meaningful proof target rather than a paraphrase of existing entries.

---

### B-240 - Homology cycle carrier respects history-sameness via $\hsame$-stable differential

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Homology cycle carrier respects history-sameness via $\hsame$-stable differential |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
If the chain differential $d$ satisfies $\hsame(h,k)\Rightarrow\hsame(d(h),d(k))$ for all histories, and $Z_d(h)$ and $\hsame(h,k)$, then $Z_d(k)$.

Local inputs:
- `papers/bedc/parts/concrete_instances/76_homology_namecert_construction.tex`

Rationale:
`76_homology_namecert_construction.tex` has 34 theorems but no bedc-deep additions; only `B-135 cohomology-cocycle-predicate-semantic-namecert` (which is a separate chapter, 77_cohomology) appears on BOARD. Existing homology theorems include `cycle-carrier-append-hsame-transport` (line 376 area) for the append case and `boundary-cycle-append-hsame-transport`, `cycle-boundary-append-hsame-transport`, `cycle-boundary-append-cycle-hsame-transport` — all `append`-flavored transports. The plain non-append cycle-carrier hsame transport — `Z_d(h)\land\hsame(h,k)\Rightarrow Z_d(k)` under a stated `d`-stability hypothesis — is missing despite being the most basic transport claim, and is not on BOARD. It is exactly the kind of single-implication seed the loop is meant to add.

---

### B-241 - Continuation Ezero right-unit probe forces source emptiness

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Continuation Ezero right-unit probe forces source emptiness |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 10/10 |
| Novelty | 7/10 |

Problem:
For every generated history u, if for all r:BHist, ContR(Ezero(emp), u, r) implies hsame(r, Ezero(emp)), then hsame(u, emp).

Local inputs:
- `papers/bedc/parts/proof_standing/02_ext_cont_proof_spine.tex`
- `lean4/BEDC/FKernel/Cont.lean`

Rationale:
papers/bedc/parts/proof_standing/02_ext_cont_proof_spine.tex:197-212 proves thm:cont-e1-right-unit-probe-forces-empty for the Eone(emp) probe. There is no companion theorem for the symmetric Ezero(emp) probe, even though the kernel logic is symmetric in e0/e1. Grep for cont_e0_right_unit|e0_right_unit_probe|Ezero.*right.*unit returns zero matches across papers/bedc/parts and lean4/BEDC. Review category 4 (missing companion result; sibling of an existing checked theorem). Closeable in 1-3 rounds: the proof is a verbatim mirror of the Eone case at line 207-211 - apply the probe law to canonical continuation ContR(Ezero(emp), u, append(Ezero(emp), u)); continuation result transport gives ContR(Ezero(emp), u, Ezero(emp)); right-unit uniqueness then forces u hsame emp. All cited ingredients (canonical continuation, cont right-unit uniqueness, append lemmas) are already checked at lean4/BEDC/FKernel/Cont.

---

### B-242 - Tensor product singleton factor associator

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Tensor product singleton factor associator |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 9/10 |

Problem:
If TensorProductSingletonFactor(l,r,t) and TensorProductSingletonFactor(t,s,u) hold, then there exists m with TensorProductSingletonFactor(r,s,m) and TensorProductSingletonFactor(l,m,u), making the singleton tensor pairing associative up to the factor predicate.

Local inputs:
- `papers/bedc/parts/concrete_instances/65_tensorproduct_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/module/21_module_namecert_construction_core.tex`

Rationale:
Chapter 65 defines TensorProductSingletonFactor at line 110-121 (a ternary continuation-ledger factor predicate) and proves swap symmetry at line 201-227 (factor (l,r,t) implies factor (r,l,t)). The chapter intro (line 4) explicitly motivates 'multilinear data on which higher tensor algebras and exterior powers are built' yet provides no associator law for the four-place factor structure. Grep for 'tensor.*associ|associat.*tensor|TensorProduct.*Assoc' across papers/bedc/parts/ returns 0 matches. The proof would use the same singleton-collapse + continuation-respect technique as the existing swap-symmetry theorem, applied to the rebracketing of two ContR ledgers. Distinct from board entries B-06..B-31 (no tensor product appears on the board).

---

### B-243 - NatTrans Godement interchange of vertical and horizontal composition

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | NatTrans Godement interchange of vertical and horizontal composition |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 10/10 |
| Novelty | 10/10 |

Problem:
For natural transformations alpha:F=>G, beta:G=>H between functors C->D and alpha':F'=>G', beta':G'=>H' between functors D->E, the horizontal composite (beta'*beta) o (alpha'*alpha) of the vertical composites is identical (componentwise) to the vertical composite (beta'*beta) o (alpha'*alpha) of the horizontal composites.

Local inputs:
- `papers/bedc/parts/concrete_instances/nattrans/vertical_and_opposite_extras.tex`
- `papers/bedc/parts/concrete_instances/functor/pipeline_composite_extras.tex`

Rationale:
nattrans/vertical_and_opposite_extras.tex proves vertical composition naturality (line 59), functor whiskering (line 249), prewhiskering by a functor (line 345), and horizontal composition (line 422) as separate theorems, but never relates the two compositions through the Godement interchange law. Grep across papers/bedc/parts/ for 'whisker.*associ|associ.*whisker|whiskering.*associat' returns 0 matches; 'interchange|godement' (case-insensitive) returns only AbGroup middle-four interchange (algebraic, not categorical). Functor composition associativity is proven at functor/pipeline_composite_extras.tex:348 but the natural-transformation interchange that would justify combining horizontal/vertical composites is missing. This is the central 2-categorical coherence law making bicategory structure visible. Not on board.

---

### B-244 - Functor whiskering preserves vertical composition

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Functor whiskering preserves vertical composition |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
For functors F,G,H:C->D, K:D->E, and natural transformations alpha:F=>G, beta:G=>H, the K-whiskered vertical composite K_*(beta o alpha) is identical componentwise to the vertical composite (K_*beta) o (K_*alpha).

Local inputs:
- `papers/bedc/parts/concrete_instances/nattrans/vertical_and_opposite_extras.tex`
- `papers/bedc/parts/concrete_instances/nattrans/tail_comm_closed.tex`

Rationale:
vertical_and_opposite_extras.tex proves Functor whiskering of a single natural transformation (line 249, thm:functor-whiskering-nattrans-certificate) and Vertical composition naturality (line 59), and prewhiskering by a functor (line 345), but never proves that whiskering distributes over vertical composition. Grep across papers/bedc/parts/ for 'whisker.*compos|compos.*whisker' returns 0 hits for the distributivity statement. This is a strictly weaker theorem than the full Godement interchange but is independently meaningful as the 2-categorical-functoriality of whiskering. Not on board.

---

### B-245 - NatPrime predicate respects history-sameness

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | NatPrime predicate respects history-sameness |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 10/10 |
| Novelty | 9/10 |

Problem:
If NatPrime(p) and hsame(p, p'), then NatPrime(p').

Local inputs:
- `papers/bedc/parts/concrete_instances/prime/the_prime_predicate.tex`
- `papers/bedc/parts/concrete_instances/prime/the_certificate.tex`
- `papers/bedc/parts/concrete_instances/04_nat_namecert_construction.tex`

Rationale:
Belongs to concrete_instances chapter 39 (prime). Textbook-classical (Hungerford Algebra ch.II §1; the prime predicate is stable under equality of representatives — every introductory number theory text states this implicitly when defining primes on equivalence classes). Negative evidence: grep 'NatPrime.*hsame' returns no labeled theorem; grep 'primality.*respects' returns no matches; def:prime-stability-certificate item 1 lists the property as a stability obligation but no \begin{theorem} proves it. Closes in 1-3 rounds because the proof is a three-way conjunction transport: (i) Unary transports along hsame via lem:unary-transport (already proven); (ii) NatGT(p, Eone(emp)) transports via NatUnaryStrictPrefix endpoint transport (already in chapter 04); (iii) the universal-divisor clause transports through cor:nat-divides-endpoint-hsame-transport (already proven, B-77/B-79 family). All three sub-transports exist; just compose.

---

### B-246 - Trivial subgroup carries SubgroupUp(G)

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Trivial subgroup carries SubgroupUp(G) |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 10/10 |
| Novelty | 9/10 |

Problem:
For any GroupUp(G) certificate, the singleton predicate P(x) := x ~_G e packaged with the inherited classifier carries a SubgroupUp(G) certificate, with closure-under-identity, closure-under-multiplication via e·e ~ e, and closure-under-inverse via inv(e) ~ e.

Local inputs:
- `papers/bedc/parts/concrete_instances/58_subgroup_namecert_construction_core.tex`
- `papers/bedc/parts/concrete_instances/16_group_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/15_monoid_namecert_construction.tex`

Rationale:
Belongs to concrete_instances chapter 58 (subgroup), which currently has only Centralizer SubgroupUp instance. Textbook-classical (Dummit-Foote Abstract Algebra §2.1, example 1 — the trivial subgroup {e}). Negative evidence: grep 'trivial.*subgroup', 'subgroup-singleton', 'subgroup-identity-only' all 0 matches; no BOARD entry between B-127 (subgroup intersection) and any singleton-subgroup case. Closes in 1-3 rounds: closure-under-identity is reflexivity of ~_G; closure-under-multiplication uses monoid left/right unit applied at e (monoid stability rows already lean-checked); closure-under-inverse follows from group left-inverse + right-identity at inv(e) by symmetry+transitivity of hsame (one-line). All three obligations discharge from already-proven group/monoid stability rows.

---

### B-247 - Polynomial multiplication absorbs the zero polynomial on the left

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Polynomial multiplication absorbs the zero polynomial on the left |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 9/10 |

Problem:
For a CommRing R and any normalized polynomial q, PolyMul_R(nil, q) ~ nil under PolySame_R.

Local inputs:
- `papers/bedc/parts/concrete_instances/25_polynomial_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/25_polynomial_literal_addtrim.tex`

Rationale:
Belongs to concrete_instances chapter 25 (polynomial). Textbook-classical (Hungerford Algebra ch.III §6 — zero element of a polynomial ring absorbs multiplication). Negative evidence: grep 'PolyMul.{0,5}nil' / 'polynomial.*zero.*absorption' / 'polynomial.*zero.*mul' returns 0 matches; the only zero-absorption hits are ring-level (thm:ring-mul-zero-absorption) not polynomial-level. BOARD has B-22 (polynomial mul zero-tail invariance), B-30 (two-sided trim compatibility for radd), B-194 (polynomial mul commutativity) — none covers nil-as-PolyMul-left-absorber. Closes in 1-3 rounds: rmul_R has a defining nil clause `rmul_R(nil, y) := nil` (def:polynomial-raw-cauchy-product); trim_R(nil) = nil by trim's nil clause; PolyMul_R(nil, q) = trim_R(rmul_R(trim_R(nil), trim_R(q))) reduces to nil; PolySame_R(nil, nil) is the nil-nil clause of ListClassifierSpec. Three-line proof using existing definitions only.

---

### B-248 - FPS Cauchy product constant term is product of constant terms

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | FPS Cauchy product constant term is product of constant terms |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 9/10 |

Problem:
For carried coefficient sequences F, G : NatUp → R over a Ring R, (F ⊙_fps G)_0 ~_R F_0 ·_R G_0.

Local inputs:
- `papers/bedc/parts/concrete_instances/26_fps_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/18_ring_namecert_construction.tex`

Rationale:
Belongs to concrete_instances chapter 26 (FormalPowerSeries). Textbook-classical (Stanley EC1 §1.1 — constant term is multiplicative on FPS products). Negative evidence: grep 'fps.{0,5}coeff.{0,5}zero' / 'constant.{0,5}term.{0,5}fps' returns 0 hits; only one F_0·G_0 occurrence inside lem:fps-cauchy-coefficient-spine-swapped-reverse for commutativity, not standalone for index 0. BOARD has B-85 (FPS Cauchy classifier congruence), B-211/212 (FPS commutativities), B-231 (Cauchy distributivity) — none addresses the boundary index n=0 directly. Closes in 1-3 rounds: def:fps-cauchy-coefficient-spine gives `(F⊙G)_n := fold_+(CauchySp_n(F,G))`; at n=0, Split(0) has unique decomposition (0,0) so CauchySp_0(F,G) = [F_0 ·_R G_0]; fold_+([x]) = x +_R 0_R; thm:ring-add-right-zero (already checked) collapses to F_0 ·_R G_0. Three-line proof using existing fold and split definitions.

---

### B-249 - Continuation fixed right-unit probe forces source emptiness

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (codex) |
| Object | Continuation fixed right-unit probe forces source emptiness |
| Layer | proof_standing |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |

Problem:
For all histories p and u, (forall r:BHist, ContR(p,u,r) -> HSame(r,p)) implies HSame(u,emp).

Local inputs:
- `papers/bedc/parts/core/03_relational_extension_and_continuation.tex`
- `papers/bedc/parts/proof_obligations/unary_shift_and_commutativity.tex`
- `lean4/BEDC/FKernel/Continuation.lean`

Rationale:
Clean inversion/forcing theorem on the core continuation relation: it characterizes the empty history as the unique right-unit witness of ContR by probing across all result histories. The existing paper has def:continuation-relation, def:continuation-step-rules, and def:continuation-morphism-comp-closed but no labeled theorem reading off emptiness from the universal right-fixedpoint condition. None of the existing BOARD entries (B-06 through B-31) target continuation right-unit inversion; they cluster around concrete-instance stability fields (lattice, module, polynomial, functor, nattrans) and naming-license boundaries, not the abstract continuation relation itself. The implication form is concrete (single P implies Q under the BHist/ContR setup), at the right level for proof_standing or the relational-extension core chapter, and would give a reusable lemma for arguing about identity-style continuation interfaces without committing to a specific concrete instance.

---

### B-250 - Prewhiskering preserves vertical composition

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (codex) |
| Object | Prewhiskering preserves vertical composition |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
Under FunctorUp and NatTransUp setups, for L : B -> C and vertically composable alpha : F => G, beta : G => H, the prewhiskered transformation (beta o_v alpha) * L has the same component family as (beta * L) o_v (alpha * L) up to the nattrans component classifier.

Local inputs:
- `papers/bedc/parts/concrete_instances/37_functor_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/38_nattrans_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/36_category_namecert_construction.tex`

Rationale:
Chapters 37 and 38 are 100% definition-only, and `def:functor-whiskered-nattrans-certificate-data` already supplies the prewhiskering carrier on the paper side, but no theorem states an interchange law between whiskering and vertical composition. This is distinct from B-11 (functor composition closes the hom-carrier classifier) and B-14 (vertical composition preserves the naturality square): it pins down how prewhiskering distributes over vertical composition, which is a third independent categorical interchange law and a natural next theorem site once B-11 and B-14 land. The proof is a direct component-wise calculation under the existing certificate fields, making it a clean medium-risk slot.

---

### B-251 - Continuation fixed left-unit probe forces empty source

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (codex) |
| Object | Continuation fixed left-unit probe forces empty source |
| Layer | core |
| Route | proof |
| Risk | unknown |
| Fit | 7/10 |
| Novelty | 7/10 |

Problem:
If for all r, ContR(u, p, r) implies HSame(r, p), then HSame(u, emp).

Local inputs:
- `papers/bedc/parts/core/continuation_relation.tex`
- `papers/bedc/parts/core/continuation_step_rules.tex`
- `papers/bedc/parts/proof_obligations/unary_shift_and_commutativity.tex`
- `lean4/BEDC/FKernel/Continuation.lean`

Rationale:
Single-implication structural probe over the core continuation relation: it characterizes the empty history as the only left source whose continuations all collapse onto the right argument. The paper has rich continuation infrastructure (def:continuation-relation, def:continuation-step-rules, def:continuation-morphism-comp-closed, def:continuation-morphism-composite-left-factor, def:continuation-pattern-hardening) but no theorem extracting an emptiness conclusion from a universal probe condition. No board entry addresses left-unit probing of ContR — B-06/B-18 concern naming-certificate boundaries (additive vs unary) rather than the underlying continuation relation. The statement is testable on the closed inductive history structures (BHist/probes) without auxiliary axioms, so the formalization route is clean.

---

### B-252 - QuotientRing multiplication descends to cosets

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | QuotientRing multiplication descends to cosets |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 10/10 |
| Novelty | 9/10 |

Problem:
Under Ring↑ R and Ideal↑ I, if a ∼I a′ and b ∼I b′, then a ·R b ∼I a′ ·R b′, so QuotientRing↑ multiplication is representative-independent.

Local inputs:
- `papers/bedc/parts/concrete_instances/85_quotientring_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/83_ideal_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/84_quotientgroup_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/42_ring_namecert_construction.tex`

Rationale:
QuotientRing↑ (chapter 85) is the multiplicative lift of QuotientGroup↑ along Ideal↑, but the surrounding theorems on the BOARD and in the paper coverage cover only quotient-group / centralizer-coset closure and ring/module representative transport (B-19, B-23). Well-definedness of multiplication on cosets is a genuinely missing ring-specific certificate prerequisite that uses ideal absorption plus ring distributivity — not a paraphrase of any module representative target. High value: it is on the critical path for the QuotientRing↑ certificate.

---

### B-253 - Matrix transpose reverses product over the opposite ring

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | Matrix transpose reverses product over the opposite ring |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 9/10 |

Problem:
Under Mat↑ over Ring↑ R, for carried conformable matrices A,B, transpose(A ·R B) is Mat↑-classified over Rop with transpose(B) ·Rop transpose(A).

Local inputs:
- `papers/bedc/parts/concrete_instances/48_matrix_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/42_ring_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/39_monoid_namecert_construction.tex`

Rationale:
Chapter 48 (Matrix) currently exposes identity, associativity, finite-fold distribution, and multiplication classifier congruence; no anti-homomorphism statement crossing the opposite-ring certificate exists on BOARD or in paper coverage. This is a structural counterpart that consumes already-proven opposite-operation certificates from the ring/monoid layers, distinct from any module-side or quotient-ring entry.

---

### B-254 - Two-index fold swap from finite permutation invariance

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | Two-index fold swap from finite permutation invariance |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
Under a commutative additive finite-fold certificate with permutation invariance, if sτ(k,j) ∼R s(j,k) pointwise, then ΣJ(j ↦ ΣK(k ↦ s(j,k))) ∼R ΣK(k ↦ ΣJ(j ↦ sτ(k,j))).

Local inputs:
- `papers/bedc/parts/concrete_instances/48_matrix_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/49_finite_additive_scalar_fold.tex`
- `papers/bedc/parts/concrete_instances/42_ring_namecert_construction.tex`

Rationale:
Chapter 48 cites two-index fold swap as a stability obligation but it is not derived from the underlying finite-additive-scalar-fold layer (chapter 49, def:finite-additive-scalar-fold present in coverage but no fold-swap theorem). Establishing this collapses an assumed matrix-level certificate field into a derived theorem — strictly upstream of B-08/B-19/B-23 patterns and not duplicated by any module or polynomial entry on BOARD.

---

### B-255 - Singleton determinant row-swap sign collapse

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | Singleton determinant row-swap sign collapse |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
Under singleton Determinant↑, if M′ is obtained from singleton-carried M by a row-swap ledger with sign endpoint s, then det_e(M′) ∼R s ·R det_e(M); the singleton sign classifier further collapses to det_e(M′) ∼R det_e(M).

Local inputs:
- `papers/bedc/parts/concrete_instances/86_determinant_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/48_matrix_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/43_commring_namecert_construction.tex`

Rationale:
Chapter 86 advertises row-swap sign behavior as a determinant stability obligation; the existing theorem in 86 covers endpoint correspondence and multiplicativity but not row-swap discharge. No determinant entry sits on BOARD. Compact, in-scope target that closes a named obligation in the singleton case without requiring a full determinant theory expansion.

---

### B-256 - CatLimit apex uniqueness from universal cones

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | CatLimit apex uniqueness from universal cones |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 10/10 |

Problem:
Under CatLimit↑ for a fixed Functor↑ diagram D, if L and L′ are both certified limiting cones, there exist comparison morphisms u:L→L′ and v:L′→L whose composites are classified as the respective identities.

Local inputs:
- `papers/bedc/parts/concrete_instances/107_catlimit_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/60_category_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/61_functor_namecert_construction.tex`

Rationale:
Chapter 107 introduces CatLimit↑ as a universal cone but the canonical apex-uniqueness theorem is missing from BOARD and from visible paper coverage (no thm:catlimit-* labels). Distinct from the functor-composition (B-11) and natural-transformation composition (B-14) targets because it consumes the universal-cone field directly to derive an isomorphism in the apex layer. Foundational for any future categorical limit machinery.

---

### B-257 - CatLimit and CatColimit are opposite-dual certificates

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | CatLimit and CatColimit are opposite-dual certificates |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 9/10 |

Problem:
Under CatLimit↑(C,D,L), applying opposite-category and opposite-functor certificate data yields CatColimit↑(Cop,Dop,Lop), and the converse follows after double-opposite identification.

Local inputs:
- `papers/bedc/parts/concrete_instances/107_catlimit_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/108_catcolimit_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/60_category_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/61_functor_namecert_construction.tex`

Rationale:
Chapters 107 and 108 advertise CatLimit↑/CatColimit↑ as dual interfaces; the opposite-category/opposite-functor identities exist in earlier category chapters but the duality bridge between the two limit interfaces is not proven on BOARD or in coverage. Reuses already-derived opposite machinery to close an advertised duality at the limit layer — distinct from the apex-uniqueness target since it transports the universal-cone certificate across the opposite construction rather than deriving it.

---

### B-258 - AdjunctionUp-Induced MonadUp Ledger Certification

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | AdjunctionUp-Induced MonadUp Ledger Certification |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 9/10 |

Problem:
Under certified Cat↑, Functor↑, NatTrans↑, and AdjunctionUnitCounitCarrier data for F ⊣ G, the induced endofunctor G ∘ F with unit η and multiplication G ε F satisfies the Monad↑ carrier laws with multiplication ledger obtained by whiskering the counit ledger.

Local inputs:
- `papers/bedc/parts/concrete_instances/36_category_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/37_functor_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/38_nattrans_namecert_construction.tex`

Rationale:
Sits naturally on the categorical track that B-11/B-14/B-17 ... B-228 are building (Cat↑ → Functor↑ → NatTrans↑ → Adjunction↑). No existing BOARD entry or paper label introduces a Monad↑ certificate, and the claim is fully concrete: certified adjunction data plus whiskering ledger transport ⇒ Monad↑ carrier laws hold with an explicit multiplication ledger. Distinct from adjunction composition because the construction object (an endofunctor with unit/multiplication) and the obligation set (monad triangle/associator coherence) are different from triangle determinacy.

---

### B-259 - NatTransUp Whiskering Interchange Ledger Exactness

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | NatTransUp Whiskering Interchange Ledger Exactness |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |

Problem:
Under certified Functor↑ and NatTrans↑ data, vertical-then-horizontal composition of natural transformations equals horizontal-then-vertical composition with the two BEDC ledgers classifier-same.

Local inputs:
- `papers/bedc/parts/concrete_instances/37_functor_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/38_nattrans_namecert_construction.tex`

Rationale:
The interchange law is a 2-dimensional coherence statement that B-14 (component-wise naturality of the composite) does not address: B-14 fixes a single direction of composition, while interchange forces equality between two distinct nesting orders of horizontal and vertical pasting plus equal ledger transport. Required as a prerequisite by any later monad/adjunction whiskering result, and no `\label{thm:nattrans-interchange...}` exists in current paper coverage.

---

### B-260 - Composite Gap Associativity for Three-Stage Compression

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | Composite Gap Associativity for Three-Stage Compression |
| Layer | core |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |

Problem:
Under three composable GapPolicy interfaces with layered coverage and separation hypotheses, the left-nested and right-nested CompGap judgments yield the same final token classifier relation and equivalent intermediate witness ledgers.

Local inputs:
- `papers/bedc/parts/core/03_relational_extension_and_continuation.tex`
- `papers/bedc/parts/core/08_typed_naming_certificates.tex`
- `papers/bedc/parts/proof_obligations/exact_globalize.tex`

Rationale:
Sharpens cor:ledger-composition-principle (which is a 2-stage statement) to a 3-stage associativity theorem with explicit witness-ledger equivalence between the two parenthesizations. Lives in the core CompGap layer and is reusable downstream wherever ledger composition needs to be reassociated (e.g., the AdjunctionUp/MonadUp candidates above). Concrete implication form, no paper label currently asserts associativity of CompGap.

---

### B-261 - NameCert Composition for Stable Transformations

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | NameCert Composition for Stable Transformations |
| Layer | hardening |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |

Problem:
Under SemanticNameCert carriers for source, intermediate, and target classifiers, if two StableTransformation witnesses satisfy descent and ledger soundness, then their composite transformation satisfies a SemanticNameCert-style stability certificate with composite ledger policy.

Local inputs:
- `papers/bedc/parts/core/08_typed_naming_certificates.tex`
- `papers/bedc/parts/hardening/composite_gap_ledger.tex`
- `papers/bedc/parts/proof_obligations/descent_certificate.tex`

Rationale:
Distinct from B-17 (presentation weakening of a single SemanticNameCert) because it is a binary composition closure result for stable transformations along three classifiers. Provides the missing compositional closure on the hardening layer parallel to what category-theoretic composition theorems give in the concrete_instances layer. The implication form is precise and the local inputs already exist.

---

### B-262 - FunctorUp Composition Obstruction Without Classifier Replacement

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | FunctorUp Composition Obstruction Without Classifier Replacement |
| Layer | proof_obligations |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
Under raw object and morphism maps preserving identities and raw composition but lacking classifier-replacement stability, there exists a NatTrans↑ whiskering obligation whose naturality classifier cannot be transported, hence Functor↑ composition certification does not follow.

Local inputs:
- `papers/bedc/parts/concrete_instances/37_functor_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/38_nattrans_namecert_construction.tex`
- `papers/bedc/parts/proof_obligations/lean_scaffold_contract.tex`

Rationale:
Negative counterpart to B-11 (positive functor composition closure): explicitly isolates classifier-replacement stability as a non-redundant field by exhibiting a finite obstruction. Belongs cleanly in proof_obligations alongside B-18 / B-20 / B-24-style independence theorems for additive and module certificates. The candidate is concrete (whiskering obligation as the witness of failure) and not paraphrased by any existing BOARD entry or paper label.

---

### B-263 - Matrix transpose classifier involution

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | Matrix transpose classifier involution |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
Under the Mat↑ setup over a scalar Ring↑, A ∼Mat B implies A^T ∼Mat B^T, and for every carried A, (A^T)^T ∼Mat A under the original pointwise classifier.

Local inputs:
- `papers/bedc/parts/concrete_instances/24_matrix_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/18_ring_namecert_construction.tex`

Rationale:
Definition 48.70 introduces matrix transpose and Theorem 48.71 proves product-reversal over the opposite ring, but the paper does not isolate transpose itself as a classifier-preserving involution. No BOARD entry (B-06..B-31) addresses matrix transpose. The two-part claim (congruence + involution) is tight and uses only the pointwise index swap, making it a genuine prerequisite/sibling of 48.71 rather than a paraphrase. Lands cleanly in concrete_instances/24_matrix_namecert_construction.tex.

---

### B-264 - Opposite ring double-opposite rigidity

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | Opposite ring double-opposite rigidity |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
Under a Ring↑ R, the iterated opposite construction (R^op)^op coincides with R on carrier, classifier, additive data, unit, multiplication, stability rows, and ledger rows.

Local inputs:
- `papers/bedc/parts/concrete_instances/18_ring_namecert_construction.tex`

Rationale:
Category, functor, and lattice chapters carry explicit double-opposite data-identity theorems, but the ring-level analogue is missing. Distinct from B-28 (which is a forgetful projection CommRing↑ → Ring↑); this is involutivity of the opposite-ring construction itself. No matching label appears in paper_coverage (no `thm:ring-double-opposite` or similar). Fills a structural gap and supports later module/algebra reuse.

---

### B-265 - QuotientRing additive descent to ideal cosets

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | QuotientRing additive descent to ideal cosets |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
Under a Ring↑ R and Ideal↑ I, if a ≡I a′ and b ≡I b′ for the ideal-coset relation defined by I(a −R a′), then (a +R b) ≡I (a′ +R b′) and (−R a) ≡I (−R a′).

Local inputs:
- `papers/bedc/parts/concrete_instances/61_quotientring_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/59_ideal_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/18_ring_namecert_construction.tex`

Rationale:
Chapter 85 establishes the ideal-coset relation and proves multiplication descent, but the additive and negation descent legs are not standalone theorem sites. This is the additive prerequisite to a complete representative-independence package for QuotientRing↑ and is genuinely distinct from the proved multiplicative case. No BOARD entry covers quotient rings, and no `thm:quotientring-additive-descent` label appears in paper_coverage.

---

### B-266 - Determinant singleton row-swap sign collapse

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | Determinant singleton row-swap sign collapse |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |

Problem:
In the singleton Determinant↑ setup, any certified row-swap endpoint S of a singleton-carried matrix M satisfies CommRingSingletonClassifier(det_e(S), −det_e(M)) and hence CommRingSingletonClassifier(det_e(S), det_e(M)).

Local inputs:
- `papers/bedc/parts/concrete_instances/62_determinant_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/24_matrix_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/19_commring_namecert_construction.tex`

Rationale:
Definition 86.1 lists row-swap sign collapse among determinant stability obligations; Theorem 86.2 records endpoint correspondence, identity, classifier transport, and multiplicativity but not the alternating-law sibling. The singleton scaffold makes the proof small (singleton classifier collapses sign) while exercising the row-swap obligation directly. No BOARD entry addresses determinants, and no matching label appears in paper_coverage. Narrow but honest scope.

---

### B-267 - LinearMap composition preserves certificate

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | LinearMap composition preserves certificate |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 9/10 |

Problem:
Under a common scalar Ring↑, if LinearMapCert_R(M,N; f) and LinearMapCert_R(N,P; g) hold for Module↑ objects M, N, P, then LinearMapCert_R(M,P; g ∘ f) holds with composed carrier, classifier, stability, and ledger witnesses.

Local inputs:
- `papers/bedc/parts/concrete_instances/23_linearmap_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/21_module_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/18_ring_namecert_construction.tex`

Rationale:
The LinearMap↑ chapter supplies the certificate interface and proves kernel/image inheritance, but composition closure is not packaged. Foundational structural theorem prerequisite for any later categorical or endomorphism reuse of certified linear maps. Distinct from module scalar-action targets (B-08, B-19, B-20, B-23, B-24) because it concerns morphism composition closure, not module element classifier behavior. No paper label matches.

---

### B-268 - Composite gap intermediate-witness sameness from same admitted source

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Composite gap intermediate-witness sameness from same admitted source |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
Under layered first-gap separation, if CompGap(z_1, h) and CompGap(z_2, h) hold over the same admitted source h with intermediate witnesses y_1 and y_2 respectively, then interSame(y_1, y_2) holds.

Local inputs:
- `papers/bedc/parts/core/07_gap_policies_coverage_separation_and_composition.tex`
- `lean4/BEDC/FKernel/Gap.lean`

Rationale:
Chapter 07 lines 117-118 (proof of thm:composite-gap-separation) explicitly derives 'First-layer separation gives interSame(y_1,y_2)' as an intermediate step but the chapter never extracts it as its own labeled theorem. The chapter has 8 labeled theorems (gap-coverage, gap-separation, gap-separation-from-memberships, gap-representative, composite-gap-coverage, composite-gap-separation, composite-exactness-from-layers, composite-representative-for-admitted-source) and the dual 'finalSame from same source' direction is named (composite-gap-separation), while the strictly stronger structural assertion at the intermediate level is left implicit. Category 7 (composite consequence) and Category 8 (constructor inversion / determinism for the existential unpacking of CompGap). Closeable in 1 round: apply compGap_left_witness twice, then first-layer gap-separation. Required infrastructure (gap-separation, compGap-left-witness leanvariant) already present.

---

### B-269 - Package representative for a generated answer-history

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Package representative for a generated answer-history |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
Under PkgPol(Π), for every generated answer-history s, there exists a package token p with Pkg(Π, s, p) such that for every t with hsame(s, t) and Pkg(Π, t, q), psame(p, q) holds.

Local inputs:
- `papers/bedc/parts/core/06_packages_and_package_policies.tex`

Rationale:
Chapter 06 has only one labeled theorem (thm:packages-classify-signatures-core), which states extensionality and grounding as biconditionals but does not assemble them into a representative-selection statement. The exact dual lives one chapter later as thm:gap-representative-for-admitted-source (07.tex:59) for gap policies. The asymmetry — gap policy has its representative theorem named, package policy does not — is a clean editorial gap. Category 7 (composite consequence: combine PkgPol existence field with extensionality field). Closeable in 1 round: existence supplies p; extensionality applied to (s, t, hsame(s,t), p, q) supplies psame(p, q).

---

### B-270 - QuotientRing ideal-coset equivalence relation

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (codex) |
| Object | QuotientRing ideal-coset equivalence relation |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 9/10 |

Problem:
If the ideal certificate supplies zero closure, additive-inverse closure, additive closure, and classifier transport, then the ideal-coset relation $\equiv_I$ on a $\RingUp$ carrier is reflexive, symmetric, and transitive.

Local inputs:
- `papers/bedc/parts/concrete_instances/61_quotientring_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/ideal/`
- `papers/bedc/parts/concrete_instances/ring/18_ring_certificate_and_additive_laws.tex`

Rationale:
Foundational gap directly upstream of the existing QuotientRing descent theorems. The paper defines $\equiv_I$ in `def:quotientring-ideal-coset-relation` and proves operation descent in `thm:quotientring-multiplication-descends-to-cosets` and `thm:quotientring-additive-descent`, but never proves the relation is an equivalence relation. Without that, the descent results cannot license a well-defined coset quotient. The claim is a single concrete implication, ideal-closure-fields imply equivalence-relation laws, and lives squarely in concrete_instances next to the existing quotient-ring chapter. Distinct from B-25..B-29 (lattice) and B-19..B-24 (module/commring structure) since none touch quotient construction. Required as a prerequisite before any further QuotientRing certificate-field work.

---

### B-271 - AbGroup additive negation is involutive: -(-a) ~ a

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | AbGroup additive negation is involutive: -(-a) ~ a |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 7/10 |

Problem:
Under an AbGroupUp(M) certificate, for every carried element x of M, the additive negation satisfies -(-x) ~_M x.

Local inputs:
- `papers/bedc/parts/concrete_instances/17_abgroup_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/abgroup/17_abgroup_torsion_subgroup_closure.tex`
- `papers/bedc/parts/concrete_instances/group/namecert_construction_core/02_certificate.tex`

Rationale:
Hungerford 'Algebra' ch.I §1 includes (-(-a)) = a as an immediate textbook consequence of additive group axioms. Chapter 17_abgroup has 23 theorems (centralizer/normalizer-flavored, double cancel, mul-balanced, etc.) and a forgetful prop:abgroup-forgets-group-certificate (B-53), but `grep -E 'abgroup.*neg.*involu|neg.{0,5}neg|negation.{0,30}involu'` against papers/bedc/parts/ returns 0 labeled theorems for AbGroup negation involutive. All prereqs already exist: (i) thm:group-left-inverse-involutive and thm:group-right-inverse-involutive in group/namecert_construction_core/02_certificate.tex provide inv(inv(x)) ~ x in multiplicative form; (ii) prop:abgroup-forgets-group-certificate (B-53) provides the forgetful that turns AbGroup additive structure into Group multiplicative structure. The proof is a one-line transport of group inverse-involutivity along the forgetful, so the theorem closes in 1 codex round.

---

### B-272 - Polynomial singleton evaluation: eval at any alpha of [c] returns c

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Polynomial singleton evaluation: eval at any alpha of [c] returns c |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 7/10 |

Problem:
Under a RingUp(R) certificate with Horner evaluation as in def:polynomial-horner-evaluation, for every carried scalar c and every carried evaluation point alpha, Eval_{alpha,R}(cons(c, nil)) ~_R c.

Local inputs:
- `papers/bedc/parts/concrete_instances/25_polynomial_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/25_polynomial_literal_addtrim.tex`

Rationale:
Hungerford 'Algebra' ch.III §5 records as a routine textbook fact that the constant polynomial [c] evaluates to c independent of the evaluation point. Chapter 25 has 22 theorems and an existing thm:polynomial-evaluation-at-zero-constant-term at line 406 of 25_polynomial_literal_addtrim.tex, but that theorem is the special case alpha=0 with arbitrary spine cons(a,t); it is NOT the singleton [c] evaluated at arbitrary alpha. Grep for 'eval.{0,5}singleton|singleton.{0,5}eval|polynomial.{0,30}cons.{0,5}nil' returns 0 labeled theorems. The Horner unfolding of cons(c, nil) is c +_R alpha *_R Eval(nil); Eval(nil) ~_R 0_R is a definitional row, alpha *_R 0_R ~_R 0_R is RingUp's right-zero absorption (already used in 18_ring_zero_product_and_signed_square.tex), and c +_R 0_R ~_R c is the additive zero unit. All three prereqs are present, so the proof is three classifier-rewrites and closes in 1 codex round.

---

### B-273 - Subgroup chain composition: K subgroup of G and H subgroup of K implies H subgroup of G

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Subgroup chain composition: K subgroup of G and H subgroup of K implies H subgroup of G |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
Given carrier predicates P_K and P_H over the carrier of G with SubgroupUp(G)(P_K) and the conjunction predicate P_H_in_G(x) := P_K(x) and P_H(x), if P_H satisfies the SubgroupUp closure rows internally to the P_K-restricted carrier (containment of e_G, closure under mul, closure under inv, hsame transport, restricted-classifier compatibility), then P_H_in_G satisfies SubgroupUp(G).

Local inputs:
- `papers/bedc/parts/concrete_instances/58_subgroup_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/58_subgroup_namecert_construction_core.tex`
- `papers/bedc/parts/concrete_instances/group/namecert_construction_core/02_certificate.tex`

Rationale:
Hungerford 'Algebra' ch.I §5 (Theorem 5.1 corollary) records subgroup chain transitivity as standard textbook fact. Chapter 58 has 18+16 theorems concentrated on centralizer/normalizer/quotient-classifier and B-127 (Subgroup intersection is a subgroup) and B-246 (Trivial subgroup carries SubgroupUp). Grep for 'subgroup.{0,5}of.{0,5}subgroup|nested.{0,5}subgroup|subgroup.{0,5}transit|chain.{0,5}subgroup' across papers/bedc/parts/ returns only one specific instance ratup-fieldup-affine-normalizer-subgroupup-inclusion-action at 58_subgroup_namecert_construction_core.tex line 351, not the general transitivity. All prereqs exist: (i) thm:subgroup-trivial-certificate at 58_subgroup_namecert_construction.tex line 542 enumerates the SubgroupUp row format (identity, product, inverse, transport, restricted-classifier); (ii) thm:subgroup-centralizer-intersection-classifier-mul-closed-from-empty-unit and the four sibling lemmas in 58_subgroup_namecert_construction_core.tex prove closure of conjunction predicates under each row; (iii) Group multiplication and inverse congruence are in group/namecert_construction_core/02_certificate.tex. The proof is row-by-row conjunction lifting and closes in 1-2 codex rounds. This is a stepping-stone toward Lagrange's theorem (B-141) — Lagrange currently cannot decompose the iterated coset structure without subgroup chain transitivity.

---

### B-274 - Categorical equivalence is closed under composition (transitivity of equivalences)

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Categorical equivalence is closed under composition (transitivity of equivalences) |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 9/10 |

Problem:
If `AdjunctionUnitCounitCarrier(p,q,a,u_1,c_1,l_1,r_1)` and `AdjunctionUnitCounitCarrier(q,r,a,u_2,c_2,l_2,r_2)` both satisfy the empty-roundtrip condition (l_i,r_i hsame to ε), then there exist `u_3,c_3,l_3,r_3` such that `AdjunctionUnitCounitCarrier(p,r,a,u_3,c_3,l_3,r_3)` holds and l_3,r_3 are hsame to ε.

Local inputs:
- `papers/bedc/parts/concrete_instances/88_equivcat_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/85_adjunction_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/85_adjunction_namecert_certificate.tex`
- `papers/bedc/parts/concrete_instances/85_adjunction_namecert_triangle_carrier.tex`

Rationale:
Chapter 88 contains 11 theorems (88_equivcat_namecert_construction.tex lines 10, 30, 64, 85, 107, 130, 148, 171, 192, 212, 234) and ALL labels begin `thm:equivcat-adjunction-empty-roundtrip-...`; every existing theorem decomposes or characterizes a SINGLE equivalence's empty-roundtrip witness. None compose two equivalences. Grep for `equivcat.*compos|equivcat.*transit|equiv.*pr.serv.*lim|equivcat-transitive` across papers/bedc/parts returns 0 hits. The chapter intro at line 4 explicitly calls $\EquivCatUp$ 'the structural notion of sameness for $\NameCert_{\CategoryUp}$ instances' — sameness should be transitive but that property is unproven. Infrastructure is in place: chapter 85 supplies AdjunctionUnitCounitCarrier across general (p,q) prefix pairs (85_adjunction_namecert_triangle_carrier.tex lines 16-186 give component-empty / collapse / prefix-deterministic theorems that suffice as building blocks).

---

### B-275 - Continuous-map image of a principal-suffix filter is a principal-suffix filter on the target

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Continuous-map image of a principal-suffix filter is a principal-suffix filter on the target |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 9/10 |

Problem:
If `FilterPrincipalSuffix(base,left,right,...)` (chapter 71) and `ContinuousMapCarrier(base,map,target,modulus,cert,distance)` (chapter 34), then there exist target histories carrying a `FilterPrincipalSuffix` witness on `target` whose intersection-closure and unary-commuting-square fields are determined by the source filter and the continuous-map graph.

Local inputs:
- `papers/bedc/parts/concrete_instances/71_filter_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/34_continuous_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/34_continuous_namecert_function_carrier.tex`

Rationale:
Chapter 71 has 15 theorems all labeled `thm:filter-principal-suffix-...` (71_filter_namecert_construction.tex lines 10, 32, 53, 71, 93, 114, 132, 146, 166, 188, 208, 236, 259, 281, 300). Every existing theorem is INTERNAL to a single filter (intersection closure, commuting square, point determinism, semantic name-cert). Grep `filter.*continu|continuous.*filter|filter.*image|filter.*map|filter.*pushforward` across papers/bedc/parts returns 0 file matches. Chapter intro line 4 declares the filter is 'the constructive analogue of mathlib-style \texttt{Filter} for the BEDC topology and analysis layers' — pushforward under continuous maps is the canonical first interaction with the topology layer (mathlib's `Filter.map`), and it is absent.

---

### B-276 - Continuous image of a compact source is compact, not merely totally bounded

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Continuous image of a compact source is compact, not merely totally bounded |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
If `ContinuousMapCarrier(source,map,target,modulus,cert,distance)` and the source carries a full `CompactWitnessCarrier` (totally-bounded plus located refinement chain), then the target image bundle inherits a CompactWitness with both the totally-bounded image fields AND a located refinement chain transported through the modulus, not merely the totally-bounded image proved in proposition 35b.

Local inputs:
- `papers/bedc/parts/concrete_instances/35_compact_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/35b_compact_image_total_bounded.tex`
- `papers/bedc/parts/concrete_instances/34_continuous_namecert_construction.tex`

Rationale:
`35b_compact_image_total_bounded.tex` lines 41-125 prove `prop:uniformly-continuous-image-totally-bounded-source` ONLY for the totally-bounded fragment (it produces an `ImageFiniteNetLedger` but no located refinement). Chapter 35 has 19+ refinement-chain theorems (lines 15-553 including `thm:compact-witness-carrier-located-extension-closed` and `thm:compact-located-refinement-chain-transitivity`) for the located component of the compact carrier on a single source, but no theorem lifts the totally-bounded image proof to a full compact image. Grep `image.*compact|compact-image|continuous.*compact` across papers/bedc/parts returns only the existing totally-bounded variant and a roadmap mention. In BEDC, `compact = totally-bounded + located + Cauchy-completeness`; the located component's preservation under continuous maps is the missing piece that distinguishes the claim from what is already proved.

---

### B-277 - EqType class membership is transitive at the class-carrier layer

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | EqType class membership is transitive at the class-carrier layer |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |

Problem:
If a history h belongs to the equality-type class anchored at `anchor` (i.e., `EqtypeClassCarrier(anchor,h)`) and h' belongs to the equality-type class anchored at h (`EqtypeClassCarrier(h,h')`), then h' belongs to the equality-type class anchored at `anchor`.

Local inputs:
- `papers/bedc/parts/concrete_instances/109_eqtype_namecert_construction.tex`

Rationale:
Chapter 109 has 13 theorems all labeled `thm:eqtype-class-carrier-...` or `thm:eqtype-class-carrier-anchor-hsame-transport` (109_eqtype_namecert_construction.tex lines 10, 23, 37, 50, 64, 78, 93, 107, 128, 142, 156, 177, 194). Every theorem treats specific anchor patterns (`e1-anchor`, `e0-anchor`, `visible-context`) with READBACK / DETERMINISTIC / ABSURD / SEMANTIC-NAMECERT patterns. The chapter intro at line 4 calls $\EqUp$ 'the foundational equality layer underlying every $\psame$ classifier' — classical equality is reflexive/symmetric/transitive, but the only equivalence-relation property proved is HSAME transport (`thm:eqtype-class-carrier-anchor-hsame-transport` line 194), not class-carrier transitivity (chained anchor relation). Grep `eqtype.*reflex|eqtype.*sym|eqtype.*trans|reflex.*eqtype` returns only the unrelated anchor-transport theorem. The chain transitivity is a single-implication structural fact that fits the chapter's style and infrastructure.

---

### B-278 - Derivative metric quotients compose: chain rule on metric quotient witnesses

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Derivative metric quotients compose: chain rule on metric quotient witnesses |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 7/10 |
| Novelty | 9/10 |

Problem:
If `DerivativeMetricQuotient(f,z,h_f,q_f,d_f)` holds and `DerivativeMetricQuotient(g,q_f,h_g,q_g,d_g)` also holds (the inner derivative is taken at the outer quotient endpoint), and continuations chain via `Cont(f,append(h_f,h_g),q_g)`, then a composite metric-quotient witness exists for the chain f→g whose distance history is classifier-equal to the continuation product of d_f and d_g.

Local inputs:
- `papers/bedc/parts/concrete_instances/100_derivative_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/42_complex_differentiability_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/32_metric_namecert_construction.tex`

Rationale:
Chapter 100 has 19 theorems (100_derivative_namecert_construction.tex lines 28, 55, 80, 99, 117, 131, 146, 161, 176, 192, 207, 222, 242, 267, 289, 307, 327, 342, 356) all labeled `thm:derivative-metric-quotient-...` or `thm:derivative-cplx-diff-at-...`. Every theorem is about TRANSPORT (`hsame-transport` line 28), DETERMINACY (`result-deterministic` line 222, `hsame-step-result-deterministic` line 242), READBACK (`visible-context-readback` line 131-192), or NEGATIVE shape (`visible-step-same-quotient-absurd` line 289). Grep `chain.*rule|chainrule|derivative-chain|derivative.*compos|derivative.*product-rule|derivative.*linearity|derivative-leibniz|derivative-sum` returns 0 hits in the derivative chapter (only roadmap and complex-differentiability mentions of `composite modulus` in unrelated contexts). The chain rule is the canonical compositional theorem (foundational for any analytic chapter built on derivatives) and is genuinely absent.

---

### B-279 - Tensor product factorization is unique up to the tensor classifier

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Tensor product factorization is unique up to the tensor classifier |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
If `TensorProductSingletonFactor(l,r,t)` and `TensorProductSingletonFactor(l,r,t')` both hold for the same factor pair (l,r) with the same singleton-carrier source and target modules, then the two factorization endpoints t and t' are classifier-equal under the tensor classifier (hsame on the tensor carrier).

Local inputs:
- `papers/bedc/parts/concrete_instances/65_tensorproduct_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/21_module_namecert_construction.tex`

Rationale:
Chapter 65 has 12 theorems (65_tensorproduct_namecert_construction.tex lines 18, 36, 49, 67, 82, 97, 125, 139, 156, 172, 202, 230) covering EXISTENCE (`factor-witness` line 125), TRANSPORT (`factor-hsame-transport` line 139), SYMMETRY (`factor-source-target-swap` line 172, `factor-swap-symmetry` line 202), and ASSOCIATIVITY (`factor-associator` line 230). The chapter intro at line 4 says 'packages the universal bilinear factorization' — the universal property has both an EXISTENCE clause (proved via `factor-witness`) and a UNIQUENESS clause (any two factorizations agree). Grep `tensorproduct.*univers|tensor.*univers.*property|tensorproduct-uniqueness` returns 0 hits. The uniqueness clause as a single-implication theorem t hsame t' from two factor witnesses is missing and is a clean, single-step extension building only on `hsame-transport` and `factor-witness`.

---

### B-280 - Derivative empty-function quotient step zero result is absurd

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Derivative empty-function quotient step zero result is absurd |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
If DerivativeMetricQuotient(∅, z, h, q, dist) holds and the witness step displays as Ezero(s) for some s, then ⊥.

Local inputs:
- `papers/bedc/parts/concrete_instances/100_derivative_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/32_metric_namecert_construction.tex`

Rationale:
100_derivative_namecert_construction.tex has 19 theorems and 0 completed-target hits. thm:derivative-metric-quotient-empty-function-step-readback (line 100) handles the empty-function step but only proves q hsame h for a generic step. The exclusion of an Ezero-displayed step under the empty-function quotient regime is structurally analogous to thm:filter-principal-suffix-unary-intersection-zero-result-absurd (71_filter line 146) and thm:derivative-metric-quotient-distance-result-nonempty (line 118), but the empty-function-specific Ezero exclusion does not exist. Concrete single-implication, opens analysis chapter.

---

### B-281 - Residue pole data integral suffix closure

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Residue pole data integral suffix closure |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
If ResiduePoleData(f, z₀, r, p, g, I, ρ) holds, q is unary, and ContR(f, q, fq), then there exists Iq with ResiduePoleData(fq, z₀, r, p, g, Iq, ρ), ContR(I, q, Iq), and ContR(Iq, ρ, fq).

Local inputs:
- `papers/bedc/parts/concrete_instances/103_residue_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/49_contour_integral_operation.tex`

Rationale:
103_residue_namecert_construction.tex has 10 theorems and 0 completed-target hits. thm:residue-pole-data-residue-suffix-closure (line 56) proves residue suffix closure and thm:residue-pole-data-integral-prefix-closure (line 142) proves the integral prefix closure, but the integral SUFFIX closure (the obvious dual where q is appended after f rather than prefixed) is missing — there is no thm:residue-pole-data-integral-suffix-closure label. Single-implication concrete claim, structurally identical to the existing prefix variant. Opens an untouched complex-analysis chapter.

---

### B-282 - EquivCat empty-roundtrip identity carrier hsame transport in target prefix

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | EquivCat empty-roundtrip identity carrier hsame transport in target prefix |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
If the empty-roundtrip identity carrier exists for prefixes (p, q) and HSame(q, q'), then the empty-roundtrip identity carrier exists for (p, q').

Local inputs:
- `papers/bedc/parts/concrete_instances/88_equivcat_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/85_adjunction_namecert_construction.tex`

Rationale:
88_equivcat_namecert_construction.tex has 11 theorems and 0 completed-target hits. The chapter has determinacy theorems for source-prefix (line 212) and target-prefix (line 148) but NO hsame-transport theorem for the identity carrier under target prefix — labels at lines 10, 30, 64, 85, 107, 130, 148, 171, 192, 212, 234 are exclusively about determinacy/exclusion/exactness rather than transport. This is the basic stability claim required before composition of equivalences can ever be opened, and it follows directly from unary transport plus determinacy. Opens an untouched CT chapter.

---

### B-283 - Gamma Weierstrass Cauchy modulus stable under domain-core hsame transport

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Gamma Weierstrass Cauchy modulus stable under domain-core hsame transport |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 9/10 |

Problem:
If GammaDom(s) holds at apartness precision k₀ with Weierstrass modulus N(k) for the partial products P_N(s), and s hsame s', then GammaDom(s') holds at precision k₀ and the partial products P_N(s') admit the same modulus N(k).

Local inputs:
- `papers/bedc/parts/concrete_instances/53_gamma_function_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/40_complex_limit_namecert_construction.tex`

Rationale:
53_gamma_function_namecert_construction.tex has 19 theorems and 0 completed-target hits. thm:gamma-domain-core-hsame-transport (line 128) transports GammaDom membership under hsame and lem:gamma-weierstrass-cauchy (line 196) gives the explicit modulus, but the COMPOSITE — that the modulus itself is hsame-invariant on the GammaDom — is the natural missing stability claim. It is the classifier-level prerequisite for both thm:gamma-recurrence (line 220) and thm:gamma-reflection (line 239) to lift to representative-stable form. Opens special-functions chapter the loop has never touched.

---

### B-284 - Adele history-carrier visible-scale append result hsame transport

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Adele history-carrier visible-scale append result hsame transport |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
If the visible-scale append result is nonempty for adele history a and scale s, and a hsame a', then the visible-scale append result is nonempty for a' at the same scale s.

Local inputs:
- `papers/bedc/parts/concrete_instances/79_adele_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/78_padic_namecert_construction.tex`

Rationale:
79_adele_namecert_construction.tex has 30 theorems and 0 completed-target hits. The chapter has thm:adele-constant-slice-carrier-hsame-transport (line 572) for the constant slice and thm:adele-visible-scale-append-not-empty (line 242) for nonempty results, but there is no hsame-transport for the visible-scale append result itself — labels at lines 122, 143, 185, 204, 242, 464-538 cover the carrier nonempty / readback structure without relating different histories under hsame. A single-implication transport theorem is the missing structural prerequisite for adele-level carrier reasoning. Opens number-theory chapter the loop has never touched.

---

### B-285 - Finite image nets produce image locatedness ledgers

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (codex) |
| Object | Finite image nets produce image locatedness ledgers |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |

Problem:
Under a compact-source / metric-target continuous-image setup, ImageFiniteNetLedger together with target metric-distance finite comparison data implies ImageLocatedRefinementLedger for the graph image predicate.

Local inputs:
- `papers/bedc/parts/concrete_instances/33_compact_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/32_metric_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/34_continuous_namecert_construction.tex`

Rationale:
Connects two already-named compact-image predicates (def:compact-image-finite-net-ledger and def:compact-image-located-refinement-ledger) with an explicit implication. Both endpoints exist in the paper as definitions, but no theorem currently bridges them — the compact chapter exposes finite-net and located-refinement as parallel obligations without a derivation showing that the finite-net version plus metric-distance comparison data is sufficient to recover the located-refinement version. The claim is single-implication, scoped to existing concrete_instances setups (compact + metric), and does not overlap any existing BOARD entry (B-06..B-31 cover naming, lattices, modules, polynomials, functors/nattrans, intervals, continuous-modulus composition — none touch image-locatedness). It is a clean prerequisite-style lemma rather than a broad survey item, so the loop can converge on a finite proof using already-formalized compact / metric scaffolding.

---

### B-286 - Continuous-map image determinacy for principal-suffix points

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (codex) |
| Object | Continuous-map image determinacy for principal-suffix points |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 7/10 |
| Novelty | 7/10 |

Problem:
If two displayed image rows are induced by the same continuous-map graph from the same principal-suffix source point, then their target histories are history-same.

Local inputs:
- `papers/bedc/parts/concrete_instances/34_continuous_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/32_metric_namecert_construction.tex`
- `papers/bedc/parts/core/03_relational_extension_and_continuation.tex`

Rationale:
This is a foundational image-determinacy / graph-functionality claim about ContinuousMap carriers, formulated as a single implication on principal-suffix points. It is distinct from B-12 (which is about uniform-continuity modulus composition) and from the existing continuous-map definitions (def:continuousmap-carrier, def:continuousmapup-metric-*), which specify carrier and stability fields but do not separately project image determinacy as a labeled theorem. Filling this gap clarifies the function-likeness of continuous-map graphs at the certificate level and gives downstream chapters a citable handle for source-target consistency.

---

### B-287 - EquivCat empty-roundtrip identity carrier source-prefix hsame transport

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (codex) |
| Object | EquivCat empty-roundtrip identity carrier source-prefix hsame transport |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 7/10 |

Problem:
Under AdjunctionUnitCounitCarrier(p,q,a,unit,counit,left,right) with left ~ emp, right ~ emp, and p hsame p', the empty roundtrip identity carrier transports to AdjunctionUnitCounitCarrier(p',q,a,emp,emp,emp,emp) with empty identity components on (p',q,a) and (q,p',a).

Local inputs:
- `papers/bedc/parts/concrete_instances/88_equivcat_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/86_adjunction_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/85_nattrans_namecert_construction.tex`

Rationale:
Direct symmetric counterpart of the existing target-prefix transport theorem (thm:equivcat-empty-roundtrip-identity-carrier-target-prefix-hsame-transport, line 257). The paper currently proves transport along q hsame q' but not along p hsame p'; without it the EquivCat empty-roundtrip identity carrier behaves asymmetrically under classifier transport, which is a real gap given that the underlying Adjunction carrier is symmetric in its source and target prefixes. The proof should mirror the existing one: apply equivcat-empty-roundtrip-prefix-determinacy, transport unary membership along p hsame p', then re-apply adjunction-unit-counit-empty-components-exactness with both triangle results emp. Distinct from any current BOARD entry.

---

### B-288 - Gamma limit certificate hsame transport

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (codex) |
| Object | Gamma limit certificate hsame transport |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 6/10 |

Problem:
If s hsame t, GammaDom(s), and Gamma(s,z) hold with a Weierstrass limit witness, then Gamma(t,z) holds with the transported domain witness and the same Cauchy modulus, with z unchanged.

Local inputs:
- `papers/bedc/parts/concrete_instances/53_gamma_function_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/55_complex_topology_namecert_construction.tex`
- `papers/bedc/parts/core/03_relational_extension_and_continuation.tex`

Rationale:
The Gamma chapter ships transport theorems for the pole locus (thm:gamma-pole-locus-hsame-transport-witness), the domain core (thm:gamma-domain-core-hsame-transport), and the Weierstrass Cauchy modulus (thm:gamma-weierstrass-cauchy-modulus-hsame-transport), but no theorem closes the loop at the value level: Gamma(s,z) implies Gamma(t,z) under s hsame t. This theorem is the natural composition of the three existing transport theorems with ComplexLimitUp uniqueness, and it is the prerequisite needed for any downstream zeta argument that compares Gamma values across history-equivalent complex histories (notably the s ↦ 1-s reflection comparisons in the zeta functional equation chapter). Sits cleanly inside the existing concrete_instances/gamma scope, fills a known gap, and does not duplicate any existing BOARD entry.

---

### B-289 - MetricBallBudget 有限路径预算归纳

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | MetricBallBudget 有限路径预算归纳 |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
在 Met↑ 的 ball-budget setup 下, 若有限路径 x0,...,xn 的每条边满足 MetricBallBudget_d(x_i,x_{i+1}; r_i), 则 MetricBallBudget_d(x0,xn; r0+...+r_{n-1})。

Local inputs:
- `papers/bedc/parts/concrete_instances/32_metric_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/11_list_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/13_real_namecert_construction.tex`

Rationale:
Existing metric chapter has only the two-step composition theorem for ball budgets; this is the proper finite-path induction extension that closes path-budget transport via triangle inequality plus monotone budget addition. No BOARD entry covers metric ball-budget propagation, and paper labels show only def-level modulus / continuous data, not a path-budget theorem. Useful prerequisite for downstream compact and continuous targets, and small enough to close in one oracle round.

---

### B-290 - Compact 有限网见证的精度放宽

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | Compact 有限网见证的精度放宽 |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
在 Compact↑ setup 下, 若 n 是 ε-有限网见证且 ordered-real 预算给出 ε ≤ ε′, 则同一网见证 n 也是 ε′-有限网见证。

Local inputs:
- `papers/bedc/parts/concrete_instances/35_compact_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/32_metric_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/29_totalorder_namecert_construction.tex`

Rationale:
Compact stability certificate enumerates per-precision finite-net data plus precision-monotonicity as obligation fields, but neither BOARD nor paper labels (def:compact-uniform-finite-net, def:compact-finite-refinement-chain, etc.) elevate the precision-coarsening to a standalone theorem. Promoting it to a theorem unblocks later compact classifier and uniform finite-net ledger targets without overlapping prefix/refinement results. Short, concrete implication form; lands cleanly in concrete_instances.

---

### B-291 - Compact 见证分类器的传递闭合

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | Compact 见证分类器的传递闭合 |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
在 Compact↑ classifier setup 下, 若 K∼K′ 和 K′∼K″ 都由成员谓词的 carrier-sameness 双向等价给出, 则复合这些双向等价得到 K∼K″。

Local inputs:
- `papers/bedc/parts/concrete_instances/35_compact_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/32_metric_namecert_construction.tex`

Rationale:
Compact classifier specification defines compact-witness sameness via bidirectional membership evidence under carrier sameness; transitivity is the natural classification-style theorem but is not present in BOARD or paper labels (only def-level classifier specs appear). Distinct from prefix-closure/refinement targets — this is structural transitivity of the equivalence used for classifier sameness. Compact in size yet structurally important for downstream classifier-projection lemmas.

---

### B-292 - ContinuousMap 复合的代表元同余

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | ContinuousMap 复合的代表元同余 |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 9/10 |

Problem:
在 ContinuousMap↑ setup 下, 若 f∼f′ 且 g∼g′ under ContinuousMap classifier 且复合两侧的源域、目标域和 totally-bounded witnesses 匹配, 则 g∘f ∼ g′∘f′。

Local inputs:
- `papers/bedc/parts/concrete_instances/34_continuous_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/32_metric_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/35_compact_namecert_construction.tex`

Rationale:
B-12 covers forward closure of uniform-continuity moduli under composition; this candidate is the sibling congruence theorem at the classifier level — composition transports representative sameness through both factors. Genuinely distinct because it requires graph-output replacement, modulus mutual refinement, and codomain classifier transitivity, not just modulus composition. Not in paper labels (continuousmapup-metric-* are def-level only).

---

### B-293 - LinearMap 证书的复合闭合

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | LinearMap 证书的复合闭合 |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
在同一标量 Ring↑ 和三个 Module↑ setup 下, 若 f:M→N 与 g:N→P 是 certified LinearMap↑ carriers, 则 g∘f 携带 LinearMap↑ carrier、stability 和 ledger, 且其点态分类器由 f 与 g 的点态分类器复合给出。

Local inputs:
- `papers/bedc/parts/concrete_instances/22_linearmap_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/21_module_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/19_commring_namecert_construction.tex`

Rationale:
Linearmap chapter has carrier/source/pattern/classifier/stability/ledger definitions but no BOARD target on linear-map structural closure. Composition closure is the principal structure theorem for the linearmap certificate package, distinct from existing module-side targets B-08/B-23 (which are scalar-action obligations). Closes via additivity, scalar compatibility and pointwise classifier transport — clearly bounded scope.

---

### B-294 - Matrix 转置的双重刚性

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | Matrix 转置的双重刚性 |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |

Problem:
在 Matrix↑ setup 下, 若转置操作按同一 scalar classifier 逐坐标搬运矩阵 carrier, 则任意矩阵 A 满足 (Aᵀ)ᵀ ∼ A under Matrix↑ classifier。

Local inputs:
- `papers/bedc/parts/concrete_instances/23_matrix_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/19_commring_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/11_list_namecert_construction.tex`

Rationale:
Matrix chapter has carrier/classifier/stability/transpose-certified-scalar-carrier definitions but no transpose-involution theorem in BOARD or paper labels. Small structural rigidity result — two row/column swaps composed back to global structural equality at the matrix classifier level — that is not just a scalar-classifier transport. Tight scope, easily closeable in a short oracle pass.

---

### B-295 - ConvRad checked 行不能推出 Cauchy-Hadamard

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | ConvRad checked 行不能推出 Cauchy-Hadamard |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 10/10 |

Problem:
在 ConvRad↑ setup 中只假设 checked carrier、radius transport、coefficient transport 与 append-unary closure 行而不加入 analytic ledger policy 时, 存在两个同 checked 行的政策解释使 Cauchy-Hadamard exactness 的真值不同。

Local inputs:
- `papers/bedc/parts/concrete_instances/41_convergence_radius_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/40_power_series_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/44_complex_series_namecert_construction.tex`

Rationale:
ConvRad chapter explicitly separates checked NameCert rows from analytic ledger laws and leaves Cauchy-Hadamard limsup characterization as a ledger-policy obligation. This candidate elevates that separation into an obstruction/independence theorem closeable by exhibiting two policy interpretations sharing all checked rows but disagreeing on exact-radius law — entirely BEDC-internal, not external complex analysis. No analogous BOARD entry; def:conv-rad-* labels are all def-level.

---

### B-296 - CatLimit transport along pointwise certified diagram equivalence

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | CatLimit transport along pointwise certified diagram equivalence |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 9/10 |

Problem:
Under NameCertCat↑, if Functor↑ diagrams D,E:J→C admit a pointwise two-sided classifier-equivalent NatTrans↑, then any CatLimit↑(D,L,λ) transports componentwise to a CatLimit↑(E,L,λ_E).

Local inputs:
- `papers/bedc/parts/concrete_instances/36_category_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/37_functor_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/38_nattrans_namecert_construction.tex`

Rationale:
Lifts B-256's vertex uniqueness (already in BOARD context) to diagram-level invariance under NatTrans equivalence — a strictly stronger transport statement that has no analog in current BOARD or paper labels. Binds Functor↑/NatTrans↑/CatLimit↑ certificate fields together, and provides the natural stability lemma needed before any further CatLimit construction targets land. Single-implication form, lands cleanly in concrete_instances next to chapters 36-38.

---

### B-297 - Cone morphism classifier descent through NatTrans whiskering

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | Cone morphism classifier descent through NatTrans whiskering |
| Layer | core |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |

Problem:
Under certified Cat↑/Functor↑ composition and endpoint transport, if α:D⇒E is a NatTrans↑ and f is a ConeMor_D between D-cones, then post-whiskering f by α yields a ConeMor_E between the corresponding E-cones.

Local inputs:
- `papers/bedc/parts/concrete_instances/36_category_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/37_functor_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/38_nattrans_namecert_construction.tex`

Rationale:
Distinct from B-14 (vertical NatTrans composition naturality square): this is whiskering descent on cone morphism ledger, not on nattrans composition itself. Acts as the foundational lemma underneath the diagram-transport target above; isolating it prevents repeated ad hoc reproof in CatLimit/CatColimit follow-ups. Concrete single-implication form, anchored on the cone morphism ledger fields already in functor/nattrans chapters.

---

### B-298 - CatColimit vertex co-uniqueness from universal cocones

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | CatColimit vertex co-uniqueness from universal cocones |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 10/10 |

Problem:
For a fixed Functor↑ diagram D, if both C and C′ are CatColimit↑-certified universal cocone vertices, there exist comparison morphisms u:C→C′ and v:C′→C with u∘v and v∘u classified as the corresponding identity morphisms by the Cat↑ morphism classifier.

Local inputs:
- `papers/bedc/parts/concrete_instances/36_category_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/37_functor_namecert_construction.tex`

Rationale:
True dual of the existing CatLimit vertex uniqueness work — exercises the colimit direction of BEDC's classifier language, which is currently uncovered by both BOARD and paper labels. Tests symmetry/completeness of the universal property formulation under classifier-only equality. Single implication, no overlap with B-11/B-14/B-17 which all live on the limit/functor side.

---

### B-299 - SemanticNameCert stability under equivalence-refining classifier replacement

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | SemanticNameCert stability under equivalence-refining classifier replacement |
| Layer | hardening |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |

Problem:
If SemanticNameCert(S,P,L,C) holds and C′ is a classifier on S that mutually implies C while preserving P- and L-transport, then SemanticNameCert(S,P,L,C′) holds.

Local inputs:
- `papers/bedc/parts/core/08_typed_naming_certificates.tex`
- `papers/bedc/parts/proof_obligations/exact_globalize.tex`

Rationale:
Sibling but distinct from B-17 (presentation weakening on P,L with C fixed): this fixes S,P,L and replaces the classifier C, isolating which record fields are invariant under classifier swaps. Closes the symmetric half of the SemanticNameCert stability picture and prevents per-instance reproofs of isomorphic-classifier replacement downstream. Concrete one-line implication on a single record.

---

### B-300 - Subtype classifier reflects parent classifier

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | Subtype classifier reflects parent classifier |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 9/10 |

Problem:
Under Set↑ parent S, stable predicate P, and Subtype↑ setup, x ∼S y with P(x), P(y) implies (x,Px) ∼Sub (y,Py), and (x,Px) ∼Sub (y,Py) implies x ∼S y.

Local inputs:
- `papers/bedc/parts/concrete_instances/115_subtype_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/113_set_namecert_construction.tex`
- `papers/bedc/parts/core/08_typed_naming_certificates.tex`

Rationale:
Chapter 115 introduces Subtype↑ as the kernel-licit refinement type built from a parent Set↑ carrier with a decidable stable predicate, but no theorem in the existing paper or BOARD pins down that the subtype classifier is exactly the parent classifier restricted to predicate-witnesses. This biconditional is the canonical representation theorem for Subtype↑ and is a prerequisite for downstream subring/submodule/kernel constructions. It is not subsumed by B-17 (a generic SemanticNameCert presentation weakening), since this is concrete and bidirectional rather than a one-way pointwise weakening.

---

### B-301 - FinSet enumeration membership exactness

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | FinSet enumeration membership exactness |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 10/10 |
| Novelty | 9/10 |

Problem:
Under FinSet↑ given by Set↑ carrier and enumeration list xs, a is a FinSet member iff there exists x ∈ xs with a ∼A x.

Local inputs:
- `papers/bedc/parts/concrete_instances/114_finset_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/113_set_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/35_list_namecert_construction.tex`

Rationale:
Chapter 114 stipulates FinSet↑ as NameCertSet↑ plus a finite enumeration witness via NameCertList↑, but the paper currently only carries the carrier definition and certificate entry; no theorem ties FinSet membership to existence of a classifier-equal enumeration point. This is the central representation theorem for FinSet↑ and is a prerequisite for Permutation↑, Graph↑, and combinatorial certificate work. It is orthogonal to BOARD's polynomial/list zero-tail normalization targets, which concern raw operation invariance rather than membership classification.

---

### B-302 - FinSet classifier invariant under enumeration permutation

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | FinSet classifier invariant under enumeration permutation |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
Under a fixed Set↑ classifier, if FinSet↑ enumeration lists xs, ys are connected by a certified permutation preserving ∼A pointwise, then they induce the same FinSet classifier.

Local inputs:
- `papers/bedc/parts/concrete_instances/114_finset_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/118_permutation_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/35_list_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/113_set_namecert_construction.tex`

Rationale:
FinSet↑ enumeration is presentation data, so the classifier should not depend on the order of the enumeration witness; without this theorem the same finite set has multiple non-canonical FinSet classifiers. The claim is concrete and uses only certified permutation plus pointwise classifier preservation, distinct from BOARD's categorical composition targets (B-11/B-14) and from polynomial/list zero-tail rewrites. It also serves as a downstream substrate for Permutation↑ presentation independence.

---

### B-303 - Permutation composition closure for FinSet bijections

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | Permutation composition closure for FinSet bijections |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 10/10 |
| Novelty | 9/10 |

Problem:
Under Permutation↑ over FinSet↑, if σ and τ are FinSet-classified self-bijections then τ∘σ is a carried permutation and preserves both forward and inverse bijection classifiers.

Local inputs:
- `papers/bedc/parts/concrete_instances/118_permutation_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/114_finset_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/113_set_namecert_construction.tex`

Rationale:
Chapter 118 presents Permutation↑ as the carrier of FinSet↑ self-bijections supplying the underlying carrier and action data for SymGroup↑, but no theorem currently records that bijection composition stays inside the certificate. This closure is the prerequisite for SymGroup↑ structure work and is structurally distinct from B-11 functor composition (different objects, different inputs: FinSet classifier transport plus inverse witness composition).

---

### B-304 - SymGroup forgets to Group certificate

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | SymGroup forgets to Group certificate |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 7/10 |

Problem:
Under SymGroup↑ setup, forgetting the FinSet action presentation while keeping composition, identity, inverse, and classifier yields a Group↑ name certificate.

Local inputs:
- `papers/bedc/parts/concrete_instances/119_symgroup_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/118_permutation_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/40_group_namecert_construction.tex`

Rationale:
Chapter 119 declares SymGroup↑ as the canonical instance packaging Permutation↑ under composition into NameCertGroup↑, but no forgetful Group↑ projection theorem exists. This is a direct sibling to B-28 (CommRing forgets to Ring) and follows the same forgetful-projection pattern, so novelty is moderate; the chapter and underlying objects (Permutation↑ vs. ring multiplication) are entirely different, justifying a separate slot rather than absorbing into B-28.

---

### B-305 - Graph edge transport along vertex classifier

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | Graph edge transport along vertex classifier |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 10/10 |
| Novelty | 9/10 |

Problem:
Under Graph↑ over Set↑, if u ∼V u′ and v ∼V v′ then Edge(u,v) implies Edge(u′,v′), so the edge classifier is invariant under vertex representative replacement.

Local inputs:
- `papers/bedc/parts/concrete_instances/120_graph_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/113_set_namecert_construction.tex`
- `papers/bedc/parts/core/08_typed_naming_certificates.tex`

Rationale:
Chapter 120 defines Graph↑ as a Set↑ vertex carrier with a binary edge relation, used as the substrate for Tree↑ and poset-as-DAG, but no theorem proves that the edge relation transports under vertex classifier equivalence. This is the basic soundness theorem for Graph↑ and prerequisite for Tree↑; it is unrelated to the automorphic-adele-graph carrier already in the paper, which concerns visible-context readback rather than basic combinatorial transport.

---

### B-306 - Seq classifier equivalent to pointwise classifier

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | Seq classifier equivalent to pointwise classifier |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 10/10 |
| Novelty | 9/10 |

Problem:
Under Seq↑(A), two sequences f, g are Seq-classified equal iff for every Nat↑ index n, f(n) ∼A g(n).

Local inputs:
- `papers/bedc/parts/concrete_instances/122_seq_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/28_nat_namecert_construction.tex`
- `papers/bedc/parts/core/08_typed_naming_certificates.tex`

Rationale:
Chapter 122 introduces Seq↑ as Nat↑→A naming-certificate functions with regularity/boundedness moduli, used as the substrate for Series↑ and ConvRad↑, but no theorem makes the Seq classifier exactly pointwise. This is the canonical representation theorem for Seq↑ and a prerequisite for downstream series and analytic-limit certificates, orthogonal to B-12 (continuous modulus composition) and B-15 (Bishop real limit transport).

---

### B-307 - Series partial sums respect Seq equality

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | Series partial sums respect Seq equality |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 7/10 |

Problem:
Under Series↑ over an additive carrier, if term sequences f, g are pointwise ∼A equal then their certified partial-sum sequences are pointwise classifier-equal and induce the same Series↑ classifier.

Local inputs:
- `papers/bedc/parts/concrete_instances/123_series_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/122_seq_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/05_add_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/28_nat_namecert_construction.tex`

Rationale:
Chapter 123 presents Series↑ as NameCertSeq↑ plus partial-sum sequence with explicit convergence moduli, but no theorem packages the finite-induction step that term-level Seq equality lifts to partial-sum equality and Series↑ classifier equality. This is the functoriality of the Series construction over its underlying sequence classifier and a prerequisite for convergence-modulus soundness work; it does not duplicate polynomial-normalization or FPS-Cauchy-product targets on the BOARD.

---

### B-308 - QuotientRing zero coset classification

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | QuotientRing zero coset classification |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 10/10 |
| Novelty | 8/10 |

Problem:
Under Ring↑ and Ideal↑ setup, a ≡I 0R if and only if a is R-carried and I(a) holds.

Local inputs:
- `papers/bedc/parts/concrete_instances/85_quotientring_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/83_ideal_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/42_ring_namecert_construction.tex`

Rationale:
QuotientRing↑ chapter already lifts addition and multiplication descent to ideal cosets but does not isolate the zero-coset classification as a theorem. This is the natural classifier counterpart to the descent theorems and a direct prerequisite for ModN-style zero classification. The proof unfolds a ≡I 0R using a − 0R ∼R a and the ideal classifier transport, so it is short and does not invoke any new structure beyond existing Ring↑ and Ideal↑ fields. No BOARD entry covers ideal-coset zero classification, and no paper label matches.

---

### B-309 - ModN as the nZ quotient certificate

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | ModN as the nZ quotient certificate |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 10/10 |
| Novelty | 8/10 |

Problem:
Under Int↑ and positive n : Nat↑, if nZ is certified as an Int↑ ideal, then QuotientRing↑(Int↑, nZ) yields a ModN↑ NameCert with the same classifier.

Local inputs:
- `papers/bedc/parts/concrete_instances/104_modn_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/85_quotientring_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/83_ideal_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/30_int_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/28_nat_namecert_construction.tex`

Rationale:
ModN↑ chapter currently asserts in prose that ModN is the canonical QuotientRing↑ instance over nZ but does not provide a theorem specializing the QuotientRing certificate to the ModN certificate. This bridge theorem upgrades a header-level interface to a scannable certificate target and unblocks downstream formalization that wants to reuse ModN classifier laws. It is distinct from quotient-ring descent theorems already on the books because it is the specialization step, not the closure step.

---

### B-310 - HoloOnDisk subdisk restriction

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | HoloOnDisk subdisk restriction |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 7/10 |

Problem:
Under Holo↑ seed setup, HoloOnDisk(f, z0, r) and a certified r' ≤ r imply HoloOnDisk(f, z0, r') with a compatible classifier and ledger witness.

Local inputs:
- `papers/bedc/parts/concrete_instances/67_holomorphic_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/79_complex_topology_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/78_complex_analytic_namecert_construction.tex`

Rationale:
Holo↑ chapter is currently Seed and lists composition image-containment and identity-on-smaller-disk obligations but provides no theorem that the holomorphic carrier restricts to a smaller concentric disk. This monotonicity is a structural prerequisite for both closure obligations and any disk-shrinking identity argument. The proof mostly uses OpenDisk gap and refinement infrastructure already present in CplxTopo↑ plus existing hsame transport, so it sits cleanly inside the BEDC certificate scope without invoking external complex analysis.

---

### B-311 - HoloOnDisk additive closure

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | HoloOnDisk additive closure |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 7/10 |

Problem:
Under Holo↑ seed setup, HoloOnDisk(f, z0, r) and HoloOnDisk(g, z0, r) with compatible uniform-modulus witnesses imply HoloOnDisk(f + g, z0, r).

Local inputs:
- `papers/bedc/parts/concrete_instances/67_holomorphic_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/38_complex_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/78_complex_analytic_namecert_construction.tex`

Rationale:
Holo↑ core obligations explicitly list sum, product, and composition closure but the existing PDF-side Holo theorems concentrate on open-disk boundary and iterated differentiability readback, not additive closure. Additive closure is the smallest of the three closure theorems and a natural sibling of the product and composition closure targets, with a self-contained proof using complex pointwise sum and modulus pasting plus hsame-stable ledger composition. No BOARD entry currently covers this closure direction.

---

### B-312 - Holo dense-sequence identity classifier

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | Holo dense-sequence identity classifier |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 9/10 |

Problem:
Under Holo↑ seed setup, if f and g are holomorphic on the same disk and classifier-equal on a certified quantitatively dense sequence, then f and g are identified by the Holo classifier on any certified smaller disk.

Local inputs:
- `papers/bedc/parts/concrete_instances/67_holomorphic_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/79_complex_topology_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/74_analytic_continuation_namecert_construction.tex`

Rationale:
Holo↑ obligations explicitly list a dense-sequence identity obligation but currently leave it as a Seed field rather than a paper theorem. The proposed claim is the BEDC certificate counterpart of the classical identity theorem, expressed entirely through CplxTopo↑ DomCompat and density witnesses already certified in the chapter. It is the highest-leverage upgrade from Holo seed status to scannable certificate, and it is genuinely new relative to the BOARD which contains no analogous identity-classifier targets. Complexity is real but bounded by the existing density and DomCompat scaffolding.

---

### B-313 - LFunction finite zero-tail stability

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | LFunction finite zero-tail stability |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 7/10 |

Problem:
Under LFunction↑ Dirichlet partial-sum setup, DirichletPartSum(term, s, n, S) together with term(i, s) ∼ e for all i in [n, n+k) implies DirichletPartSum(term, s, n + k, S).

Local inputs:
- `papers/bedc/parts/concrete_instances/105_lfunction_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/69_dirichlet_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/68_complex_series_namecert_construction.tex`

Rationale:
LFunction↑ already proves successor positivity, previous uniqueness, successor determinacy, and one-step zero-term stability, but lacks the multi-step finite-fold version. The proposed theorem is the natural Nat-induction extension of the one-step theorem and is needed for any later truncation argument on Dirichlet partial sums. It stays strictly inside BEDC certificate framework about partial-sum stability and does not introduce analytic L-function content. Short complexity, clear induction skeleton, no BOARD overlap.

---

### B-314 - HoloOnDisk nested subdisk functoriality

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (codex) |
| Object | HoloOnDisk nested subdisk functoriality |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
Under HolomorphicUp, given Subradius(r2,r1;e1) and Subradius(r1,r0;e0) over a HoloOnDisk(f,z0,r0) parent witness, the iterated subdisk witness W↾e1∘(W↾e0) is classifier-equivalent to the direct subdisk witness W↾(e0·e1) of HoloOnDisk(f,z0,r2) along the composed ledger.

Local inputs:
- `papers/bedc/parts/concrete_instances/55_complex_topology_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/43_holomorphic_namecert_construction.tex`

Rationale:
This is the natural functoriality completion of the two existing items in 55_complex_topology_namecert_construction.tex: lem:holo-certified-subdisk-radius-compose composes Subradius witnesses at the LEDGER level only, and thm:holo-on-disk-subdisk-restriction restricts along a SINGLE Subradius. Neither states that two successive HoloOnDisk restrictions yield the classifier-equivalent witness as one direct restriction along the composed ledger e0·e1. This functoriality square is a concrete coherence theorem on the modulus ledger δ_r2(k,g'')=δ_r1(k,g''·e1)=δ_r0(k,g''·e1·e0)=δ_r0(k,g''·(e0·e1)) and on the inherited stability/classifier fields. It is distinct from B-10 (interval nested bounds, different carrier), B-11 (categorical functor composition over hom-carriers), and B-29 (lattice bound uniqueness). It does not duplicate any \label{*:holo-*} or \label{*:cplx-topo-*} entry in the paper. Landing in 55_complex_topology_namecert_construction.tex (415 lines) is safe and natural — the proof reuses lem:holo-certified-subdisk-radius-compose plus the parent restriction theorem twice. Risk: medium (witness-level coherence over already-proven ledger-level coherence).

---

### B-315 - LinearMap pointwise classifier equivalence

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | LinearMap pointwise classifier equivalence |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |

Problem:
If the codomain classifier is supplied by a NameCert and the LinearMap classifier is the pointwise codomain comparison, then the LinearMap classifier is reflexive, symmetric, and transitive under the LinearMapUp setup.

Local inputs:
- `papers/bedc/parts/concrete_instances/linearmap/the_certificate.tex`
- `papers/bedc/parts/core/08_typed_naming_certificates.tex`
- `lean4/BEDC/Derived/LinearMapUp.lean`

Rationale:
The pointwise classifier is defined at papers/bedc/parts/concrete_instances/linearmap/the_certificate.tex:13-16, and the stability list explicitly names pointwise reflexivity and transitivity at lines 18-28 but has no standalone theorem packaging the full equivalence, especially symmetry. The core NameCert fields needed for the proof are at papers/bedc/parts/core/08_typed_naming_certificates.tex:49-52. Focused rg for linearmap pointwise classifier reflexivity/symmetry/transitivity/equivalence returned only the definition/stability text and incidental use sites, with no matching theorem/lemma/proposition label. The landing file is 58 lines, so it is safely below the line cap.

---

### B-316 - FinSet duplicate insertion invariance

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | FinSet duplicate insertion invariance |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 9/10 |

Problem:
If a new finite-spine entry is carried by the SetUp source and classifier-equal to an entry already occurring in xs, then adding that entry to xs leaves FinSetEnumClassifier unchanged.

Local inputs:
- `papers/bedc/parts/concrete_instances/90_finset_namecert_construction.tex`
- `papers/bedc/parts/core/08_typed_naming_certificates.tex`

Rationale:
FinSetEnumClassifier is extensional membership equivalence over EnumMem at papers/bedc/parts/concrete_instances/90_finset_namecert_construction.tex:12-30, while finite-spine occurrence is generated by cons/tail clauses at lines 99-101. The existing theorem at lines 49-60 proves invariance under classifier-preserving permutations only; it does not cover multiplicity collapse. Focused rg for finset/enumeration duplicate, idempotence, insertion, and multiplicity returned 0 hits, so no labeled theorem appears to state this duplicate-insensitivity property.

---

### B-317 - EnumPerm transitivity by bijection composition

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | EnumPerm transitivity by bijection composition |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
If EnumPerm(xs, ys) and EnumPerm(ys, zs) hold under the same SetUp carrier and classifier, then EnumPerm(xs, zs) holds by composing the certified finite-position bijections.

Local inputs:
- `papers/bedc/parts/concrete_instances/90_finset_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/94_permutation_namecert_construction.tex`
- `papers/bedc/parts/core/08_typed_naming_certificates.tex`

Rationale:
EnumPerm is defined with a certified position bijection and pointwise classifier-preservation at papers/bedc/parts/concrete_instances/90_finset_namecert_construction.tex:33-47; the inverse map is recorded at line 46, but no composition law is stated. The only theorem using EnumPerm is classifier invariance at lines 49-60. Focused rg for EnumPerm or enumeration permutation plus refl/sym/trans returned no theorem label beyond the definition and that invariance theorem, making transitivity a concrete closure gap rather than a hidden duplicate.

---

### B-318 - Subtype restricted classifier NameCert

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Subtype restricted classifier NameCert |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
If a parent SetUp carrier has a NameCert and P is stable under the parent classifier, then the restricted classifier on S_P forms a NameCert on the subtype carrier.

Local inputs:
- `papers/bedc/parts/concrete_instances/91_subtype_namecert_construction.tex`
- `papers/bedc/parts/core/08_typed_naming_certificates.tex`

Rationale:
The subtype carrier and restricted classifier are defined at papers/bedc/parts/concrete_instances/91_subtype_namecert_construction.tex:12-29. The existing theorem at lines 31-55 only proves reflection/equivalence with the parent comparison for already formed subtype endpoints; it does not package inhabitedness, restricted reflexivity/symmetry/transitivity, or carrier transport as a NameCert. Core NameCert fields are available at papers/bedc/parts/core/08_typed_naming_certificates.tex:49-52. Focused rg for subtype restricted classifier NameCert/equivalence/transport found no subtype theorem beyond the reflection theorem; analogous restricted-classifier results in other chapters do not cover SubtypeUp.

---

### B-319 - Totally bounded net tolerance weakening

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Totally bounded net tolerance weakening |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 9/10 |

Problem:
If TotallyBoundedProbeBundleNet(X, eps, P, net) holds and RatUp supplies eps <= epsPrime, then the same ProbeBundle data forms a TotallyBoundedProbeBundleNet(X, epsPrime, P, netPrime).

Local inputs:
- `papers/bedc/parts/concrete_instances/105_totallybounded_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/32_metric_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/12_rat_namecert_construction.tex`
- `lean4/BEDC/Derived/TotallyBoundedUp.lean`

Rationale:
The ProbeBundle net carrier stores coverage bounds d_p <= eps at papers/bedc/parts/concrete_instances/105_totallybounded_namecert_construction.tex:75-99, especially lines 91-94. The existing stability theorem at lines 102-116 transports equivalent tolerance and ledger histories by hsame/RatUp classifier data; it does not weaken along an order comparison eps <= epsPrime. Focused rg for totallybounded monotonicity, tolerance weakening, larger tolerance, and ProbeBundleNet weakening returned 0 hits, so this concrete monotonicity theorem is open.

---

### B-320 - CompleteMetric limit witness uniqueness

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | CompleteMetric limit witness uniqueness |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 9/10 |

Problem:
If two CompleteMetricLimitWitness packages converge the same regular Cauchy stream in a separated MetricSpaceUp carrier with the triangle and zero-distance exactness fields, then their limit histories are point-classifier equal.

Local inputs:
- `papers/bedc/parts/concrete_instances/106_completemetric_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/32_metric_namecert_construction.tex`

Rationale:
CompleteMetricLimitWitness is defined at papers/bedc/parts/concrete_instances/106_completemetric_namecert_construction.tex:31-59. The singleton theorem at lines 64-99 proves uniqueness only inside the singleton carrier, and the general theorem at lines 101-119 proves transport stability, not uniqueness. MetricSpaceUp lists identity-of-indiscernibles and triangle obligations at papers/bedc/parts/concrete_instances/32_metric_namecert_construction.tex:4 and line 37, with empty-distance exactness at lines 43-62. Focused rg for CompleteMetricLimitWitness uniqueness or complete metric limit uniqueness found no general theorem; broader limit-uniqueness hits are in ComplexLimit, Real capstone, or the singleton case, so this gap is genuine.

---

### B-321 - Matrix transpose double-readback involution

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | Matrix transpose double-readback involution |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
Under a certified scalar RingUp and MatrixUp carrier, if X is a carried n by m matrix, then (X^T)^T is carried as an n by m matrix and pointwise matrix-classifier equal to X.

Local inputs:
- `papers/bedc/parts/concrete_instances/matrix/finite_fold_multiplication_transpose.tex`
- `papers/bedc/parts/concrete_instances/matrix/carrier_definition.tex`
- `papers/bedc/parts/concrete_instances/matrix/the_certificate.tex`

Rationale:
This is a concrete closure/readback theorem for an already-defined matrix operation and is not covered by the current BOARD or paper labels. It lands in the matrix concrete-instance subtree, has a narrow implication form, and should be a useful companion to the existing transpose product-reversal surface without duplicating it.

---

### B-322 - FinSet enumeration classifier transitivity

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | FinSet enumeration classifier transitivity |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
Under a fixed SetUp NameCert on A, if FinSetEnumClassifier(xs,ys) and FinSetEnumClassifier(ys,zs), then FinSetEnumClassifier(xs,zs).

Local inputs:
- `papers/bedc/parts/concrete_instances/90_finset_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/11_list_namecert_construction.tex`
- `papers/bedc/parts/core/08_typed_naming_certificates.tex`

Rationale:
The claim is a precise classifier-closure property for the finite-set enumeration classifier and is not already represented by the existing permutation-invariance definition label. It belongs in the FinSet concrete-instance chapter and supplies a basic relation law needed by the public classifier surface.

---

### B-323 - Enumeration permutation composition closure

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | Enumeration permutation composition closure |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
Under a fixed SetUp NameCert on A, if EnumPerm(xs,ys) and EnumPerm(ys,zs), then EnumPerm(xs,zs).

Local inputs:
- `papers/bedc/parts/concrete_instances/90_finset_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/94_permutation_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/95_symgroup_namecert_construction.tex`

Rationale:
This is a concrete composition-closure theorem for the EnumPerm carrier relation, distinct from classifier preservation under one enumeration permutation and not duplicated by existing BOARD entries. It directly supports the permutation and symmetric-group concrete-instance surface with a focused construction target.

---

### B-324 - CatColimit cocone morphism prewhiskering descent

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | CatColimit cocone morphism prewhiskering descent |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
Given a certified NatTrans beta:E=>D and D-cocones kappa,mu pulled back to E-cocones by precomposing each leg with beta, if CoconeMor_D(kappa,mu;f), then CoconeMor_E(kappa^beta,mu^beta;f).

Local inputs:
- `papers/bedc/parts/concrete_instances/84_catcolimit_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/83_catlimit_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/38_nattrans_namecert_carrier.tex`
- `papers/bedc/parts/concrete_instances/36_category_namecert_construction.tex`

Rationale:
This is a specific bridge theorem for CatColimit cocone morphisms under diagram prewhiskering, not a marker or abstract source-equivalence restatement. It is parallel to known CatLimit coverage but absent on the colimit side, so it fills a concrete asymmetric gap without duplicating the existing comparison-fiber collapse corollary.

---

### B-325 - Residue pole data result determinism

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | Residue pole data result determinism |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |

Problem:
If two ResiduePoleData witnesses share z0,r,p,g,I,rho and have function histories f and f', then f is hsame to f'.

Local inputs:
- `papers/bedc/parts/concrete_instances/103_residue_namecert_construction.tex`
- `papers/bedc/parts/core/03_relational_extension_and_continuation.tex`

Rationale:
The candidate is a narrow determinacy result for a concrete carrier witness and is not matched by the supplied paper labels or existing BOARD targets. It belongs to the residue concrete-instance chapter and records a reusable endpoint consequence of shared continuation data rather than merely rephrasing an abstract classifier equivalence.

---

### B-326 - Matrix addition commutativity

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Matrix addition commutativity |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 6/10 |

Problem:
Under a MatrixUp carrier over a scalar RingUp source, if A and B are carried matrices of the same dimensions and matrix addition is pointwise, then A + B is matrix-classified with B + A.

Local inputs:
- `papers/bedc/parts/concrete_instances/24_matrix_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/matrix/the_certificate.tex`
- `papers/bedc/parts/concrete_instances/matrix/finite_fold_multiplication_laws_distributivity_transpose.tex`
- `lean4/BEDC/Derived/MatrixUp.lean`

Rationale:
This belongs in the matrix concrete-instance chapter as a first linear-algebra theorem: pointwise matrix addition is commutative because scalar addition is commutative. Evidence for the needed objects is present: MatrixUp is introduced with pointwise classifier and derived addition at papers/bedc/parts/concrete_instances/24_matrix_namecert_construction.tex:4, the classifier is defined at papers/bedc/parts/concrete_instances/matrix/the_certificate.tex:14, and existing distributivity theorems already assume pointwise matrix addition at papers/bedc/parts/concrete_instances/matrix/finite_fold_multiplication_laws_distributivity_transpose.tex:41. Focused grep found no theorem label for matrix addition commutativity; the proof is entrywise and should close in one round.

---

### B-327 - Matrix addition associativity

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Matrix addition associativity |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 6/10 |

Problem:
Under a MatrixUp carrier over a scalar RingUp source, if A, B, and C are carried same-shaped matrices and matrix addition is pointwise, then (A + B) + C is matrix-classified with A + (B + C).

Local inputs:
- `papers/bedc/parts/concrete_instances/24_matrix_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/matrix/the_certificate.tex`
- `papers/bedc/parts/concrete_instances/matrix/finite_fold_multiplication_laws_distributivity_transpose.tex`
- `lean4/BEDC/Derived/MatrixUp.lean`

Rationale:
This is a standard first theorem in any linear-algebra text after defining matrix addition. The chapter has the pointwise classifier and addition closure rows at papers/bedc/parts/concrete_instances/matrix/the_certificate.tex:14 and :51, and multiplication distributivity already uses pointwise addition at papers/bedc/parts/concrete_instances/matrix/finite_fold_multiplication_laws_distributivity_transpose.tex:41. There is no matching theorem label for matrix addition associativity. The proof is a pointwise application of scalar additive associativity, so it is a small stepping-stone rather than a matrix-algebra headline.

---

### B-328 - Zero matrix is additive identity

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Zero matrix is additive identity |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 7/10 |

Problem:
Under a MatrixUp carrier over a scalar RingUp source, if A is a carried n by m matrix and Z is the finite-fold zero matrix datum, then A + Z and Z + A are matrix-classified with A.

Local inputs:
- `papers/bedc/parts/concrete_instances/24_matrix_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/matrix/the_certificate.tex`
- `papers/bedc/parts/concrete_instances/matrix/finite_fold_zero_matrix_absorption.tex`
- `papers/bedc/parts/concrete_instances/ring/18_ring_certificate_and_additive_laws.tex`
- `lean4/BEDC/Derived/MatrixUp.lean`

Rationale:
This is the textbook additive-identity law for matrices. The zero matrix datum exists at papers/bedc/parts/concrete_instances/matrix/finite_fold_zero_matrix_absorption.tex:2, but the only theorem there is zero multiplication at :13, not additive identity. Matrix addition is already a derived pointwise operation from papers/bedc/parts/concrete_instances/24_matrix_namecert_construction.tex:4. The proof is entrywise using scalar left/right zero laws, with no missing infrastructure.

---

### B-329 - Zero linear map certificate

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Zero linear map certificate |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 10/10 |
| Novelty | 7/10 |

Problem:
Under ModuleUp certificates for M and N over the same scalar RingUp source, if z maps every carried element of M to 0_N, then z satisfies LinearMapCert_R(M,N;z).

Local inputs:
- `papers/bedc/parts/concrete_instances/23_linearmap_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/linearmap/the_certificate.tex`
- `papers/bedc/parts/concrete_instances/linearmap/module_linearmap_certificates.tex`
- `papers/bedc/parts/concrete_instances/module/21_module_namecert_construction_core.tex`
- `lean4/BEDC/Derived/LinearMapUp.lean`

Rationale:
This is the standard zero homomorphism theorem from an introductory module or linear algebra text. LinearMapUp is defined as additivity plus scalar compatibility at papers/bedc/parts/concrete_instances/23_linearmap_namecert_construction.tex:4, the certificate package is present at papers/bedc/parts/concrete_instances/linearmap/module_linearmap_certificates.tex:99, and module zero-action annihilation already exists at papers/bedc/parts/concrete_instances/module/21_module_namecert_construction_core.tex:654. Grep found no zero-map certificate theorem. It lands naturally in module_linearmap_certificates.tex, which is below the line cap.

---

### B-330 - LinearMap pointwise sum commutativity

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | LinearMap pointwise sum commutativity |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 6/10 |

Problem:
Under common ModuleUp source and target certificates, if f and g satisfy LinearMapCert_R(M,N), then the pointwise sum f + g is LinearMap-classified with g + f.

Local inputs:
- `papers/bedc/parts/concrete_instances/23_linearmap_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/linearmap/the_certificate.tex`
- `papers/bedc/parts/concrete_instances/linearmap/module_linearmap_certificates.tex`
- `lean4/BEDC/Derived/LinearMapUp.lean`

Rationale:
This is the first additive law for Hom_R(M,N), standard in module theory. The pointwise sum certificate is already proved at papers/bedc/parts/concrete_instances/linearmap/module_linearmap_certificates.tex:341, and the pointwise classifier is defined at papers/bedc/parts/concrete_instances/linearmap/the_certificate.tex:14. Focused grep found no commutativity theorem for linearmap pointwise addition. The proof is pointwise target-module additive commutativity.

---

### B-331 - FPS pointwise addition associativity

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | FPS pointwise addition associativity |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 6/10 |

Problem:
Under a FormalPowerSeriesUp carrier over a scalar RingUp source, if F, G, and H are carried coefficient sequences, then (F + G) + H is FPS-classified with F + (G + H).

Local inputs:
- `papers/bedc/parts/concrete_instances/26_fps_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/ring/18_ring_certificate_and_additive_laws.tex`
- `lean4/BEDC/Derived/FpsUp.lean`

Rationale:
This is a standard formal-power-series ring law, smaller than product identity or distributivity. The FPS pointwise addition coefficient rule is defined at papers/bedc/parts/concrete_instances/26_fps_namecert_construction.tex:384, and FPS addition commutativity is already proved at :394, so the needed pointwise infrastructure exists. Grep found no FPS addition associativity theorem. The proof is coefficientwise scalar additive associativity followed by the FPS pointwise classifier.

---

### B-332 - Topology finite-intersection closure from indexed opens

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Topology finite-intersection closure from indexed opens |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 9/10 |

Problem:
If a TopologyUp carrier supplies indexed open-set witnesses and two opens U and V are carried by those witnesses, then the finite-intersection witness carries U ∩ V as an open and transports membership under the carrier classifier.

Local inputs:
- `papers/bedc/parts/concrete_instances/66_topology_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/55_complex_topology_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/32_metric_namecert_construction.tex`

Rationale:
The generic topology chapter is still only a skeleton: papers/bedc/parts/concrete_instances/66_topology_namecert_construction.tex:4 says TopologyUp packages open subsets closed under finite intersections and arbitrary unions, but the file has no companion theorem body. The closest developed content is specialized ComplexTopologyUp, where generated open disks, finite intersection, and arbitrary union are proved at papers/bedc/parts/concrete_instances/55_complex_topology_namecert_construction.tex:285-307. BOARD coverage around tools/bedc-deep/BOARD.md:8066 and tools/bedc-deep/BOARD.md:8173 is complex/HoloOnDisk-specific rather than the generic TopologyUp closure step.

---

### B-333 - Norm-induced metric certificate

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Norm-induced metric certificate |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 9/10 |

Problem:
If a NormUp vector-space carrier has subtraction, norm non-negativity, positive definiteness, symmetry of subtraction, triangle inequality, and classifier congruence, then d(x,y)=norm(x-y) satisfies the MetricSpaceUp distance obligations.

Local inputs:
- `papers/bedc/parts/concrete_instances/67_norm_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/68_banach_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/32_metric_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/22_vecspace_namecert_construction.tex`

Rationale:
NormUp is under-represented: papers/bedc/parts/concrete_instances/67_norm_namecert_construction.tex:4 lists positive definiteness, absolute homogeneity, and triangle inequality, while BanachUp explicitly depends on the metric induced by the norm at papers/bedc/parts/concrete_instances/68_banach_namecert_construction.tex:4. The target is a missing middle step to MetricSpaceUp, whose required obligations are enumerated at papers/bedc/parts/concrete_instances/32_metric_namecert_construction.tex:30-38. Existing metric BOARD work focuses on ball budgets and compactness-style behavior, not on deriving the metric certificate from NormUp.

---

### B-334 - Measure empty-set zero from sigma-additivity

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Measure empty-set zero from sigma-additivity |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 9/10 |

Problem:
If a MeasureUp carrier has sigma-additivity on a designated sigma-algebra and the empty set is measurable, then the measure of the empty set is RealUp-classified as zero.

Local inputs:
- `papers/bedc/parts/concrete_instances/70_measure_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/101_integral_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/17_abgroup_namecert_construction.tex`

Rationale:
MeasureUp appears as a definition-only substrate: papers/bedc/parts/concrete_instances/70_measure_namecert_construction.tex:4 says it packages a constructive sigma-additive non-negative real-valued set function, and IntegralUp depends on MeasureUp at papers/bedc/parts/concrete_instances/101_integral_namecert_construction.tex:4. BOARD contour-integral work such as tools/bedc-deep/BOARD.md:5628-5648 covers ContourUp operation closure, but not the generic MeasureUp sanity theorem that sigma-additivity forces the empty set to have zero measure. This is a small concrete implication with a clear algebraic cancellation dependency rather than a survey of measure theory.

---

### B-335 - Topology arbitrary-union closure from indexed families

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (codex) |
| Object | Topology arbitrary-union closure from indexed families |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 7/10 |

Problem:
Under an indexed TopologyUp carrier with a supplied union index for a family of open indices carrying predicates U_a, pointwise carriedness implies the union index carries the predicate x | exists a, U_a(x), and that union membership transports under the carrier classifier.

Local inputs:
- `papers/bedc/parts/concrete_instances/66_topology_namecert_construction.tex`

Rationale:
This fills a direct gap in the generic TopologyUp surface: the topology chapter states closure under arbitrary unions but currently only exposes and proves finite-intersection closure. The existing complex-topology union theorem is a concrete instance, not the generic indexed TopologyUp closure law, so this deserves its own target slot.

---

### B-336 - Metric balls instantiate indexed TopologyUp opens

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (codex) |
| Object | Metric balls instantiate indexed TopologyUp opens |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
Under a MetricSpaceUp carrier with explicit positive-radius ball witnesses, each metric ball predicate supplies a TopologyUp open index carrying that ball and transporting membership under the metric carrier classifier.

Local inputs:
- `papers/bedc/parts/concrete_instances/32_metric_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/66_topology_namecert_construction.tex`

Rationale:
This is a concrete bridge between the metric and topology certificate layers, matching the paper surface where TopologyUp is described as generalising MetricSpaceUp. It is not just a verification marker or source-equivalence restatement; it would add a reusable open-ball construction needed by later topological instances.

---

### B-337 - Measure finite disjoint-union additivity

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Measure finite disjoint-union additivity |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
If A and B are disjoint measurable subsets in a MeasureUp carrier whose certificate supplies sigma-additivity and countable-sum head-tail readback, then μ(A ∪ B) is RealUp-classified with μ(A) + μ(B).

Local inputs:
- `papers/bedc/parts/concrete_instances/70_measure_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/101_integral_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/17_abgroup_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/16_group_namecert_construction.tex`

Rationale:
MeasureUp is still very lightly populated: papers/bedc/parts/concrete_instances/70_measure_namecert_construction.tex:4 states only the sigma-additive nonnegative real-valued measure interface, and the current theorem at 70_measure_namecert_construction.tex:12-18 proves only the empty-set consequence. IntegralUp immediately depends on this layer at papers/bedc/parts/concrete_instances/101_integral_namecert_construction.tex:4. Focused grep for finite additivity, disjoint union, and measure-union found no labeled theorem beyond the empty-set proof and BOARD B-334 at tools/bedc-deep/BOARD.md:8714-8736. The proposed theorem is the next concrete implication from the same certificate data: specialize sigma-additivity to the sequence A, B, empty, empty, ... and use the existing empty-set-zero theorem plus RealUp additive-group cancellation/readback.

---

### B-338 - Totally bounded subcarrier inherits the same net

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Totally bounded subcarrier inherits the same net |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 7/10 |

Problem:
Under the TotallyBoundedProbeBundleNet setup, if Y is a classifier-stable subcarrier of X and X has an epsilon-net bundle P at tolerance epsilon, then restricting the coverage rows to Y makes the same P an epsilon-net for Y.

Local inputs:
- `papers/bedc/parts/concrete_instances/105_totallybounded_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/32_metric_namecert_construction.tex`

Rationale:
Belongs in concrete_instances/105_totallybounded_namecert_construction.tex. This is the standard metric-space theorem that every subset of a totally bounded set is totally bounded. The chapter defines TotallyBoundedProbeBundleNet at papers/bedc/parts/concrete_instances/105_totallybounded_namecert_construction.tex:75 and proves coverage stability and tolerance weakening at lines 102 and 183, but focused search found no subset/subcarrier theorem. It closes in 1 round: for y in Y, use the inclusion Y -> X, apply the existing X coverage row, and reuse the same probe bundle.

---

### B-339 - Finite union of totally bounded ProbeBundle nets

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Finite union of totally bounded ProbeBundle nets |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
If X and Y each carry a TotallyBoundedProbeBundleNet at the same tolerance epsilon, then the union carrier X union Y carries a TotallyBoundedProbeBundleNet whose probe bundle is bundleAppend of the two nets.

Local inputs:
- `papers/bedc/parts/concrete_instances/105_totallybounded_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/32_metric_namecert_construction.tex`
- `lean4/BEDC/FKernel/Bundle.lean`

Rationale:
Belongs in concrete_instances/105_totallybounded_namecert_construction.tex. Finite unions of totally bounded metric subspaces are a standard introductory metric theorem. The net object is already explicit at papers/bedc/parts/concrete_instances/105_totallybounded_namecert_construction.tex:75, and the Lean bundle side already has bundleAppend and append membership support in lean4/BEDC/FKernel/Bundle.lean:12 and lean4/BEDC/FKernel/Bundle.lean:174. Focused search found no totally bounded union theorem. It closes in 1-3 rounds by case-splitting on union membership and injecting the selected center through the left or right side of bundleAppend.

---

### B-340 - Finite-spine concatenation enumerates finite-set union

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Finite-spine concatenation enumerates finite-set union |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
If finite spines xs and ys enumerate finite predicates U and V over the same SetUp classifier, then the concatenated spine enumerates the union predicate z such that U(z) or V(z).

Local inputs:
- `papers/bedc/parts/concrete_instances/90_finset_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/11_list_namecert_construction.tex`

Rationale:
Belongs in concrete_instances/90_finset_namecert_construction.tex. Closure of finite sets under union is a first textbook theorem about finite sets. The chapter introduces enumeration membership at papers/bedc/parts/concrete_instances/90_finset_namecert_construction.tex:12 and the FinSet enumeration carrier at line 104, then proves duplicate and permutation invariance at lines 150 and 192, but focused search found no union or concatenation enumeration theorem. It should close in 1-3 rounds from the existing finite-spine and ListUp infrastructure by the usual append-membership split.

---

### B-341 - CatColimit transport along pointwise diagram equivalence

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | CatColimit transport along pointwise diagram equivalence |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
If D and E are pointwise certified equivalent diagrams and ColimCocone_D(K,kappa) holds, then the E-cocone obtained by composing each E-leg through the inverse component is ColimCocone_E(K,kappa^E) under the CategoryUp/FunctorUp/NatTransUp setup.

Local inputs:
- `papers/bedc/parts/concrete_instances/84_catcolimit_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/83_catlimit_namecert_construction.tex`

Rationale:
CatColimit has the needed local definitions: fixed-diagram cocone comparison data at papers/bedc/parts/concrete_instances/84_catcolimit_namecert_construction.tex:12 and ColimCocone couniversality at 84:27-31, plus cocone morphism descent through natural-transformation prewhiskering at 84:226-244. The dual CatLimit chapter already defines pointwise certified diagram equivalence at papers/bedc/parts/concrete_instances/83_catlimit_namecert_construction.tex:176-194 and proves CatLimit transport at 83:197-210, so the missing dual theorem is sharply delimited. Focused grep for `CatColimit transport|pointwise certified diagram equivalence|ColimCocone_{E}|transport.*colimit` in the CatColimit file returned 0 hits; theorem inventory in that file has only labels at 84:34, 84:90, 84:108, 84:133, and 84:226, none a pointwise-diagram transport theorem. Marker grep for Lean status macros in the CatColimit file returned 0 hits, and the target file is 283 lines.

---

### B-342 - CatColimit cocone comparison-fiber collapse

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | CatColimit cocone comparison-fiber collapse |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
If ColimCocone_D(C,kappa) holds and u1,u2:C->C' both satisfy CoconeMor_D(kappa,kappa';-), then MorEq_C(C,C';u1,u2) under the fixed certified diagram setup.

Local inputs:
- `papers/bedc/parts/concrete_instances/84_catcolimit_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/83_catlimit_namecert_construction.tex`

Rationale:
The CatColimit definition explicitly includes the uniqueness field: any two morphisms out of a colimiting cocone into the same target cocone are classified by MorEq_C at papers/bedc/parts/concrete_instances/84_catcolimit_namecert_construction.tex:27-31. The file proves endomorphism rigidity at 84:108-129 and vertex co-uniqueness at 84:133-174, but it does not extract the arbitrary comparison-fiber corollary. The dual CatLimit file already has exactly this extraction as Comparison-fiber collapse at papers/bedc/parts/concrete_instances/83_catlimit_namecert_construction.tex:134-153. Focused grep for `comparison-fiber|fiber collapse|CoconeMor_D.*u_1|CoconeMor_D.*u_2` in the CatColimit file found no labelled theorem or corollary; the only relevant uniqueness evidence is the definition line 84:31.

---

### B-343 - EnumPerm inverse symmetry

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | EnumPerm inverse symmetry |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
If EnumPerm_{A,sim_A}(xs,ys) holds under NameCert(A,sim_A), then EnumPerm_{A,sim_A}(ys,xs) holds using the certified inverse finite-position bijection and classifier symmetry.

Local inputs:
- `papers/bedc/parts/concrete_instances/90_finset_namecert_construction.tex`
- `papers/bedc/parts/core/08_typed_naming_certificates.tex`

Rationale:
EnumPerm is defined as a classifier-preserving finite-position bijection at papers/bedc/parts/concrete_instances/90_finset_namecert_construction.tex:33-46, and line 90:46 states that the inverse position map is part of the certified bijection. Existing positive coverage proves only classifier invariance under an EnumPerm at 90:49-59 and EnumPerm transitivity at 90:192-240. The NameCert core supplies classifier symmetry at papers/bedc/parts/core/08_typed_naming_certificates.tex:49-52. Focused grep for `EnumPerm.*sym|symmetry.*EnumPerm|EnumPerm.*inverse|inverse.*EnumPerm|EnumPerm.*reflex|identity.*EnumPerm` in the FinSet file returned 0 hits; Lean marker grep in that file returned only the unrelated marker at 90:122 for FinsetEnumerationBundle_member_source_carried.

---

### B-344 - EnumPerm identity closure

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | EnumPerm identity closure |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |

Problem:
If every entry of a finite spine xs is carried by A under NameCert(A,sim_A), then EnumPerm_{A,sim_A}(xs,xs) holds by the identity finite-position bijection and classifier reflexivity.

Local inputs:
- `papers/bedc/parts/concrete_instances/90_finset_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/94_permutation_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/95_symgroup_namecert_construction.tex`
- `papers/bedc/parts/core/08_typed_naming_certificates.tex`

Rationale:
The EnumPerm definition at papers/bedc/parts/concrete_instances/90_finset_namecert_construction.tex:33-46 is the finite-enumeration datum later used by PermutationUp, and 90:46 explicitly links it to the permutation interface; papers/bedc/parts/concrete_instances/94_permutation_namecert_construction.tex:4 says PermutationUp packages bijections of FinSetUp onto itself, while papers/bedc/parts/concrete_instances/95_symgroup_namecert_construction.tex:4 packages group structure on those permutations. FinSet currently proves bijection composition at 90:174-190 and EnumPerm transitivity at 90:192-240, but no identity/reflexivity theorem. Focused grep for `EnumPerm.*reflex|reflex.*EnumPerm|identity.*EnumPerm|EnumPerm.*identity` returned 0 hits, and the NameCert reflexivity field is available from papers/bedc/parts/core/08_typed_naming_certificates.tex:49-52.

---

### B-345 - FinSetEnumClassifier symmetry

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | FinSetEnumClassifier symmetry |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |

Problem:
If FinSetEnumClassifier_{A,sim_A}(xs,ys) holds, then FinSetEnumClassifier_{A,sim_A}(ys,xs) holds under the finite-spine enumeration membership definition.

Local inputs:
- `papers/bedc/parts/concrete_instances/90_finset_namecert_construction.tex`

Rationale:
FinSetEnumClassifier is defined extensionally as pointwise equivalence of EnumMem predicates at papers/bedc/parts/concrete_instances/90_finset_namecert_construction.tex:12-30. Existing theorems include EnumPerm implies FinSetEnumClassifier at 90:49-59 and FinSet enumeration classifier transitivity at 90:269-294, but there is no standalone symmetry theorem for the classifier. Focused grep for `FinSetEnumClassifier.*sym|sym.*FinSetEnumClassifier|finset-enumeration-classifier.*sym|FinSetEnumClassifier.*reflex|reflex.*FinSetEnumClassifier` returned 0 hits. This is a concrete inversion law for the FinSet enumeration classifier, not a parameter-transport echo.

---

### B-346 - EnumPerm symmetry from inverse bijection

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | EnumPerm symmetry from inverse bijection |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
Under a fixed SetUp carrier A with classifier sim_A, EnumPerm_{A,sim_A}(xs,ys) implies EnumPerm_{A,sim_A}(ys,xs) by using the certified inverse position map and source-classifier symmetry.

Local inputs:
- `papers/bedc/parts/concrete_instances/90_finset_namecert_construction.tex`

Rationale:
This is a concrete missing equivalence-relation law for the FinSet enumeration-permutation datum. The current FinSet chapter defines EnumPerm and proves invariant and transitivity results, but does not state the inverse-bijection symmetry theorem; it is not covered by existing BOARD targets or paper labels, and it lands safely in the existing FinSet concrete-instance file.

---

### B-347 - FinSet enum classifier symmetry

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | FinSet enum classifier symmetry |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 6/10 |

Problem:
Under a fixed SetUp carrier A with classifier sim_A, FinSetEnumClassifier_{A,sim_A}(xs,ys) implies FinSetEnumClassifier_{A,sim_A}(ys,xs) by reversing the pointwise membership equivalence for every query history.

Local inputs:
- `papers/bedc/parts/concrete_instances/90_finset_namecert_construction.tex`

Rationale:
This is a small but concrete certificate-completeness theorem for the finite-set enumeration classifier. The paper defines the classifier and proves transitivity, but no labeled theorem records symmetry; the target is distinct from EnumPerm symmetry because it applies directly to extensional enumeration classifiers rather than certified position bijections.

---

### B-348 - UnitUp terminal map uniqueness

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | UnitUp terminal map uniqueness |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
For any source naming certificate, if f and g send every carried source endpoint into UnitHistoryCarrier, then UnitHistoryClassifier(f(a),g(a)) holds for every carried input a.

Local inputs:
- `papers/bedc/parts/concrete_instances/93_unit_namecert_construction.tex`
- `papers/bedc/parts/core/08_typed_naming_certificates.tex`

Rationale:
The UnitUp chapter states the terminal-object role in prose and proves the empty-endpoint classifier facts, but it does not give the promised terminal uniqueness theorem as a labeled result. This is a concrete uniqueness target, not a marker or verification-axis item, and it cleanly belongs in the existing UnitUp concrete-instance surface.

---

### B-349 - Complex partial sums commute with pointwise addition

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | Complex partial sums commute with pointwise addition |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
If c and d have closed partial sums S_c(n) and S_d(n) at a unary index n, then the pointwise-sum sequence has a closed partial sum at n hsame to the complex sum of S_c(n) and S_d(n).

Local inputs:
- `papers/bedc/parts/concrete_instances/44_complex_series_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/14_complex_namecert_construction.tex`

Rationale:
This fills a paper-internal algebra gap between the complex partial-sum recursion and the later convergence-linearity statement. Existing labels cover partial-sum existence, determinacy, hsame transport, and convergence linearity, but not the finite partial-sum compatibility with pointwise addition; it is concrete, scoped, and distinct from current BOARD entries.

---

### B-350 - EnumPerm identity reflexivity

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (codex) |
| Object | EnumPerm identity reflexivity |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |

Problem:
If A(entry_xs(i)) holds for every position i under a fixed SetUp/NameCert, then the identity position bijection witnesses EnumPerm_A(xs,xs).

Local inputs:
- `papers/bedc/parts/concrete_instances/90_finset_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/89_set_namecert_construction.tex`
- `papers/bedc/parts/core/08_typed_naming_certificates.tex`

Rationale:
This is a concrete finite-spine permutation closure fact in the existing FinSet certificate surface. The paper already has EnumPerm inverse symmetry and transitivity, but not the identity/reflexivity witness; adding this target would close the missing basic relation law without duplicating an existing BOARD entry or paper theorem.

---

### B-351 - Ideal intersection closure

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Ideal intersection closure |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 9/10 |

Problem:
If R has a RingUp certificate and I,J are IdealUp predicates over R, then K(x)=I(x) and J(x) is an IdealUp predicate over R.

Local inputs:
- `papers/bedc/parts/concrete_instances/59_ideal_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/61_quotientring_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/18_ring_namecert_construction.tex`

Rationale:
IdealUp is structurally under-developed: papers/bedc/parts/concrete_instances/59_ideal_namecert_construction.tex:1-10 is only the chapter shell, while line 4 says the object is a sub-rng closed under multiplication by ambient ring elements and is the kernel object for QuotientRingUp. Quotient-ring content already consumes ideal fields for cosets and descent at papers/bedc/parts/concrete_instances/61_quotientring_namecert_construction.tex:12-22 and :75-89, but the IdealUp chapter itself has no canonical closure theorem. A binary intersection theorem is a concrete algebraic construction, not another quotient-ring descent target.

---

### B-352 - Sheaf gluing uniqueness from locality

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Sheaf gluing uniqueness from locality |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 10/10 |

Problem:
If a SheafUp presheaf gives a compatible local family on an open cover and two global sections restrict to that family on every cover member, then the two global sections are classifier-equal.

Local inputs:
- `papers/bedc/parts/concrete_instances/129_sheaf_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/128_presheaf_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/66_topology_namecert_construction.tex`

Rationale:
The sheaf chapter is untouched beyond its shell: papers/bedc/parts/concrete_instances/129_sheaf_namecert_construction.tex:4 says SheafUp is a presheaf satisfying locality and gluing over open covers, and :6-10 contains only empty carrier/certificate sections. The presheaf input is likewise only introduced at papers/bedc/parts/concrete_instances/128_presheaf_namecert_construction.tex:4-10, while generic TopologyUp has already gained indexed-open closure laws at papers/bedc/parts/concrete_instances/66_topology_namecert_construction.tex:45-128. This candidate opens a genuinely new sheaf-theoretic surface with the smallest nontrivial companion theorem to gluing.

---

### B-353 - Computable composition by bounded simulation

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Computable composition by bounded simulation |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 10/10 |

Problem:
If f and g are ComputableUp partial Nat functions with certified bounded simulations and f(n) returns m within its bound while g(m) returns k within its bound, then the composite g after f has a certified bounded simulation returning k.

Local inputs:
- `papers/bedc/parts/concrete_instances/177_computable_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/04_nat_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/98_seq_namecert_construction.tex`

Rationale:
Computability is a blindspot in the current board: papers/bedc/parts/concrete_instances/177_computable_namecert_construction.tex:4 defines ComputableUp through Turing-machine simulation up to time-step bounds, and :6-10 has no theorem body. The dependency on NatUp and SeqUp is explicit at the same line; NatUp has substantial unary infrastructure beginning at papers/bedc/parts/concrete_instances/04_nat_namecert_construction.tex:8, while SeqUp is only a substrate shell at papers/bedc/parts/concrete_instances/98_seq_namecert_construction.tex:4-10. Composition of bounded simulations is the first concrete theorem for this chapter and is distinct from the already queued Seq pointwise classifier target.

---

### B-354 - Error-code unique decoding radius

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Error-code unique decoding radius |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 10/10 |

Problem:
If C is an ErrorCodeUp code with minimum distance d and t=floor((d-1)/2), and two codewords c1,c2 are both within Hamming distance t of the same received word r, then c1 and c2 are code-classifier equal.

Local inputs:
- `papers/bedc/parts/concrete_instances/219_errorcode_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/20_field_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/22_vecspace_namecert_construction.tex`

Rationale:
Coding theory has no completed content despite a precise promise: papers/bedc/parts/concrete_instances/219_errorcode_namecert_construction.tex:4 packages a subset of F_q^n at minimum Hamming distance d with decoder data correcting up to floor((d-1)/2) errors, and :6-10 is empty. The theorem is a single metric-distance implication that explains why the advertised decoding radius is well-defined before any larger coding-theory results are attempted.

---

### B-355 - Matching subset closure

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Matching subset closure |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 9/10 |

Problem:
If M is a MatchingUp edge set in a GraphUp carrier and N is a FinSetUp edge subset of M, then N is also a MatchingUp edge set.

Local inputs:
- `papers/bedc/parts/concrete_instances/212_matching_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/96_graph_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/90_finset_namecert_construction.tex`

Rationale:
The combinatorial optimization slice is nearly empty: papers/bedc/parts/concrete_instances/212_matching_namecert_construction.tex:4 says MatchingUp is a subset of graph edges with no shared vertex, and :6-10 has no companion theorem. GraphUp is only the vertex/edge substrate at papers/bedc/parts/concrete_instances/96_graph_namecert_construction.tex:4-10, while FinSetUp now has concrete enumeration membership machinery at papers/bedc/parts/concrete_instances/90_finset_namecert_construction.tex:12-31. Subset heredity is the smallest real matching theorem and does not duplicate the graph edge-transport board item.

---

### B-356 - Finite ideal intersection closure

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (codex) |
| Object | Finite ideal intersection closure |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 6/10 |

Problem:
Under a RingUp certificate, if every predicate in a finite indexed family is IdealUp over the same RingUp data, then their pointwise finite intersection is IdealUp.

Local inputs:
- `papers/bedc/parts/concrete_instances/59_ideal_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/ring/18_ring_certificate_and_additive_laws.tex`
- `papers/bedc/parts/concrete_instances/90_finset_namecert_construction.tex`

Rationale:
This is a concrete closure theorem for the IdealUp chapter. The paper has binary ideal intersection closure, but not a finite indexed intersection package; the finite form is distinct enough to merit a narrow target because it packages the closure rows over a finite spine or finite-set witness and can land safely in the short IdealUp file using existing RingUp and FinSet/List infrastructure.

---

### B-357 - Ideal kernel closure for ring maps

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (codex) |
| Object | Ideal kernel closure for ring maps |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |

Problem:
Under source and target RingUp certificates, if f preserves carrier classification, zero, addition, additive inverse, and multiplication, then the zero-fiber predicate of f is an IdealUp predicate on the source ring.

Local inputs:
- `papers/bedc/parts/concrete_instances/59_ideal_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/ring/18_ring_certificate_and_additive_laws.tex`
- `papers/bedc/parts/concrete_instances/61_quotientring_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/21_module_linearmap_kernel_and_inverse_action.tex`

Rationale:
This is a concrete zero-fiber closure target for IdealUp and is not covered by the existing quotient-ring or module-linear-map kernel theorems. It gives the ring-level sibling of the LinearMap kernel submodule pattern while using IdealUp absorption and RingUp zero-product rows, so it fits the concrete_instances surface without duplicating an existing BOARD entry.

---

### B-358 - ProbSpace complement mass additivity

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | ProbSpace complement mass additivity |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 9/10 |

Problem:
If a ProbSpaceUp carrier has a measurable subset A and a measurable complement Ac whose disjoint union is the total space, then mu(A)+mu(Ac) is RealUp-classified as the probability unit.

Local inputs:
- `papers/bedc/parts/concrete_instances/162_probspace_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/70_measure_namecert_construction.tex`

Rationale:
The probability layer is an empty skeleton while its measure substrate has just become usable: papers/bedc/parts/concrete_instances/162_probspace_namecert_construction.tex:4 says ProbSpaceUp is a MeasureUp space with total measure equal to the unit, and papers/bedc/parts/concrete_instances/70_measure_namecert_construction.tex:47-52 now proves finite disjoint-union additivity. BOARD coverage around tools/bedc-deep/BOARD.md:8714 and tools/bedc-deep/BOARD.md:8790 covers MeasureUp only; grep over BOARD/state for ProbSpaceUp/probability returned no target. This is a concrete first probability theorem, not a new verification marker or carrier transport sequel.

---

### B-359 - Convex midpoint closure from affine-combination field

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Convex midpoint closure from affine-combination field |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 9/10 |

Problem:
If a ConvexSetUp carrier contains x and y and h is a nonnegative scalar with h+h classified as 1, then the affine midpoint h*x+h*y is carried by the same ConvexSetUp carrier.

Local inputs:
- `papers/bedc/parts/concrete_instances/186_convexset_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/184_affinespace_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/22_vecspace_namecert_construction.tex`

Rationale:
The convex-geometry slice has no deep-loop target and is still only a chapter stub: papers/bedc/parts/concrete_instances/186_convexset_namecert_construction.tex:4 says ConvexSetUp is closed under affine combinations with nonnegative coefficients summing to one, while papers/bedc/parts/concrete_instances/184_affinespace_namecert_construction.tex:4 and papers/bedc/parts/concrete_instances/22_vecspace_namecert_construction.tex:51-63 provide the affine/vector-space substrate. Grep over BOARD/state for ConvexSetUp/convex returned no hits. The midpoint statement is the smallest nontrivial specialization of the advertised closure law and gives later polytope/LP chapters a citable convexity lemma.

---

### B-360 - Network-flow weak duality for cuts

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Network-flow weak duality for cuts |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 9/10 |

Problem:
If f is a feasible NetworkFlowUp s-t flow and C is an s-t cut in the same directed graph, then the value of f is NatUp-classified below the capacity of C.

Local inputs:
- `papers/bedc/parts/concrete_instances/211_networkflow_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/96_graph_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/04_nat_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/90_finset_namecert_construction.tex`

Rationale:
Combinatorial optimization is nearly untouched beyond MatchingUp: papers/bedc/parts/concrete_instances/211_networkflow_namecert_construction.tex:4 promises edge capacities and max-flow/min-cut duality, papers/bedc/parts/concrete_instances/96_graph_namecert_construction.tex:4 supplies the graph edge substrate, and papers/bedc/parts/concrete_instances/04_nat_namecert_construction.tex:52-70 gives unary NatUp comparison infrastructure. BOARD has Matching subset closure at tools/bedc-deep/BOARD.md:9260, but no NetworkFlowUp/flow/cut target. Weak duality is a single concrete implication and the natural prerequisite before any max-flow/min-cut equality claim.

---

### B-361 - Hash second-preimage success induces collision

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Hash second-preimage success induces collision |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 10/10 |

Problem:
If a HashUp transcript is a successful second-preimage for message x with distinct x' and H(x') classified equal to H(x), then the pair (x,x') is a successful collision transcript for the same hash row.

Local inputs:
- `papers/bedc/parts/concrete_instances/220_hash_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/110_funcobj_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/90_finset_namecert_construction.tex`

Rationale:
The cryptographic slice has no completed deep-loop content: papers/bedc/parts/concrete_instances/220_hash_namecert_construction.tex:4 lists collision resistance, preimage resistance, and second-preimage resistance over a deterministic finite-output map, while papers/bedc/parts/concrete_instances/110_funcobj_namecert_construction.tex:4 gives the function-object substrate and papers/bedc/parts/concrete_instances/90_finset_namecert_construction.tex:4 supplies finite-output enumeration machinery. Grep over BOARD/state for HashUp/hash returned no hits. The reduction is a concrete transcript-level implication and avoids importing any cryptographic hardness theory.

---

### B-362 - Network-flow cut accounting from vertex conservation

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (codex) |
| Object | Network-flow cut accounting from vertex conservation |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
Under a finite directed NetworkFlowUp setup, if a flow satisfies the source-value row and vertex conservation at every nonterminal cut-side vertex, then every finite s-t cut supplies Cont(value, backward crossing flow, forward crossing flow).

Local inputs:
- `papers/bedc/parts/concrete_instances/211_networkflow_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/96_graph_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/90_finset_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/04_nat_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/05_add_namecert_construction.tex`

Rationale:
This is a concrete prerequisite theorem for the current network-flow surface: the existing weak-duality proof uses cut accounting as a feasibility row, while this target derives that row from local vertex conservation. It is not a BOARD duplicate and is not already proven by the current weak-duality theorem.

---

### B-363 - Network-flow max-flow min-cut equality package

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (codex) |
| Object | Network-flow max-flow min-cut equality package |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 9/10 |

Problem:
Under a finite NetworkFlowUp setup, if a feasible flow carries an augmenting-path exhaustion certificate, then its value is NatUp-classified equal to the capacity of the residual cut induced by that certificate.

Local inputs:
- `papers/bedc/parts/concrete_instances/211_networkflow_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/96_graph_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/90_finset_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/04_nat_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/27_preorder_namecert_construction.tex`

Rationale:
This is a conditional strong-duality target, distinct from the existing weak-duality cut bound. It lands directly in the network-flow chapter, has a single certificate-to-classification implication shape, and would close a named interface direction without duplicating any existing BOARD entry.

---

### B-364 - NetworkFlowUp residual reachability cut extraction

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (codex) |
| Object | NetworkFlowUp residual reachability cut extraction |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 7/10 |

Problem:
Under a finite NetworkFlowUp setup, if t is not residual-reachable from s, then the cut induced by the residual-reachable side supplies the residual-cut augmenting-path exhaustion certificate: all forward cut edges are saturated and the backward cut flow is classified empty.

Local inputs:
- `papers/bedc/parts/concrete_instances/211_networkflow_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/96_graph_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/90_finset_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/04_nat_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/27_preorder_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/05_add_namecert_construction.tex`

Rationale:
This is a concrete theorem-level bridge in the existing NetworkFlowUp surface: the paper already has weak duality, cut accounting, a residual-exhaustion certificate, and max-flow/min-cut equality from such a certificate, but it does not derive that certificate from the standard no-residual-path condition. It is not a duplicate of the existing equality package because it produces the certificate rows that the equality theorem assumes, and the landing file is a concrete non-hub chapter well below the line cap.

---

### B-365 - Sheaf global restrictions form compatible local family

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Sheaf global restrictions form compatible local family |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
If an indexed SheafUp carrier S over T has a cover U=(A,iota,h,gamma) of i and g is a section of Sec(i), then the family a |-> rho_{i,iota(a)}(g) is compatible over U under the presheaf restriction-composition and topology finite-intersection fields.

Local inputs:
- `papers/bedc/parts/concrete_instances/129_sheaf_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/66_topology_namecert_construction.tex`

Rationale:
The indexed presheaf carrier defines restriction maps, identity, and composition at papers/bedc/parts/concrete_instances/129_sheaf_namecert_construction.tex:12-32; the sheaf cover definition gives compatibility over pairwise intersections and says the needed inclusions come from the finite-intersection law at 129_sheaf_namecert_construction.tex:35-59, with that topology law labeled at papers/bedc/parts/concrete_instances/66_topology_namecert_construction.tex:46. The only theorem in the sheaf file is gluing uniqueness from locality at 129_sheaf_namecert_construction.tex:62-96. Focused rg for global/restrict/compatible local family/global section terms under parts found 0 theorem labels for global restrictions forming a compatible local family; hits were the definition and the uniqueness theorem context, not this closure claim. The target file is 96 lines and has 0 Lean marker macros.

---

### B-366 - Computable bounded graph certificate is functional

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Computable bounded graph certificate is functional |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
If a partial graph F carries a bounded ComputableUp graph certificate and F(n,m) and F(n,m') both hold, then m and m' are hsame-classified NatUp outputs.

Local inputs:
- `papers/bedc/parts/concrete_instances/177_computable_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/04_nat_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/98_seq_namecert_construction.tex`

Rationale:
The bounded simulation witness is defined at papers/bedc/parts/concrete_instances/177_computable_namecert_construction.tex:12-24, and the bounded graph certificate states both F(n,m) iff BoundedSim(P_F,n,beta_F(n),m) and same-input output determinacy for bounded simulations at 177_computable_namecert_construction.tex:27-33. The only theorem in the file is composition by bounded simulation at 177_computable_namecert_construction.tex:36-65, with its Lean marker at line 56. Focused rg for computable determinacy, bounded same input, output determinacy, and graph functional terms found 0 computable theorem labels; the only hits in this file were definition prose at lines 29 and 33, while other hits were unrelated module or continuous determinacy theorems.

---

### B-367 - Hash collision success is symmetric

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Hash collision success is symmetric |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
If HashCollisionSuccess_H(x,x') holds and the message and digest classifiers are symmetric in the HashUp certificate, then HashCollisionSuccess_H(x',x) holds over the same evaluation row.

Local inputs:
- `papers/bedc/parts/concrete_instances/220_hash_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/90_finset_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/110_funcobj_namecert_construction.tex`

Rationale:
Hash evaluation, second-preimage success, and ordered collision success are defined at papers/bedc/parts/concrete_instances/220_hash_namecert_construction.tex:12-40; the existing theorem only proves second-preimage success induces collision for the same ordered pair at 220_hash_namecert_construction.tex:43-64. Focused rg for hash collision symmetry, collision reverse, HashCollisionSuccess, and second-preimage/collision terms returned only the definition at line 32 and the second-preimage theorem at lines 43-49, with 0 theorem labels for reversing a collision transcript. The file is 64 lines and has 0 Lean marker macros.

---

### B-368 - Convex affine-combination row is order symmetric

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Convex affine-combination row is order symmetric |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 7/10 |
| Novelty | 7/10 |

Problem:
If a ConvexSetUp binary affine-combination row holds, x and y are carried, a and b are nonnegative, and a+_F b is classifier-equal to 1_F with scalar-addition commutativity, then the swapped endpoint (b odot y)+_V(a odot x) is carried by the same convex carrier.

Local inputs:
- `papers/bedc/parts/concrete_instances/186_convexset_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/20_field_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/22_vecspace_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/184_affinespace_namecert_construction.tex`

Rationale:
The binary affine-combination row is defined at papers/bedc/parts/concrete_instances/186_convexset_namecert_construction.tex:12-30 and already gives closure for ordered coefficients and ordered endpoints. The only theorem in the file is the midpoint specialization at 186_convexset_namecert_construction.tex:32-57. Focused rg for convex symmetry, affine swap, affine symmetry, midpoint, and ConvexSet terms found 0 theorem labels for a swapped affine-combination closure; hits were the definition, the midpoint theorem, and unrelated affine uses in field files. The target file is only 57 lines and has 0 Lean marker macros.

---

### B-369 - Module action annihilator is an IdealUp predicate

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Module action annihilator is an IdealUp predicate |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
Under a ModuleUp(R,M) certificate, if Ann_M(r) and Ann_M(s) hold then Ann_M(r+_R s) and Ann_M(-_R r) hold, and if a is carried by R then Ann_M(a dot_R r) and Ann_M(r dot_R a) hold, so Ann_M is an IdealUp predicate over R.

Local inputs:
- `papers/bedc/parts/concrete_instances/module/action_faithfulness_annihilator.tex`
- `papers/bedc/parts/concrete_instances/module/21_module_namecert_construction_core.tex`
- `papers/bedc/parts/concrete_instances/59_ideal_namecert_construction.tex`
- `lean4/BEDC/Derived/ModuleUp.lean`
- `lean4/BEDC/Derived/RingUp.lean`

Rationale:
This belongs in the module action-faithfulness child file. The object is already introduced at papers/bedc/parts/concrete_instances/module/action_faithfulness_annihilator.tex:1-20, and line 20 explicitly says no ideal carrier is introduced. Existing results only prove the difference-annihilator lemma and the faithful-action iff zero-annihilator theorem at lines 23-104. The missing theorem is the standard module-theory fact that the annihilator of a module is an ideal, found in any introductory algebra text after modules are introduced. It should close in 1-3 rounds because the proof only uses scalar distributivity, zero action, ring additive inverse/addition, and two-sided absorption-style scalar multiplication rows already present in the module and ring chapters.

---

### B-370 - Ring-map preimage of an ideal is an IdealUp predicate

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Ring-map preimage of an ideal is an IdealUp predicate |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 7/10 |

Problem:
Under RingUp certificates S and T, a ring map f:S to T, and an IdealUp predicate J on T, if K(x) is the carried preimage condition C_S(x) and J(f(x)), then K satisfies the IdealUp rows on S.

Local inputs:
- `papers/bedc/parts/concrete_instances/59_ideal_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/18_ring_namecert_construction.tex`
- `lean4/BEDC/Derived/RingUp.lean`

Rationale:
This belongs in the IdealUp chapter. The file already proves the special zero-fiber case at papers/bedc/parts/concrete_instances/59_ideal_namecert_construction.tex:55-148, but focused grep found no preimage or inverse-image ideal theorem. The theorem is the standard preimage-of-an-ideal result from introductory ring theory, and it is a direct generalization of the existing zero-fiber proof. It should close quickly because the zero-fiber proof already exhibits the carrier, classifier-transport, addition, inverse, multiplication, and absorption proof pattern; replacing the target zero predicate by an arbitrary target ideal predicate reuses the same ring-map preservation rows plus the IdealUp rows for J.

---

### B-371 - Subgroup one-step criterion

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Subgroup one-step criterion |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
Under a GroupUp carrier and predicate P, if P is inhabited, classifier-stable, and closed under x dot inv(y) for any two P-elements, then P satisfies the SubgroupUp identity, product, inverse, and transport rows.

Local inputs:
- `papers/bedc/parts/concrete_instances/58_subgroup_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/16_group_namecert_construction.tex`
- `lean4/BEDC/Derived/SubgroupUp.lean`
- `lean4/BEDC/Derived/GroupUp.lean`

Rationale:
This belongs in the SubgroupUp chapter. The chapter proves centralizer, intersection, trivial subgroup, and subgroup-chain certificates, for example papers/bedc/parts/concrete_instances/58_subgroup_namecert_construction_core.tex:27-66, 86-138, and papers/bedc/parts/concrete_instances/58_subgroup_namecert_construction.tex:550-685, but focused searches for one-step, subgroup test, and inverse-product closure found no theorem. The one-step subgroup criterion is a standard theorem in introductory group theory. It should close in 1-3 rounds from existing group identity, inverse, associativity, multiplication congruence, and classifier transport rows: use an inhabitant a to get e from a dot inv(a), get inv(x) from e dot inv(x), and get xy from x dot inv(inv(y)).

---

### B-372 - Computable bounded graph single-valuedness

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | Computable bounded graph single-valuedness |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
Under a bounded ComputableUp graph certificate, if F(n,m) and F(n,m') are accepted for the same unary input n, then m hsame m'.

Local inputs:
- `papers/bedc/parts/concrete_instances/177_computable_namecert_construction.tex`

Rationale:
This is a concrete determinacy theorem for the ComputableUp graph surface. The certificate already records bounded-simulation output uniqueness, but the paper only exposes it as a definition field and currently has composition as the standalone theorem; making graph single-valuedness explicit would fill a small, closeable theorem slot without duplicating an existing BOARD item.

---

### B-373 - Hash collision transcript symmetry

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | Hash collision transcript symmetry |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
If HashCollisionSuccess_H(x,x') holds and the message and digest classifiers are symmetric, then HashCollisionSuccess_H(x',x) holds over the same HashEval rows.

Local inputs:
- `papers/bedc/parts/concrete_instances/220_hash_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/90_finset_namecert_construction.tex`

Rationale:
This is a concrete bridge theorem for the HashUp transcript predicates. The paper proves that second-preimage success induces collision, but it does not separately state collision symmetry; the result is local, uses the same evaluation rows, and turns classifier symmetry into an explicit transcript-level operation.

---

### B-374 - Network-flow equality implies optimality

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | Network-flow equality implies optimality |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 10/10 |
| Novelty | 8/10 |

Problem:
If a feasible flow F and finite cut C satisfy FlowValue(F) hsame CutCap(C), then every feasible flow has value below FlowValue(F) and every finite cut has capacity above CutCap(C).

Local inputs:
- `papers/bedc/parts/concrete_instances/211_networkflow_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/96_graph_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/04_nat_namecert_construction.tex`

Rationale:
This directly fills a standard readback gap in the NetworkFlowUp chapter. Weak duality and residual-exhaustion equality are already present, but the optimality consequence from equality is not separately labeled; it is concrete, local, and distinct from the existing equality theorem.

---

### B-375 - Banach bounded operator composition closure

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | Banach bounded operator composition closure |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
If BanachBLOp(C,D,T,K,Lambda) and BanachBLOp(D,E,S,L,Mu), then the composite endpoint map S o T is a BanachBLOp(C,E,S o T,L*K,Nu) with the composed ledger.

Local inputs:
- `papers/bedc/parts/concrete_instances/banach/bounded_linear_operator_obligations.tex`
- `papers/bedc/parts/concrete_instances/banach/norm_completion_certificate.tex`

Rationale:
This is a natural closure theorem for the Banach bounded-linear-operator carrier. The chapter already proves Lipschitz use, Cauchy-stream transport, and NameCert obligations, but not carrier closure under composition; the target is concrete and has an appropriate child-file landing path.

---

### B-376 - ConvexSet finite affine-spine closure

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | ConvexSet finite affine-spine closure |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
Under a ConvexSetUp binary affine-combination row, any finite carried point spine with nonnegative scalar weights whose finite scalar sum is classified as 1_F has its recursively bracketed affine endpoint carried by C.

Local inputs:
- `papers/bedc/parts/concrete_instances/186_convexset_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/90_finset_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/22_vecspace_namecert_construction.tex`

Rationale:
This upgrades the binary ConvexSetUp row to the finite-spine closure that the chapter description advertises. The paper currently proves midpoint closure only, so the finite affine-spine result is a distinct concrete closure theorem rather than a duplicate of existing coverage.

---

### B-377 - Analytic continuation identity law

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | Analytic continuation identity law |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |

Problem:
If f is holomorphic on D and DomCompat(D,D,U) is witnessed by a nontrivial overlap inside D, then AnaCont(f,D,f,D,f) holds and any h with AnaCont(f,D,f,D,h) is pointwise hsame to f.

Local inputs:
- `papers/bedc/parts/concrete_instances/50_analytic_continuation_operation.tex`

Rationale:
This is a missing operation-law companion for the AnalyticContUp chapter. Uniqueness, symmetry, functoriality, and triple-chain associativity are already labeled, but the identity law is not; the claim is concrete and local to the existing continuation predicate.

---

### B-378 - ConvexSet raw finite weights normalize to affine spine

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (codex) |
| Object | ConvexSet raw finite weights normalize to affine spine |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |

Problem:
Under ConvexSetUp over FieldUp(F) and VecSpaceUp(F,V), if xs and lambda are nonempty aligned finite spines, every point in xs is carried, every weight in lambda is NonNeg_F, and sum_F(lambda) ~_F 1_F, then there exists an endpoint z with ConvAffSpine_C(xs,lambda,z).

Local inputs:
- `papers/bedc/parts/concrete_instances/186_convexset_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/22_vecspace_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/184_affinespace_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/20_field_namecert_construction.tex`

Rationale:
This lands directly in the existing ConvexSetUp chapter and is not a BOARD duplicate. The paper already defines ConvAffSpine_C and proves carrier closure from an existing ConvAffSpine witness, but this target supplies the missing normalization/construction step from raw finite affine weights to that witness. It is concrete theorem work rather than marker or verification-axis work, and the landing file is small and non-hub.

---

### B-379 - Distribution pushforward has unit total mass

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Distribution pushforward has unit total mass |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 10/10 |

Problem:
If X is a carried RandomVarUp map from a ProbSpaceUp source and mu_X is the DistributionUp pushforward measure on its target total event, then mu_X(target) is RealUp-classified as the probability unit.

Local inputs:
- `papers/bedc/parts/concrete_instances/163_randomvar_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/164_distribution_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/162_probspace_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/70_measure_namecert_construction.tex`

Rationale:
Probability has only a first ProbSpace theorem so far: papers/bedc/parts/concrete_instances/162_probspace_namecert_construction.tex:12-20 proves complement mass additivity, while RandomVarUp and DistributionUp remain only the chapter promise plus carrier/certificate section labels at papers/bedc/parts/concrete_instances/163_randomvar_namecert_construction.tex:4-10 and papers/bedc/parts/concrete_instances/164_distribution_namecert_construction.tex:4-10. The Measure substrate already has finite disjoint-union additivity at papers/bedc/parts/concrete_instances/70_measure_namecert_construction.tex:47-52, so the missing bridge is specifically the pushforward total-mass consequence. Focused BOARD search found no RandomVarUp or DistributionUp target.

---

### B-380 - Affine zero-locus intersection by equation concatenation

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Affine zero-locus intersection by equation concatenation |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 10/10 |

Problem:
If x is classified in both AffineVarUp zero-loci V(F) and V(G) over the same affine n-space, then x is classified in the zero-locus of the concatenated finite polynomial family F++G.

Local inputs:
- `papers/bedc/parts/concrete_instances/132_affinevar_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/25_polynomial_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/90_finset_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/19_commring_namecert_construction.tex`

Rationale:
The algebraic-geometry slice is essentially untouched: papers/bedc/parts/concrete_instances/132_affinevar_namecert_construction.tex:4 defines AffineVarUp as a zero-locus of a finite polynomial system, but the chapter has only carrier and certificate section labels at lines 6-10. PolynomialUp already gives the finite coefficient-sequence substrate at papers/bedc/parts/concrete_instances/25_polynomial_namecert_construction.tex:4, and FinSetUp has concrete finite enumeration membership at papers/bedc/parts/concrete_instances/90_finset_namecert_construction.tex:12-30. Focused BOARD/state-filename search found no AffineVarUp target.

---

### B-381 - Adjoint action derivation from Jacobi

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Adjoint action derivation from Jacobi |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 10/10 |

Problem:
If L is a LieAlgebraUp carrier and x,y,z are carried, then the Jacobi identity implies ad_x([y,z]) is classifier-equal to [ad_x(y),z]+[y,ad_x(z)].

Local inputs:
- `papers/bedc/parts/concrete_instances/119_liealgebra_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/121_adjointrep_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/22_vecspace_namecert_construction.tex`

Rationale:
Lie theory has no deep-loop coverage: papers/bedc/parts/concrete_instances/119_liealgebra_namecert_construction.tex:4 promises an antisymmetric bilinear bracket satisfying Jacobi, and papers/bedc/parts/concrete_instances/121_adjointrep_namecert_construction.tex:4 names the differential ad, but both chapters are only carrier/certificate skeletons at lines 6-10. VecSpaceUp already supplies the vector-space substrate at papers/bedc/parts/concrete_instances/22_vecspace_namecert_construction.tex:4. Focused BOARD search found no LieAlgebraUp, LieGroupUp, or ExpMapUp target.

---

### B-382 - Quantum channel composition closure

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Quantum channel composition closure |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 10/10 |

Problem:
If Phi and Psi are QuantumChannelUp maps with matching density-matrix spaces, then Psi composed with Phi is a QuantumChannelUp map and sends every DensityMatrixUp input to a DensityMatrixUp output.

Local inputs:
- `papers/bedc/parts/concrete_instances/199_quantumchannel_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/198_densitymatrix_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/linearmap/the_certificate.tex`

Rationale:
The quantum slice is empty despite precise interface text: papers/bedc/parts/concrete_instances/198_densitymatrix_namecert_construction.tex:4 defines DensityMatrixUp as positive trace-class trace-one data, and papers/bedc/parts/concrete_instances/199_quantumchannel_namecert_construction.tex:4 defines QuantumChannelUp as a CPTP linear map, but the quantum-channel chapter has only section labels at lines 6-10. LinearMapUp already has the map classifier and certificate surface at papers/bedc/parts/concrete_instances/linearmap/the_certificate.tex:1-28. Focused BOARD/state-filename search found no QuantumChannelUp or DensityMatrixUp target.

---

### B-383 - Matroid intersection preserves independence

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Matroid intersection preserves independence |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 10/10 |

Problem:
If I is a MatroidUp independent finite set and J is the FinSetUp intersection of I with any finite subset of the same ground set, then J is MatroidUp independent.

Local inputs:
- `papers/bedc/parts/concrete_instances/180_matroid_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/90_finset_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/lattice/the_certificate.tex`

Rationale:
Combinatorial structure beyond FinSet/Matching/NetworkFlow is still sparse: papers/bedc/parts/concrete_instances/180_matroid_namecert_construction.tex:4 says MatroidUp has independent subsets closed under taking subsets and exchange, but lines 6-10 contain only the empty carrier/certificate section surface. FinSetUp has concrete enumeration membership at papers/bedc/parts/concrete_instances/90_finset_namecert_construction.tex:12-30, and LatticeUp exposes meet/intersection-style bound structure at papers/bedc/parts/concrete_instances/lattice/the_certificate.tex:18-28. Focused BOARD/state-filename search found no MatroidUp target.

---

### B-384 - Public-key decrypt-encrypt correctness

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Public-key decrypt-encrypt correctness |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 7/10 |
| Novelty | 9/10 |

Problem:
If (pk,sk) is generated by PublicKeyUp and c is a certified encryption of a carried message m under pk, then decrypting c with sk returns a message-classifier representative of m.

Local inputs:
- `papers/bedc/parts/concrete_instances/221_publickey_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/146_numfield_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/group/namecert_construction_core/02_certificate.tex`

Rationale:
Cryptographic BEDC content has concentrated on HashUp, where concrete transcript theorems now exist at papers/bedc/parts/concrete_instances/220_hash_namecert_construction.tex:43-49 and 67-74. PublicKeyUp remains a skeleton: papers/bedc/parts/concrete_instances/221_publickey_namecert_construction.tex:4 promises key generation, encryption, decryption, and security reductions, while lines 6-10 have no companion theorem. The number-field and group substrates exist at papers/bedc/parts/concrete_instances/146_numfield_namecert_construction.tex:4-30 and papers/bedc/parts/concrete_instances/group/namecert_construction_core/02_certificate.tex:18-28. Focused BOARD search found no PublicKeyUp target.

---

### B-385 - Affine empty family full-space zero-locus

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (codex) |
| Object | Affine empty family full-space zero-locus |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 6/10 |

Problem:
Under the affine finite-family zero-locus setup, AffPoint_R,n(x) implies V_R,n(empty)(x).

Local inputs:
- `papers/bedc/parts/concrete_instances/132_affinevar_namecert_construction.tex`

Rationale:
This is a concrete base-case theorem for the existing AffineVarUp zero-locus definition. It is not a BOARD duplicate and is not already present as a theorem or corollary; the current paper has the zero-locus definition and a concatenation/intersection theorem, but no empty-family full-space statement. The landing file is short and directly suitable.

---

### B-386 - Affine duplicate equation insertion invariance

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (codex) |
| Object | Affine duplicate equation insertion invariance |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 6/10 |

Problem:
Under the affine finite-family zero-locus setup, if a polynomial equation already occurs in F, then V_R,n(insert(p,F))(x) implies and is implied by V_R,n(F)(x).

Local inputs:
- `papers/bedc/parts/concrete_instances/132_affinevar_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/90_finset_namecert_construction.tex`

Rationale:
This is a concrete invariance property for affine zero-loci under redundant finite-spine equations. It is adjacent to the existing FinSet duplicate insertion theorem, but that theorem concerns finite-set enumeration classifiers rather than affine polynomial-equation zero-loci, so this is not already proven at the affine-variety surface.

---

### B-387 - Affine finite-family inclusion reverses zero-loci

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (codex) |
| Object | Affine finite-family inclusion reverses zero-loci |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 7/10 |

Problem:
Under the affine finite-family zero-locus setup, if every equation occurring in F also occurs in G, then V_R,n(G)(x) implies V_R,n(F)(x).

Local inputs:
- `papers/bedc/parts/concrete_instances/132_affinevar_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/90_finset_namecert_construction.tex`

Rationale:
This is the natural contravariance theorem for finite polynomial-family zero-loci and is broader than the existing concatenation/intersection result. It is concrete, lands in the current AffineVarUp chapter, and would give a reusable inclusion principle for later affine-variety arguments without duplicating an existing BOARD target.

---

### B-388 - Inner derivation commutator identity

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (codex) |
| Object | Inner derivation commutator identity |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
If L carries a \LieAlgebraUp certificate and x,y,z are carried endpoints, then [\operatorname{ad}^{L}_{x},\operatorname{ad}^{L}_{y}](z) \sim_{L} \operatorname{ad}^{L}_{[x,y]_{L}}(z).

Local inputs:
- `papers/bedc/parts/concrete_instances/119_liealgebra_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/121_adjointrep_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/22_vecspace_namecert_construction.tex`

Rationale:
This is a concrete Lie-algebra theorem landing in the existing \LieAlgebraUp and \AdjointRepUp surface. The paper already has the adjoint-action definition and the derivation law from Jacobi, but no labeled theorem for the inner-derivation commutator identity. It is not a marker, closurestatus change, or mere classifier-field echo; it packages a standard Jacobi consequence that supports the adjoint-representation certificate surface without duplicating any current BOARD entry.

---

### B-389 - Distribution empty target event has zero mass

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (codex) |
| Object | Distribution empty target event has zero mass |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 6/10 |

Problem:
Under a DistributionUp pushforward for a RandomVarUp map, if the empty target event is measurable, its preimage is identified with the source empty event, and the source MeasureUp empty-set-zero theorem applies, then the pushforward mass of the target empty event is RealUp-classified as zero.

Local inputs:
- `papers/bedc/parts/concrete_instances/164_distribution_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/163_randomvar_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/162_probspace_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/70_measure_namecert_construction.tex`

Rationale:
This is a concrete distribution-level coverage theorem that lands naturally beside the existing total-mass theorem. It is not already proved by the MeasureUp empty-set theorem alone, because it explicitly composes the RandomVarUp preimage row with the DistributionUp pushforward row.

---

### B-390 - Distribution finite disjoint-union additivity

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (codex) |
| Object | Distribution finite disjoint-union additivity |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 7/10 |

Problem:
Under a DistributionUp pushforward for a RandomVarUp map, if target events are measurable and disjoint, preimages preserve the measurable union and disjointness, and the source MeasureUp finite disjoint-union theorem applies, then the pushforward mass of the union is RealUp-classified as the sum of the pushforward masses.

Local inputs:
- `papers/bedc/parts/concrete_instances/164_distribution_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/163_randomvar_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/70_measure_namecert_construction.tex`

Rationale:
This fills a real structural gap: the paper has MeasureUp finite disjoint-union additivity and a DistributionUp total-mass theorem, but not the inherited finite additivity law for pushforward distributions. It is concrete, local, and distinct from the existing BOARD targets.

---

### B-391 - Quantum channel identity closure

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (codex) |
| Object | Quantum channel identity closure |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |

Problem:
Under a fixed Hilbert carrier H, the identity trace-class map id_TC(H) is carried by QuantumChannelUp(H,H), and every DensityMatrixUp(H) input is fixed as a DensityMatrixUp(H) output.

Local inputs:
- `papers/bedc/parts/concrete_instances/199_quantumchannel_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/198_densitymatrix_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/linearmap/module_linearmap_certificates.tex`

Rationale:
The quantum-channel surface already has density-matrix image closure and binary composition closure, but it does not state the identity-channel unit law. This is a concrete closure target, not a marker or parameter echo, and it safely lands beside the existing QuantumChannel carrier and composition theorem while using the existing LinearMap identity certificate as local support.

---

### B-392 - Density matrix convex mixture closure

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (codex) |
| Object | Density matrix convex mixture closure |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
For a fixed Hilbert carrier H, if a finite spine of trace-class operators are DensityMatrixUp(H) carriers and the weights are nonnegative with total weight one, then the finite affine mixture is again a DensityMatrixUp(H) carrier.

Local inputs:
- `papers/bedc/parts/concrete_instances/198_densitymatrix_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/199_quantumchannel_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/186_convexset_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/191_operatorideal_namecert_construction.tex`

Rationale:
The paper has a concrete density-matrix carrier definition and a general ConvexSet finite affine-spine closure theorem, but no density-matrix-specific convexity theorem. This is a concrete closure result for an existing BEDC object, distinct from existing quantum-channel and convex-set entries, and it would make the mixed-state interface materially stronger.

---

### B-393 - Public-key decryption output determinacy

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (codex) |
| Object | Public-key decryption output determinacy |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
Under a PublicKeyUp certificate with a decrypt-output determinacy row, PKKeyGen_P(pk,sk), PKDecrypt_P(sk,c,d1), and PKDecrypt_P(sk,c,d2) imply mu_P(d1,d2).

Local inputs:
- `papers/bedc/parts/concrete_instances/221_publickey_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/16_group_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/146_numfield_namecert_construction.tex`
- `papers/bedc/parts/core/08_typed_naming_certificates.tex`

Rationale:
This is a concrete determinacy target for the existing PublicKeyUp surface: the paper already has a transcript interface and decrypt-encrypt correctness, but not a theorem saying two decryption endpoints for the same secret key and ciphertext are message-classifier equal. It is not a BOARD duplicate, not a marker or closure-status item, and lands safely in the existing public-key concrete-instance file.

---

### B-394 - Matroid restriction certificate

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (codex) |
| Object | Matroid restriction certificate |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |

Problem:
Under a MatroidUp independent-set certificate over ground E and a FinSetUp subset K of E, the family of independent predicates contained in K satisfies the MatroidUp certificate rows over K.

Local inputs:
- `papers/bedc/parts/concrete_instances/180_matroid_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/90_finset_namecert_construction.tex`

Rationale:
The claim is a concrete certificate-construction implication inside the existing MatroidUp and FinSetUp surface. It is not covered by existing BOARD targets, and the current matroid paper content only gives intersection preservation of independence rather than the full restricted-certificate construction with inherited empty, hereditary, ground, finite, and exchange rows.

---

### B-395 - LieAlgebra adjoint additive linearity

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | LieAlgebra adjoint additive linearity |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
If L is a LieAlgebraUp carrier and x, y, z are carried, then ad_x(y +_L z) is classifier-equal to ad_x(y) +_L ad_x(z).

Local inputs:
- `papers/bedc/parts/concrete_instances/119_liealgebra_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/22_vecspace_namecert_construction.tex`

Rationale:
The Lie algebra chapter states that LieAlgebraUp packages a vector-space carrier with an antisymmetric bilinear bracket satisfying Jacobi at papers/bedc/parts/concrete_instances/119_liealgebra_namecert_construction.tex:4, then defines the adjoint action ad_x(t) = [x,t]_L at papers/bedc/parts/concrete_instances/119_liealgebra_namecert_construction.tex:12-18. Existing labeled theorems are the derivation identity at papers/bedc/parts/concrete_instances/119_liealgebra_namecert_construction.tex:21-62 and the inner-derivation commutator identity at papers/bedc/parts/concrete_instances/119_liealgebra_namecert_construction.tex:64-107. Focused grep for theorem labels matching `adjoint.*linear|adjoint.*additive|linear.*adjoint|ad.*scalar` produced no candidate label; broader hits were only definition/proof prose inside those two existing theorems, so the basic additive linearity of each adjoint map is still absent.

---

### B-396 - Computable identity bounded graph certificate

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Computable identity bounded graph certificate |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
If Id(n,m) is unary classifier equality on NatUp histories, then a deterministic halted identity machine with its displayed bound supplies a bounded ComputableUp graph certificate for Id.

Local inputs:
- `papers/bedc/parts/concrete_instances/177_computable_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/98_seq_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/04_nat_namecert_construction.tex`

Rationale:
The computable chapter defines BoundedSim by a trace, initial configuration, transition rows, halted endpoint, and output readout at papers/bedc/parts/concrete_instances/177_computable_namecert_construction.tex:12-25, then defines a bounded graph certificate by a deterministic code, unary bound, graph equivalence, and output determinacy at papers/bedc/parts/concrete_instances/177_computable_namecert_construction.tex:27-35. It proves composition at papers/bedc/parts/concrete_instances/177_computable_namecert_construction.tex:37-56 and graph single-valuedness at papers/bedc/parts/concrete_instances/177_computable_namecert_construction.tex:87-116. Focused grep for `computable.*identity|identity.*computable|bounded.*identity|id.*BoundedSim` found no identity theorem; the only nearby hit was unrelated composition prose at papers/bedc/parts/concrete_instances/177_computable_namecert_construction.tex:65.

---

### B-397 - PublicKey arbitrary decryption of certified encryption

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | PublicKey arbitrary decryption of certified encryption |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |

Problem:
If PKDecryptEncryptExact, decrypt-output determinacy, PKKeyGen(pk,sk), PKCertifiedEnc(pk,m,c), and PKDecrypt(sk,c,d) hold, then d is message-classifier equal to m.

Local inputs:
- `papers/bedc/parts/concrete_instances/221_publickey_namecert_construction.tex`

Rationale:
The public-key chapter defines certified encryption and decrypt-encrypt exactness at papers/bedc/parts/concrete_instances/221_publickey_namecert_construction.tex:30-50. It proves decrypt-encrypt correctness only as an existential decryption endpoint at papers/bedc/parts/concrete_instances/221_publickey_namecert_construction.tex:53-68, and separately defines and proves decrypt-output determinacy at papers/bedc/parts/concrete_instances/221_publickey_namecert_construction.tex:83-116. Focused grep for `publickey.*any.*decrypt|decrypt.*certified.*encrypt|decrypt.*encrypt.*determin|decryption.*certified|decrypt.*returns.*original` found only the existing correctness and determinacy lines, with no theorem composing them into the arbitrary-output correctness implication.

---

### B-398 - Split isomorphism inverse witnesses coincide

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Split isomorphism inverse witnesses coincide |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
Under a CategoryUp certificate, if f:a->b carries a split-isomorphism witness pair with left inverse g_L and right inverse g_R, then g_L and g_R are classifier-equal in the hom carrier from b to a.

Local inputs:
- `papers/bedc/parts/concrete_instances/36_category_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/functor/certificate_obligations.tex`
- `lean4/BEDC/Derived/CategoryUp.lean`
- `lean4/BEDC/Derived/FunctorUp.lean`

Rationale:
Belongs to the category/functor certificate cluster. This is the standard category-theory lemma that a left inverse and a right inverse of the same morphism coincide, found in any introductory category text around isomorphisms. The split-isomorphism witness pair is defined at papers/bedc/parts/concrete_instances/functor/certificate_obligations.tex:527, and lines 531-541 explicitly store left and right inverse witnesses while saying no equality between them is required. Focused searches for split inverse uniqueness, left-right inverse equality, g_L/g_R equality, and inverse uniqueness found no labeled theorem or BOARD entry. The proof is a one-page associativity/unit calculation: g_L = g_L id_b = g_L (f g_R) = (g_L f) g_R = id_a g_R = g_R. It should land in the shorter category body surface rather than appending to certificate_obligations.tex, which is already 783 lines.

---

### B-399 - Split monomorphisms are left-cancellative

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Split monomorphisms are left-cancellative |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 7/10 |

Problem:
Under a CategoryUp certificate, if f:a->b has a split-monomorphism witness and the composites f after u and f after v are hom-classifier equal for u,v:x->a, then u and v are hom-classifier equal.

Local inputs:
- `papers/bedc/parts/concrete_instances/36_category_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/functor/certificate_obligations.tex`
- `lean4/BEDC/Derived/CategoryUp.lean`
- `lean4/BEDC/Derived/FunctorUp.lean`

Rationale:
Belongs to the category/functor certificate cluster. The textbook theorem is 'every split monomorphism is monic' (Mac Lane CWM I.5 / Riehl 1.2). The split-monomorphism definition is present at papers/bedc/parts/concrete_instances/functor/certificate_obligations.tex:421 and composition of split monomorphisms is already a theorem at :727, but focused searches for split mono cancellation or split monomorphism implies monomorphism found no labeled theorem and no BOARD entry. The proof uses only the stored left inverse, composition congruence, associativity, and identity laws: precompose the displayed equality by the left inverse and reduce both sides. This is a concrete cancellation theorem, not a field repackaging.

---

### B-400 - ProbSpace complement mass as one minus event mass

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | ProbSpace complement mass as one minus event mass |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 6/10 |

Problem:
Under a ProbSpaceUp carrier with complement additivity for A and Ac and an additive RealUp inverse, if mu(A)+mu(Ac) is RealUp-classified as 1_R, then mu(Ac) is RealUp-classified as 1_R + (-mu(A)).

Local inputs:
- `papers/bedc/parts/concrete_instances/162_probspace_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/70_measure_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/17_abgroup_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/group/namecert_construction_core/02_certificate.tex`
- `lean4/BEDC/Derived/AbGroupUp.lean`

Rationale:
Belongs to the probability-space chapter. The theorem P(A^c)=1-P(A) is a first-page result in introductory probability texts after finite additivity. The chapter currently proves only complement additivity at papers/bedc/parts/concrete_instances/162_probspace_namecert_construction.tex:13, using measure finite disjoint-union additivity from papers/bedc/parts/concrete_instances/70_measure_namecert_construction.tex:48. Focused search for one-minus, complement subtraction, or probability complement subtraction found no labeled theorem and BOARD has only B-358 for additivity. The file is 44 lines, so the target is safe to append. The proof closes by adding the additive inverse of mu(A), using RealUp/AbGroup cancellation or inverse uniqueness from the group certificate, and the additive unit law.

---

### B-401 - LieAlgebra adjoint scalar linearity

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (codex) |
| Object | LieAlgebra adjoint scalar linearity |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |

Problem:
If L carries LieAlgebraUp and r, x, y are carried scalar/vector endpoints, then ad_x(r smul y) is classifier-equal to r smul ad_x(y).

Local inputs:
- `papers/bedc/parts/concrete_instances/119_liealgebra_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/22_vecspace_namecert_construction.tex`

Rationale:
This is a concrete LieAlgebraUp theorem in the existing concrete_instances surface: the paper already has adjoint-action definition, Jacobi derivation, commutator identity, and additive linearity, but not the scalar-linearity half of the bracket bilinearity consequence. It is distinct from existing BOARD entries and from the present LieAlgebra labels, while still landing safely in the current LieAlgebra chapter as a focused theorem target.

---

### B-402 - QuantumChannel finite convex-mixture closure

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (codex) |
| Object | QuantumChannel finite convex-mixture closure |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
Under QuantumChannelUp(H,K), if a finite affine spine of maps Phi_i are carried by QChan_{H,K} and the weights are nonnegative with total weight one, then the pointwise affine mixture Phi_mix is carried by QuantumChannelUp(H,K).

Local inputs:
- `papers/bedc/parts/concrete_instances/199_quantumchannel_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/198_densitymatrix_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/186_convexset_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/linearmap/the_certificate.tex`

Rationale:
This is a concrete closure theorem for the existing quantum-channel carrier, distinct from the current composition and density-image theorems. It lands directly in the QuantumChannelUp chapter and uses the existing linear-map and convex finite-affine-spine surfaces rather than adding a marker or verification-axis item.

---

### B-403 - QuantumChannel preserves density finite mixtures

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (codex) |
| Object | QuantumChannel preserves density finite mixtures |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |

Problem:
If QChan_{H,K}(Phi) and DensAffSpine_H(xs,lambda,rho_mix), then applying Phi entrywise gives the matching finite affine spine over K, with endpoint Phi(rho_mix) carried by DensityMatrixUp(K).

Local inputs:
- `papers/bedc/parts/concrete_instances/199_quantumchannel_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/198_densitymatrix_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/186_convexset_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/linearmap/the_certificate.tex`

Rationale:
This is not just the single-input density-image lemma: it records finite affine-mixture compatibility of a carried CPTP linear map. The target is concrete, local to the quantum-channel and density-matrix chapters, and distinct from channel composition closure and channel convex-mixture closure.

---

### B-404 - LieAlgebra adjoint acting-endpoint scalar linearity

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (codex) |
| Object | LieAlgebra adjoint acting-endpoint scalar linearity |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |

Problem:
Under a \(\LieAlgebraUp\) certificate, if \(r\) is carried by the scalar-field carrier and \(x,y\) are carried by the vector carrier, then \(\operatorname{ad}^{L}_{r\odot_L x}(y)\sim_L r\odot_L\operatorname{ad}^{L}_{x}(y)\).

Local inputs:
- `papers/bedc/parts/concrete_instances/119_liealgebra_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/22_vecspace_namecert_construction.tex`

Rationale:
This is a concrete Lie-algebra certificate law in the existing concrete_instances surface. The paper already has the acted-on endpoint scalar-linearity theorem for \(\operatorname{ad}^{L}_{x}(r\odot_L y)\), but the acting-endpoint scalar-linearity direction is semantically different and has no matching BOARD entry or paper theorem label. It should land safely in the existing Lie-algebra chapter and clarifies the bilateral bracket linearity exposed by the adjoint notation.

---

### B-405 - LieAlgebra adjoint linear endomap package

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (codex) |
| Object | LieAlgebra adjoint linear endomap package |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 6/10 |

Problem:
Under a \(\LieAlgebraUp\) certificate, if \(x\) is carried by the Lie-algebra vector carrier, then \(t\mapsto \operatorname{ad}^{L}_{x}(t)\) carries the \(\LinearMapUp\) endomap package on that vector carrier.

Local inputs:
- `papers/bedc/parts/concrete_instances/119_liealgebra_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/22_vecspace_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/linearmap/the_certificate.tex`
- `papers/bedc/parts/concrete_instances/linearmap/module_linearmap_certificates.tex`

Rationale:
This is a concrete bridge target from the Lie-algebra certificate to the existing LinearMap certificate surface. It is not a new abstract linear-map theory item: it packages the adjoint definition, classifier descent, additive preservation, scalar compatibility, and zero row into a named endomap certificate. Existing paper theorems supply component rows, but no current BOARD entry or paper label states the assembled certificate target.

---

### B-406 - Split epimorphisms are right-cancellative

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (codex) |
| Object | Split epimorphisms are right-cancellative |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |

Problem:
Under a CategoryUp certificate, if f:a->b has a split-epimorphism witness and u after f is hom-classifier equal to v after f for u,v:b->x, then u is hom-classifier equal to v.

Local inputs:
- `papers/bedc/parts/concrete_instances/36_category_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/category/carrier_and_hom_laws.tex`
- `papers/bedc/parts/concrete_instances/category/carrier_and_hom_laws_associativity.tex`

Rationale:
The claim is a concrete single-implication category theorem that belongs in the existing CategoryUp surface. It is not a notation variant of the current BOARD category entries, which focus on functor composition and natural transformation composition, and the paper-side coverage only shows split-epimorphism data rather than this cancellativity consequence. It is close to existing category composition and determinacy material, so the novelty is moderate rather than high, but it gives a useful standalone cancellation target from a named witness.

---

### B-407 - LieAlgebra adjoint acting-endpoint additive linearity

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (codex) |
| Object | LieAlgebra adjoint acting-endpoint additive linearity |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 7/10 |

Problem:
Under a LieAlgebraUp certificate, if x, z, and y are carried by the Lie-algebra vector carrier, then ad^L_{x +_L z}(y) is classified with ad^L_x(y) +_L ad^L_z(y).

Local inputs:
- `papers/bedc/parts/concrete_instances/119_liealgebra_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/22_vecspace_namecert_construction.tex`

Rationale:
This is a concrete theorem-level gap in the existing LieAlgebraUp surface: the paper already has adjoint additivity in the acted-on endpoint and scalar linearity in the acting endpoint, but not additive linearity in the acting endpoint. It lands cleanly in the existing Lie-algebra certificate chapter, is not a BOARD duplicate, is not marker-only or verification-axis work, and the landing file is well below the line cap.

---

### B-408 - Split epimorphism composition closure

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Split epimorphism composition closure |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
If f:a->b and g:b->c are split epimorphisms in a CategoryUp certificate and u is the displayed composite g after f with ell the displayed reverse composite of their right-inverse witnesses, then u is a split epimorphism with right-inverse ell.

Local inputs:
- `papers/bedc/parts/concrete_instances/36_category_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/category/carrier_and_hom_laws_associativity.tex`
- `papers/bedc/parts/concrete_instances/functor/pipeline_composite_extras.tex`

Rationale:
Category split-epimorphism witnesses are defined at papers/bedc/parts/concrete_instances/36_category_namecert_construction.tex:489-496, and category associative composition closure is available at papers/bedc/parts/concrete_instances/category/carrier_and_hom_laws_associativity.tex:1-8 and :21-29. The nearby dual-style result papers/bedc/parts/concrete_instances/functor/pipeline_composite_extras.tex:607-620 proves left cancellation for split monomorphisms, while papers/bedc/parts/concrete_instances/36_category_namecert_construction.tex:499-513 proves only right cancellation for a single split epimorphism. Focused rg for split epimorphism composition, composition of split epimorphisms, and split-epimorphism composition labels under papers/bedc/parts returned 0 hits; the split-epi hits are preservation or cancellation only, e.g. papers/bedc/parts/concrete_instances/functor/certificate_obligations.tex:486-523 and papers/bedc/parts/concrete_instances/36_category_namecert_construction.tex:499-513.

---

### B-409 - Graph three-step path reassociation

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Graph three-step path reassociation |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
If GraphEdge(h,k,hk), GraphEdge(k,l,kl), and GraphEdge(l,m,lm) hold under GraphUp, then the two three-step path endpoints produced by left and right association are hsame.

Local inputs:
- `papers/bedc/parts/concrete_instances/96_graph_namecert_construction.tex`
- `papers/bedc/parts/core/03_relational_extension_and_continuation.tex`

Rationale:
GraphEdge is defined by unary endpoints plus a Cont row at papers/bedc/parts/concrete_instances/96_graph_namecert_construction.tex:9-20. The chapter advertises two-step path composition in its core theorem list at :34-36 and proves exactly that at :183-198, then packages only unit rows and two-step path composition in the surface theorem at :219-230. Continuation associativity is available as an input at papers/bedc/parts/core/03_relational_extension_and_continuation.tex:749-760. Focused rg in the graph chapter for three-step, threefold, triple, and associat returned only prose lines :32, :256, and :336, and the graph theorem-label inventory contains no thm:graph three-step or associativity theorem.

---

### B-410 - Topology pullback arbitrary-union closure

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Topology pullback arbitrary-union closure |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 9/10 |

Problem:
If u is an indexed arbitrary-union witness for target public open rows and f:Y->X respects classifiers under the TopologyUp pullback setup, then the pulled-back row carries the pointwise existential union of the pulled-back predicates.

Local inputs:
- `papers/bedc/parts/concrete_instances/topology/namecert_construction_core.tex`
- `papers/bedc/parts/concrete_instances/topology/public_and_singleton_rows.tex`
- `papers/bedc/parts/concrete_instances/topology/pullback_open_rows.tex`

Rationale:
Indexed arbitrary-union witnesses are defined at papers/bedc/parts/concrete_instances/topology/namecert_construction_core.tex:149-160 and arbitrary-union closure is proved at :163-190. Public open rows explicitly allow arbitrary-union provenance at papers/bedc/parts/concrete_instances/topology/public_and_singleton_rows.tex:74-80. Pullback rows are defined at papers/bedc/parts/concrete_instances/topology/pullback_open_rows.tex:1-21, but that child file proves classifier transport at :24-39 and finite-meet pullback only at :41-57; its obligation surface at :59-71 names finite-meet preservation, not arbitrary unions. Focused rg for pullback arbitrary-union, arbitrary-union pullback, pullback union, and union pullback under papers/bedc/parts/concrete_instances/topology returned 0 hits.

---

### B-411 - ConvexSet intersection closure

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | ConvexSet intersection closure |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
If C and D are ConvexSetUp carriers over the same FieldUp and VecSpaceUp data and both satisfy the binary affine-combination row, then their pointwise intersection satisfies the same nonnegative unit-sum affine-combination closure row.

Local inputs:
- `papers/bedc/parts/concrete_instances/186_convexset_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/22_vecspace_namecert_construction.tex`

Rationale:
The binary affine-combination row for ConvexSetUp is defined at papers/bedc/parts/concrete_instances/186_convexset_namecert_construction.tex:12-30. Existing theorem sites prove midpoint closure at :32-45, affine-combination order symmetry at :60-99, and finite affine-spine closure from :101-160 onward. The theorem-label inventory for that file has only thm:convexset-midpoint-affine-combination-closure, thm:convexset-affine-combination-row-order-symmetric, and thm:convexset-finite-affine-spine-closure. Focused rg for convex intersection and intersection convex across concrete_instances returned only the polytope prose dependency at papers/bedc/parts/concrete_instances/187_polytope_namecert_construction.tex:4 and no ConvexSet theorem label.

---

### B-412 - Measure self-difference zero law

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Measure self-difference zero law |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
If A is a displayed measurable event and the MeasureUp relative-difference row is applied to the reflexive inclusion A subset A, then mu(A minus A) is classified with the RealUp additive zero under the target additive AbGroupUp row.

Local inputs:
- `papers/bedc/parts/concrete_instances/measure/carrier_surface_rows.tex`
- `papers/bedc/parts/concrete_instances/measure/relative_difference_rows.tex`
- `papers/bedc/parts/concrete_instances/group/16_group_certificate_tail.tex`

Rationale:
The complement/relative-difference row is defined at papers/bedc/parts/concrete_instances/measure/carrier_surface_rows.tex:53-63, including the event A minus B, disjointness, union readback, and a RealUp endpoint row. The measure chapter proves relative-difference decomposition at papers/bedc/parts/concrete_instances/measure/relative_difference_rows.tex:91-114 and relative-difference additivity at :116-130. The additive cancellation input needed to turn mu(A) sim mu(A)+mu(A minus A) into a zero conclusion is present as group left absorption at papers/bedc/parts/concrete_instances/group/16_group_certificate_tail.tex:1-10. Focused rg for self-difference, relative-difference zero, difference zero, and zero difference under the measure files returned 0 hits.

---

### B-413 - Matrix transpose preserves addition

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Matrix transpose preserves addition |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 6/10 |

Problem:
If R is a RingUp scalar source, A and B are carried n by m matrices, and matrix addition is pointwise, then transpose(A + B) is matrix-classified with transpose(A) + transpose(B) over the swapped dimensions.

Local inputs:
- `papers/bedc/parts/concrete_instances/matrix/finite_fold_multiplication_transpose.tex`
- `papers/bedc/parts/concrete_instances/matrix/finite_fold_multiplication_laws_distributivity_transpose.tex`
- `papers/bedc/parts/concrete_instances/matrix/the_certificate.tex`
- `papers/bedc/parts/concrete_instances/ring/18_ring_certificate_and_additive_laws.tex`

Rationale:
Belongs in the MatrixUp concrete body, preferably near the existing transpose file. This is a standard first-course linear algebra law for matrices over a ring. The transpose carrier is defined at papers/bedc/parts/concrete_instances/matrix/finite_fold_multiplication_transpose.tex:2, while existing transpose coverage proves product reversal and double-transpose involution at lines 11 and 60. Matrix addition is already treated pointwise with commutativity and associativity at papers/bedc/parts/concrete_instances/matrix/finite_fold_multiplication_laws_distributivity_transpose.tex:103 and :148, but a focused scan found no theorem label for transpose preserving addition. The proof is entrywise unfolding plus scalar classifier reflexivity, so it should close in one round.

---

### B-414 - FPS coefficientwise additive inverse

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | FPS coefficientwise additive inverse |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 6/10 |

Problem:
If R is a RingUp scalar source, F is a carried formal power series, and N is the coefficientwise scalar additive inverse of F, then F + N and N + F are FPS-classified with the zero series.

Local inputs:
- `papers/bedc/parts/concrete_instances/26_fps_ringup_tail.tex`
- `papers/bedc/parts/concrete_instances/26_fps_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/ring/18_ring_certificate_and_additive_laws.tex`

Rationale:
Belongs in the FormalPowerSeriesUp RingUp tail body file. The theorem is standard in any algebra treatment of formal power series: additive inverses are coefficientwise. The FPS pointwise additive monoid instance is defined at papers/bedc/parts/concrete_instances/26_fps_ringup_tail.tex:38 and its monoid laws are proved at line 52; pointwise addition is defined at papers/bedc/parts/concrete_instances/26_fps_namecert_construction.tex:391. Ring additive inverse support already appears at papers/bedc/parts/concrete_instances/ring/18_ring_certificate_and_additive_laws.tex:32. A focused grep found no FPS negation or additive-inverse theorem. The proof is coefficientwise and uses only scalar inverse laws plus the FPS pointwise classifier.

---

### B-415 - FPS zero series absorbs Cauchy product

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | FPS zero series absorbs Cauchy product |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 6/10 |

Problem:
If R is a RingUp scalar source, Z is the zero formal power series, and F is a carried formal power series, then Z times F and F times Z under the Cauchy product are FPS-classified with Z.

Local inputs:
- `papers/bedc/parts/concrete_instances/26_fps_ringup_tail.tex`
- `papers/bedc/parts/concrete_instances/26_fps_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/25_polynomial_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/ring/18_ring_zero_product_and_signed_square.tex`

Rationale:
Belongs in the FormalPowerSeriesUp RingUp tail body file. This is a standard formal power series ring law: the zero series is absorbing for Cauchy multiplication. The Cauchy coefficient spine is defined at papers/bedc/parts/concrete_instances/26_fps_namecert_construction.tex:326, and existing FPS product results cover congruence, commutativity, distributivity, associativity, and the constant coefficient, but not zero absorption. The scalar zero-product theorem is available in papers/bedc/parts/concrete_instances/ring/18_ring_zero_product_and_signed_square.tex:19, and the finite zero-summand fold theorem is available in papers/bedc/parts/concrete_instances/25_polynomial_namecert_construction.tex:560. The proof is pointwise: every Cauchy summand is scalar-classified as zero, the finite fold is zero, and the FPS classifier packages the coefficientwise result.

---

### B-416 - Filter principal suffix upward closure

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | Filter principal suffix upward closure |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
Under the principal-suffix FilterUp setup, if a point lies in the principal suffix generated by a base row and a continuation extends that point, then the extended point lies in the same principal suffix family.

Local inputs:
- `papers/bedc/parts/concrete_instances/71_filter_namecert_construction.tex`

Rationale:
The filter chapter has several principal-suffix intersection and determinacy theorems, but no labeled theorem isolates the upward-closure component advertised by the FilterUp surface. The claim is concrete, lands in an existing non-hub file below the line cap, and is distinct from existing BOARD targets and paper labels.

---

### B-417 - Affine mutual inclusion gives equal zero-loci

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | Affine mutual inclusion gives equal zero-loci |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 7/10 |

Problem:
Under the affine finite-family zero-locus setup, if EqFamIncl(F,G) and EqFamIncl(G,F), then for every point history x the predicates V(F)(x) and V(G)(x) are equivalent.

Local inputs:
- `papers/bedc/parts/concrete_instances/132_affinevar_namecert_construction.tex`

Rationale:
The paper already proves one-way contravariance of zero-loci under finite-family inclusion, but it does not state the bidirectional presentation-equivalence theorem. This is a compact, concrete comparison target for affine equation presentations and is not a BOARD duplicate.

---

### B-418 - Matching compatible union closure

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | Matching compatible union closure |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
Under a graph matching setup, if M and N are matching edge predicates and every cross pair of selected incident edges is edge-classifier equal, then M union N is again a matching edge predicate.

Local inputs:
- `papers/bedc/parts/concrete_instances/212_matching_namecert_construction.tex`

Rationale:
The matching chapter proves downward finite-subset closure but not a positive union closure under the exact compatibility condition needed to preserve the no-shared-vertex row. The target is a concrete closure theorem in a short landing file and does not overlap existing BOARD entries.

---

### B-419 - RandomVar preimage union exactness

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | RandomVar preimage union exactness |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 9/10 |

Problem:
Under a RandomVarUp map X, if B and C are target measurable events with a displayed disjoint binary-union row, then X^{-1}(B union C) is source-measurable, classifier-equal to X^{-1}(B) union X^{-1}(C), and preserves disjointness.

Local inputs:
- `papers/bedc/parts/concrete_instances/163_randomvar_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/164_distribution_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/measure/carrier_surface.tex`

Rationale:
The RandomVarUp chapter is skeletal while the DistributionUp chapter already relies on target-event preimage rows for total and empty events. Binary-union preimage exactness is a concrete missing RandomVar-side theorem needed before pushforward additivity claims become auditable.

---

### B-420 - Zero BHist measure relative-difference row

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | Zero BHist measure relative-difference row |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 6/10 |

Problem:
Under the concrete zero BHist measure surface, if A and B are displayed measurable events with B subset A, then A setminus B is accepted by the zero surface and its measure endpoint is classified as 0_R.

Local inputs:
- `papers/bedc/parts/concrete_instances/measure/zero_bhist_surface.tex`
- `papers/bedc/parts/concrete_instances/measure/carrier_surface_rows.tex`
- `papers/bedc/parts/concrete_instances/measure/relative_difference_rows.tex`

Rationale:
The measure surface contains general relative-difference rows and the zero BHist surface proves carrier stability and sigma-additivity, but there is no labeled zero-instance theorem exhibiting the relative-difference row and constant-zero endpoint. This is a narrow concrete coverage target rather than an abstract transport restatement.

---

### B-421 - ConvexSet finite intersection closure

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (codex) |
| Object | ConvexSet finite intersection closure |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |

Problem:
Under shared FieldUp and VecSpaceUp data, if every member of a finite family is a ConvexSetUp carrier satisfying the binary affine-combination row, then their pointwise finite intersection also satisfies the binary affine-combination row.

Local inputs:
- `papers/bedc/parts/concrete_instances`

Rationale:
This is a concrete closure theorem in the existing ConvexSetUp surface, not a marker or verification-axis item. Existing labels define the intersection carrier and affine-combination row, but the proposed target is the proof that finite intersections preserve that row, which is distinct enough to deserve one BOARD slot. The two proposed titles are duplicates, so only the clearer finite-family formulation is retained.

---

### B-422 - InnerProduct orthogonality symmetry

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | InnerProduct orthogonality symmetry |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
If x and y are carried endpoints of an InnerProductUp BHist carrier and x perp_I y, then y perp_I x under the retained scalar-zero classifier.

Local inputs:
- `papers/bedc/parts/concrete_instances/64_innerproduct_namecert_construction.tex`

Rationale:
InnerProduct/Hilbert geometry is under-represented in the BOARD scan, while the paper has enough local structure for a precise theorem. The carrier records conjugate symmetry and scalar-zero exactness at papers/bedc/parts/concrete_instances/64_innerproduct_namecert_construction.tex:23-31; orthogonality is defined as scalar-zero classification of the inner-product endpoint at :324-337; the only companion theorems are zero-left, zero-right, and representative transport at :339-407. A focused grep found no labeled orthogonality-symmetry theorem and no BOARD entry for InnerProduct or orthogonality.

---

### B-423 - AbelianCat hom zero morphism uniqueness

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | AbelianCat hom zero morphism uniqueness |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
If a hom row H(A,B) of an AbelianCatUp surface carries a morphism u that is a two-sided additive identity for hom addition, then u is hom-classified with the displayed zero morphism 0_A,B.

Local inputs:
- `papers/bedc/parts/concrete_instances/154_abeliancat_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/17_abgroup_namecert_construction.tex`

Rationale:
AbelianCatUp has no BOARD target hits, but its paper surface is substantial and currently mostly obligation packaging. The carrier selects a visible zero morphism row at papers/bedc/parts/concrete_instances/154_abeliancat_namecert_construction.tex:25 and hom-wise AbGroupUp enrichment at :29-31. The existing additive/biproduct theorem reads the displayed zero row into biproduct equations at :211-233, but focused grep found no zero-morphism uniqueness theorem. This is a concrete hom-level consequence using the already-developed AbGroup identity/cancellation infrastructure rather than another carrier transport package.

---

### B-424 - DerivedCat roof identity unit laws

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | DerivedCat roof identity unit laws |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 9/10 |

Problem:
If a DerivedCatUp roof ledger represents a morphism r, then composing r with the displayed identity roof on either side is classified with r by the generated zigzag classifier.

Local inputs:
- `papers/bedc/parts/concrete_instances/138_derivedcat_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/36_category_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/77_cohomology_namecert_construction.tex`

Rationale:
DerivedCatUp is a quiet homological-algebra island with no BOARD hits. The file defines the visible localization interface, generated zigzag classifier, and roof composition obligations at papers/bedc/parts/concrete_instances/138_derivedcat_namecert_construction.tex:9-16. It proves composition descent along classifier-equivalent roofs at :47-57, but there is no companion identity-unit theorem for represented roofs. The claim is a local categorical law for the existing localization carrier, not a new derived-category survey.

---

### B-425 - RealAnalytic sine addition formula row

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | RealAnalytic sine addition formula row |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
If supplied RealAlgOrder rows, trigonometric limit witnesses, product-stability rows, and regular-rational Cauchy-product comparisons are present for x and y, then the sine endpoint for x+y is RealClassifier-equal to sin(x)cos(y)+cos(x)sin(y).

Local inputs:
- `papers/bedc/parts/concrete_instances/52_real_analytic_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/13_real_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/104_streamname_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/12_rat_namecert_construction.tex`

Rationale:
The RealAnalytic chapter is contentful but still has a missing middle row: it defines sine and cosine by supplied limit witnesses at papers/bedc/parts/concrete_instances/52_real_analytic_namecert_construction.tex:337-338, proves Pythagorean and pi-multiple zero rows, and explicitly assumes sine/cosine addition-formula rows inside the pi-multiple proof at papers/bedc/parts/concrete_instances/52_real_analytic_namecert_construction.tex:352-354. A focused BOARD/state scan found no RealAnalytic trig-addition target, so a single sine-addition implication would fill an advertised local obligation without duplicating the existing Pythagorean or pi-multiple theorems.

---

### B-426 - ShortestPath prefix optimality

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | ShortestPath prefix optimality |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 9/10 |

Problem:
If a nonnegative-weight ShortestPathUp witness certifies a path p as minimum from u to v and p factors through w as p1 followed by p2, then p1 is a ShortestPathUp witness from u to w.

Local inputs:
- `papers/bedc/parts/concrete_instances/214_shortestpath_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/96_graph_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/13_real_namecert_construction.tex`

Rationale:
The algorithmic graph slice is essentially unopened: papers/bedc/parts/concrete_instances/214_shortestpath_namecert_construction.tex:4 promises weighted graphs, nonnegative weights, minimum total-weight paths, and Dijkstra/Bellman-Ford correctness, while the file only exposes carrier and certificate section labels at papers/bedc/parts/concrete_instances/214_shortestpath_namecert_construction.tex:7 and papers/bedc/parts/concrete_instances/214_shortestpath_namecert_construction.tex:10. Focused BOARD/state grep found no shortest-path target. Prefix optimality is a concrete first theorem for the advertised minimum-path classifier and stays inside the existing GraphUp/RealUp dependencies.

---

### B-427 - Simplicial face-chain closure

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Simplicial face-chain closure |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 9/10 |

Problem:
If K is a SimplicialComplexUp carrier, sigma is in K, tau is a face of sigma, and rho is a face of tau, then rho is in K and rho is a face of sigma.

Local inputs:
- `papers/bedc/parts/concrete_instances/216_simplicialcomplex_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/90_finset_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/28_poset_namecert_construction.tex`

Rationale:
SimplicialComplexUp is a structural blindspot: papers/bedc/parts/concrete_instances/216_simplicialcomplex_namecert_construction.tex:4 states finite simplices closed under faces with face-incidence and dimension-grading data, but the chapter currently stops at section labels at papers/bedc/parts/concrete_instances/216_simplicialcomplex_namecert_construction.tex:7 and papers/bedc/parts/concrete_instances/216_simplicialcomplex_namecert_construction.tex:10. A focused BOARD/state scan found no simplicial-complex target. The proposed face-chain implication uses the named FinSetUp and PosetUp dependencies and is stronger than merely restating a one-step face-closure field.

---

### B-428 - Quadrature exactness degree weakening

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Quadrature exactness degree weakening |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 9/10 |

Problem:
If a QuadratureUp finite weighted rule is exact for every polynomial of degree at most d and e <= d, then the same rule is exact for every polynomial of degree at most e.

Local inputs:
- `papers/bedc/parts/concrete_instances/205_quadrature_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/101_integral_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/25_polynomial_literal_addtrim_eval.tex`
- `papers/bedc/parts/concrete_instances/90_finset_namecert_construction.tex`

Rationale:
QuadratureUp is another unserved numerical-analysis interface: papers/bedc/parts/concrete_instances/205_quadrature_namecert_construction.tex:4 says the classifier is exactness degree for finite weighted sums approximating integrals, and the chapter has only carrier/certificate section labels at papers/bedc/parts/concrete_instances/205_quadrature_namecert_construction.tex:7 and papers/bedc/parts/concrete_instances/205_quadrature_namecert_construction.tex:10. Focused BOARD/state grep found no quadrature target. Downward closure of exactness degree is a compact monotonicity theorem that directly tests the advertised classifier without opening a broad numerical-methods survey.

---

### B-429 - LP feasible weak duality

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | LP feasible weak duality |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 9/10 |

Problem:
If primal and dual LPDualityUp rows over an ordered field have feasible witnesses x and y, then the primal objective value at x is less than or classifier-equal to the dual objective value at y.

Local inputs:
- `papers/bedc/parts/concrete_instances/213_lpduality_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/186_convexset_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/187_polytope_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/field/20_field_laws_and_certificate.tex`
- `papers/bedc/parts/concrete_instances/29_totalorder_namecert_construction.tex`

Rationale:
LPDualityUp advertises strong duality and complementary slackness over an ordered field at papers/bedc/parts/concrete_instances/213_lpduality_namecert_construction.tex:4, but focused BOARD/state grep found no LPDuality target and the local chapter is only a 10-line skeleton. Weak duality is the missing middle implication before any strong-duality certificate can be meaningful, and it is local to the existing ConvexSetUp, PolytopeUp, FieldUp, and TotalOrderUp dependencies.

---

### B-430 - DerivedCat roof associativity classifier law

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (codex) |
| Object | DerivedCat roof associativity classifier law |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |

Problem:
Under a DerivedCatUp visible localization setup, if three displayed roof ledger rows are composable and the two left- and right-associated composite roof ledgers are formed, then those two composite ledgers are classified by the generated zigzag classifier.

Local inputs:
- `papers/bedc/parts/concrete_instances/138_derivedcat_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/36_category_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/77_cohomology_namecert_construction.tex`

Rationale:
The claim is a concrete categorical law for the existing DerivedCatUp localization surface: the paper already defines generated zigzag classifiers, roof ledgers, composition descent, and roof identity laws, but it does not state the companion associativity law for three displayed roof composites. It is distinct from the existing functor/category associativity BOARD entries because it lands at the derived-category roof-ledger layer and uses quasi-isomorphism zigzag classification, not only ordinary hom-carrier composition.

---

### B-431 - RealAnalytic cosine addition formula row

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (codex) |
| Object | RealAnalytic cosine addition formula row |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 7/10 |

Problem:
If z is the RealAlgOrder endpoint for x+y and the supplied trigonometric limit witnesses, RealAlgOrder product/difference rows, product-stability rows, even-parity regular-rational Cauchy-product comparison, and limit-uniqueness classifier rows are present, then RealClassifier(c_z, c_x*c_y - s_x*s_y) for Cos(z,c_z), Cos(x,c_x), Cos(y,c_y), Sin(x,s_x), and Sin(y,s_y).

Local inputs:
- `papers/bedc/parts/concrete_instances/52_real_analytic_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/real/13_real_alg_order_interface.tex`

Rationale:
This is a concrete theorem-row target in the existing RealAnalyticUp surface. The paper already has the sine addition row and later assumes both sine and cosine addition-formula rows, but the cosine counterpart is not present as its own labeled theorem. It is not a marker, closurestatus, or abstract transport echo, and the landing file is a non-hub concrete_instances file well below the line cap. The two codex proposals are the same target, with the accepted wording using the sharper even-parity Cauchy-product comparison.

---

### B-432 - Simplicial face-chain dimension monotonicity

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (codex) |
| Object | Simplicial face-chain dimension monotonicity |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |

Problem:
Under a SimplicialComplexUp finite face carrier K with dimension-grading data, Simplex_K(sigma) and Face_K(rho,tau) and Face_K(tau,sigma) imply dim_K(rho) <= dim_K(tau) and dim_K(tau) <= dim_K(sigma).

Local inputs:
- `papers/bedc/parts/concrete_instances/216_simplicialcomplex_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/28_poset_namecert_construction.tex`

Rationale:
The target lands directly in the existing SimplicialComplexUp concrete-instance chapter: the current surface already has face-chain closure and mentions dimension-grading data, but it has no labeled theorem extracting monotonicity along a two-step face chain. It is not a BOARD duplicate and is distinct from the existing face-chain closure theorem because it concerns the dimension row rather than carrier closure or face transitivity.

---

### B-433 - Measure binary union subadditivity

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Measure binary union subadditivity |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
If A and B are displayed measurable events in a MeasureUp carrier with displayed binary union U, the relative-difference row for U\A, finite disjoint-union additivity, nonnegative measure values, and the RealAlgOrder additive order row, then mu(U) <=_R mu(A)+mu(B).

Local inputs:
- `papers/bedc/parts/concrete_instances/measure/relative_difference_rows.tex`
- `papers/bedc/parts/concrete_instances/measure/certificate_theorems.tex`
- `papers/bedc/parts/concrete_instances/measure/carrier_surface_rows.tex`

Rationale:
The MeasureUp surface explicitly exposes binary union, complement/relative-difference, nonnegative value, and RealUp measure endpoint rows at papers/bedc/parts/concrete_instances/measure/carrier_surface_rows.tex:36-50 and papers/bedc/parts/concrete_instances/measure/carrier_surface_rows.tex:53-71. Existing consequences prove finite disjoint-union additivity at papers/bedc/parts/concrete_instances/measure/certificate_theorems.tex:167-173, monotonicity under inclusion at papers/bedc/parts/concrete_instances/measure/relative_difference_rows.tex:26-36, and relative-difference additivity at papers/bedc/parts/concrete_instances/measure/relative_difference_rows.tex:116-130, but a focused grep for subadd, Boole, countable sub, finite sub, union bound, and union-bound under the measure files returned 0 hits. This is a concrete inequality theorem about an existing MeasureUp object, naturally landing in the small relative-difference child file rather than the measure hub.

---

### B-434 - RandomVar preimage relative-difference exactness

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | RandomVar preimage relative-difference exactness |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
If B subset A are displayed target measurable events and X is a RandomVarUp map with measurable-preimage rows, then X^{-1}(A\B) is source-event-classifier equal to X^{-1}(A)\X^{-1}(B) with the source MeasureUp relative-difference ledger.

Local inputs:
- `papers/bedc/parts/concrete_instances/163_randomvar_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/measure/carrier_surface_rows.tex`
- `papers/bedc/parts/concrete_instances/measure/relative_difference_rows.tex`

Rationale:
RandomVarUp has exactly one theorem label, the disjoint binary-union preimage exactness theorem at papers/bedc/parts/concrete_instances/163_randomvar_namecert_construction.tex:12-27. MeasureUp separately defines the complement/relative-difference row at papers/bedc/parts/concrete_instances/measure/carrier_surface_rows.tex:53-71 and proves relative-difference disjoint decomposition at papers/bedc/parts/concrete_instances/measure/relative_difference_rows.tex:91-100. Focused grep for randomvar/preimage relative or difference returned only a proof sentence in the measure relative-difference transport theorem and no RandomVar theorem, so this is an open concrete closure property of the random-variable preimage operation rather than a marker or transport-only target.

---

### B-435 - ProbSpace monotone event bounds

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | ProbSpace monotone event bounds |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
If A subset B subset Omega are displayed events in a ProbSpaceUp carrier, then mu(A) <=_R mu(B) and mu(B) <=_R 1_R under the inherited MeasureUp monotonicity and total-mass row.

Local inputs:
- `papers/bedc/parts/concrete_instances/162_probspace_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/measure/relative_difference_rows.tex`
- `papers/bedc/parts/concrete_instances/measure/downstream_rows.tex`
- `papers/bedc/parts/concrete_instances/measure/analysis_seed_substrate.tex`

Rationale:
ProbSpaceUp currently proves complement mass additivity and complement mass as one minus event mass at papers/bedc/parts/concrete_instances/162_probspace_namecert_construction.tex:12-23 and 47-57. The probability substrate states that ProbSpaceUp adds only a total-event row and unit-mass endpoint row on top of MeasureUp at papers/bedc/parts/concrete_instances/measure/analysis_seed_substrate.tex:44-52, while the normalization row is stated at papers/bedc/parts/concrete_instances/measure/downstream_rows.tex:65-80 and MeasureUp monotonicity is available at papers/bedc/parts/concrete_instances/measure/relative_difference_rows.tex:26-36. Focused grep for probability/probspace monotone, bound, event bound, and inclusion returned only an unrelated probability-boundary sentence, and the probspace label inventory has only the two complement-mass theorems, so the inclusion-to-unit bound is a genuine missing probability consequence.

---

### B-436 - MonoidalCat tensor preserves composition

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | MonoidalCat tensor preserves composition |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
Under the singleton MonoidalCatUp tensor instance, composable hom rows f,f' and g,g' imply (f \otimes g) followed by (f' \otimes g') is classifier-equal to (f' \circ f) \otimes (g' \circ g).

Local inputs:
- `papers/bedc/parts/concrete_instances/159_monoidalcat_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/category/carrier_and_hom_laws.tex`

Rationale:
This is a concrete missing bifunctoriality law in an existing MonoidalCat chapter, not a marker or verification-axis item. It is distinct from existing BOARD category/functor/natural-transformation targets because it concerns tensor interchange inside the monoidal category certificate surface.

---

### B-437 - AbelianCat kernel and cokernel factor uniqueness

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | AbelianCat kernel and cokernel factor uniqueness |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
For an AbelianCatUp kernel-cokernel carrier, two factor arrows through the same kernel row that classify to the same zeroing morphism are classifier-equal, and dually for cokernel cofactor arrows.

Local inputs:
- `papers/bedc/parts/concrete_instances/154_abeliancat_namecert_construction.tex`

Rationale:
This is a concrete uniqueness target for an existing AbelianCat certificate surface. It is not covered by the listed paper labels, and it is distinct from existing BOARD entries because it targets universal factor/cofactor uniqueness rather than functorial composition or general category carrier closure.

---

### B-438 - Distribution pushforward finite additivity

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | Distribution pushforward finite additivity |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
If X is a carried RandomVarUp map and B,C are disjoint target measurable events with union U, then the DistributionUp pushforward satisfies mu_X(U) classifier-equal to mu_X(B)+mu_X(C).

Local inputs:
- `papers/bedc/parts/concrete_instances/164_distribution_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/163_randomvar_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/measure/certificate_theorems.tex`

Rationale:
This fills a direct measure-certificate gap for DistributionUp by combining existing RandomVar preimage union exactness with Measure finite disjoint-union additivity. It is a concrete closure theorem and has no close duplicate among existing BOARD entries or listed paper labels.

---

### B-439 - RandomVar preimage complement exactness

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | RandomVar preimage complement exactness |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |

Problem:
If X is a carried RandomVarUp map and B^c is the target complement or relative-difference row for B, then X^{-1}(B^c) is source-event-classifier equal to the corresponding source complement or relative difference of X^{-1}(B).

Local inputs:
- `papers/bedc/parts/concrete_instances/163_randomvar_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/measure/carrier_surface_rows.tex`
- `papers/bedc/parts/concrete_instances/measure/relative_difference_rows.tex`

Rationale:
This is a concrete missing companion to the existing RandomVar preimage union exactness theorem. It stays within the measurable-preimage certificate surface, is not already named in the provided paper coverage, and is distinct from existing BOARD targets.

---

### B-440 - CompleteMetric limit tolerance weakening

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | CompleteMetric limit tolerance weakening |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |

Problem:
If CompleteMetricLimitWitness(X,s,mu,l,L) holds and convergence bounds are weakened by supplied RatUp comparisons epsilon <= epsilon', then the same data repack as a CompleteMetricLimitWitness with weakened bound ledgers.

Local inputs:
- `papers/bedc/parts/concrete_instances/106_completemetric_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/105_totallybounded_namecert_construction.tex`

Rationale:
This is a focused monotonicity theorem for the CompleteMetric witness interface, analogous to an existing TotallyBounded result but not a duplicate of it. It is a concrete certificate-repacking result with clear local inputs and no matching listed paper label.

---

### B-441 - InnerProduct orthogonal additivity

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | InnerProduct orthogonal additivity |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 7/10 |

Problem:
Under an InnerProductUp BHist source, if x, y, and z are carried and x is orthogonal to y and to z, then x is orthogonal to y + z under the retained scalar-zero classifier.

Local inputs:
- `papers/bedc/parts/concrete_instances/64_innerproduct_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/22_vecspace_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/ring/18_ring_zero_product_and_signed_square.tex`

Rationale:
This belongs in the inner-product chapter. Orthogonal complements being closed under addition is a standard introductory linear algebra theorem. The chapter already has the carrier/source setup, row-linearity theorem, and orthogonality definition at papers/bedc/parts/concrete_instances/64_innerproduct_namecert_construction.tex:9, :59, :125, and :324, plus zero and transport/symmetry facts at :339, :363, :387, and :568. Focused scans find no theorem labelled for orthogonal additivity or subspace closure. The proof should close in 1-3 rounds by applying the existing row-linearity theorem and scalar zero-addition laws rather than building new infrastructure.

---

### B-442 - InnerProduct orthogonal scalar closure

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | InnerProduct orthogonal scalar closure |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 6/10 |

Problem:
Under an InnerProductUp BHist source, if x and y are carried, scalar r is carried, and x is orthogonal to y, then x is orthogonal to r * y under the retained scalar-zero classifier.

Local inputs:
- `papers/bedc/parts/concrete_instances/64_innerproduct_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/22_vecspace_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/ring/18_ring_zero_product_and_signed_square.tex`

Rationale:
This is another small textbook linear algebra lemma for the inner-product chapter: orthogonal complements are closed under scalar multiplication. The needed objects are already present: scalar compatibility is included in the inner-product row-linearity interface around papers/bedc/parts/concrete_instances/64_innerproduct_namecert_construction.tex:125, and orthogonality is defined at :324. Existing labelled theorems cover zero, transport, and symmetry, but focused scans show no theorem for scalar closure of orthogonality. The proof should only need the existing scalar-compatibility row and ring zero-absorption facts.

---

### B-443 - Lie bracket left-zero annihilation

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Lie bracket left-zero annihilation |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 7/10 |

Problem:
Under a LieAlgebraUp certificate, if x is carried by the vector carrier, then [0_L, x]_L is carried and classifier-equal to 0_L.

Local inputs:
- `papers/bedc/parts/concrete_instances/119_liealgebra_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/22_vecspace_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/21_module_namecert_construction.tex`

Rationale:
This belongs in the Lie algebra chapter and is a standard first consequence of bilinearity. The chapter introduces the Lie algebra as a vector space with an antisymmetric bilinear bracket at papers/bedc/parts/concrete_instances/119_liealgebra_namecert_construction.tex:4 and has bracket-linearity theorems at :113, :135, :158, :180, and :238. Focused scans for zero-bracket and bracket-annihilation find no labelled theorem for [0, x] = 0. The proof is a small bilinearity/cancellation argument using already available vector-space and module zero infrastructure.

---

### B-444 - LP weak-duality equality gives optimality

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | LP weak-duality equality gives optimality |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
Under the LPDualityUp finite ordered-field row, if x is primal feasible, y is dual feasible, and PrObj(x) is scalar-classifier equal to DuObj(y), then every primal feasible x' has PrObj(x') <= PrObj(x) and every dual feasible y' has DuObj(y) <= DuObj(y').

Local inputs:
- `papers/bedc/parts/concrete_instances/213_lpduality_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/29_totalorder_namecert_construction.tex`

Rationale:
This belongs in the LP duality chapter. In standard linear programming texts, weak duality is immediately followed by the equality-implies-optimality corollary. The chapter defines the primal/dual feasibility and objective interface at papers/bedc/parts/concrete_instances/213_lpduality_namecert_construction.tex:12 and proves weak duality at :72, while focused scans show no LP optimality theorem. The proof should close by invoking thm:lpduality-feasible-weak-duality twice and transporting through the existing ordered scalar classifier.

---

### B-445 - ErrorCode smaller-radius uniqueness

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | ErrorCode smaller-radius uniqueness |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 6/10 |

Problem:
Under an ErrorCodeUp certificate with decoding radius t = floor((d - 1) / 2), if s <= t and two codewords are both within Hamming distance s of the same received word, then the two codewords are code-classifier equal.

Local inputs:
- `papers/bedc/parts/concrete_instances/219_errorcode_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/04_nat_namecert_construction.tex`

Rationale:
This belongs in the error-correcting-code chapter. A standard coding theory corollary says a code that uniquely decodes up to radius t also uniquely decodes at every smaller radius. The chapter defines the decoding radius at papers/bedc/parts/concrete_instances/219_errorcode_namecert_construction.tex:26 and proves exact-radius uniqueness at :42, but focused scans find no smaller-radius or monotonicity corollary. The proof should be short: use Nat order transitivity to upgrade both distance bounds from s to t, then apply thm:errorcode-unique-decoding-radius.

---

### B-446 - InnerProduct orthogonal additive inverse closure

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (codex) |
| Object | InnerProduct orthogonal additive inverse closure |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |

Problem:
Under an \InnerProductUp setup, if carried vector endpoints satisfy x\perp_I y, then the displayed vector inverse -_V y is carried and x\perp_I (-_V y) under the retained scalar-zero classifier.

Local inputs:
- `papers/bedc/parts/concrete_instances/64_innerproduct_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/22_vecspace_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/20_field_namecert_construction.tex`

Rationale:
The target is a concrete closure theorem for the existing InnerProduct orthogonality surface. It is not a BOARD duplicate and is not already present as a labeled theorem: the paper has zero-left, zero-right, transport, symmetry, and additivity rows, but no additive-inverse closure row for orthogonality. The proof should land directly from the VecSpace inverse row, inner-product sesquilinearity, and scalar zero stability, so it is scoped and useful without being a marker or verification-axis item.

---

### B-447 - LP complementary slackness gives objective equality

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | LP complementary slackness gives objective equality |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 9/10 |

Problem:
If an LPDualityUp ordered-field row has primal feasible x and dual feasible y, and the two termwise slack families satisfy c_j*x_j ~ beta_j(y)*x_j for all columns and y_i*alpha_i(x) ~ y_i*b_i for all rows, then PrObj(x) ~ DuObj(y) and the existing equality-optimality corollary applies under the same setup.

Local inputs:
- `papers/bedc/parts/concrete_instances/213_lpduality_namecert_construction.tex`

Rationale:
The LP row defines alpha_i, beta_j, feasibility, and objectives at papers/bedc/parts/concrete_instances/213_lpduality_namecert_construction.tex:38-68; weak duality is proved at lines 72-136 and equality-implies-optimality is only a corollary assuming objective equality at lines 138-187. Focused rg for "slack|complementary|strong[- ]duality" in this file returned only the introductory line 4, with no labeled theorem or lemma deriving equality from complementary slackness. This is not hidden under weak duality because the existing corollary consumes equality but does not prove it from rowwise slack equalities; the file is 187 lines and is a concrete body file.

---

### B-448 - Simplicial intersection carrier is face closed

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Simplicial intersection carrier is face closed |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
If K and L are SimplicialComplexUp finite face carriers over the same simplex source and face relation, and J is a finite spine enumeration of the pointwise intersection Simplex_K and Simplex_L, then J is face closed and carries the inherited face transitivity under the same setup.

Local inputs:
- `papers/bedc/parts/concrete_instances/216_simplicialcomplex_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/90_finset_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/28_poset_namecert_construction.tex`

Rationale:
The simplicial carrier records finite simplex enumeration, PosetUp face transitivity, and face closure at papers/bedc/parts/concrete_instances/216_simplicialcomplex_namecert_construction.tex:12-39; existing theorems prove face-chain closure and dimension monotonicity for one carrier only at lines 41-78 and 98-140. Focused rg for "intersection|subcomplex" in the simplicial-complex file returned 0 hits, and the existing labels in the file are only the two chain/monotonicity claims. This is a concrete closure theorem for an existing object, not a parameter-transport echo, and the target file is 140 lines.

---

### B-449 - Quantum identity channel is CPTP

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Quantum identity channel is CPTP |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
If H is a HilbertUp carrier and id_H is the module LinearMapUp identity on TC(H), then id_H is carried by QChan_{H,H} and sends every Dens_H input to a Dens_H output under QuantumChannelUp.

Local inputs:
- `papers/bedc/parts/concrete_instances/199_quantumchannel_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/198_densitymatrix_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/linearmap/module_linearmap_certificates.tex`

Rationale:
QuantumChannelUp is defined as a LinearMapUp map plus complete-positivity and trace-preservation rows at papers/bedc/parts/concrete_instances/199_quantumchannel_namecert_construction.tex:23-34; the file proves density-matrix image at lines 36-57, composition closure at lines 59-118, and convex mixture closure later, but no identity-channel theorem. Focused rg for "identity.*quantum|quantum.*identity|identity channel|QChan.*id|cptp.*identity" across papers/bedc/parts/concrete_instances and lean4/BEDC returned only an unrelated "unit-sum identity" hit at line 219. The needed LinearMap identity certificate exists separately at papers/bedc/parts/concrete_instances/linearmap/module_linearmap_certificates.tex:189-199, so this is a concrete missing instance, not a marker-only task; the target file is 278 lines.

---

### B-450 - Matroid restrictions compose to direct restriction

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Matroid restrictions compose to direct restriction |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 7/10 |
| Novelty | 8/10 |

Problem:
If K is a finite subset of the matroid ground E, L is a finite subset of K, Ind_{M|K} is the restriction of Ind_M to K, and Ind_{(M|K)|L} is the restriction of Ind_{M|K} to L, then Ind_{(M|K)|L}(I) iff Ind_M(I) and FinSetSubset(I,L), hence the direct restriction rows to L hold under the same MatroidUp setup.

Local inputs:
- `papers/bedc/parts/concrete_instances/180_matroid_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/90_finset_namecert_construction.tex`
- `lean4/BEDC/Derived/MatroidUp.lean`

Rationale:
The restriction row package is defined at papers/bedc/parts/concrete_instances/180_matroid_namecert_construction.tex:123-177, and the existing restriction certificate proves one-step restriction rows at lines 203-269. Focused rg for "restriction.*trans|restrict.*restrict|double.*restrict|direct.*restrict|restriction.*compose|compose.*restriction" in the matroid paper file and lean4/BEDC returned only the definition/proof lines in this file and unrelated ContinuousUp restriction-transitivity theorems, with no matroid restriction-composition theorem. The claim is a concrete composition law for the matroid restriction constructor using finite-subset composition, not merely transport of an arbitrary property; the target file is 269 lines.

---

### B-451 - Quadrature degree-bound comparison is transitive

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Quadrature degree-bound comparison is transitive |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 7/10 |
| Novelty | 7/10 |

Problem:
If DegBoundLe(e,d) and DegBoundLe(d,c) hold for unary quadrature degree bounds, then DegBoundLe(e,c) holds under the QuadratureUp exactness-degree setup.

Local inputs:
- `papers/bedc/parts/concrete_instances/205_quadrature_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/25_polynomial_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/101_integral_namecert_construction.tex`

Rationale:
Quadrature defines PolyDegLe, QuadratureExactUpTo, and DegBoundLe at papers/bedc/parts/concrete_instances/205_quadrature_namecert_construction.tex:12-57; it proves degree-window inclusion from one DegBoundLe at lines 59-74 and exactness weakening at lines 76-99. Focused rg for "DegBoundLe.*trans|degree.*trans|transitive.*degree|degree.*preorder|exactness.*equiv|mutual.*degree|Quadrature.*trans" in the quadrature file and lean4/BEDC returned no quadrature theorem, only an unrelated NumField degree-one theorem. This is a small but genuine structural theorem for the exactness-degree classifier, and the target file is 99 lines.

---

### B-452 - ODE local-flow concatenation endpoint determinacy

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | ODE local-flow concatenation endpoint determinacy |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 9/10 |

Problem:
If two OdeUp local-flow rows compose through a shared middle endpoint and a direct local-flow row uses the same initial data and Lipschitz/vector-field ledger as the composed Picard route, then the direct endpoint and the composed endpoint are Banach-classifier equal.

Local inputs:
- `papers/bedc/parts/concrete_instances/171_ode_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/100_derivative_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/68_banach_namecert_construction.tex`
- `papers/bedc/parts/core/03_relational_extension_and_continuation.tex`

Rationale:
ODE is a mostly untouched dynamics surface in the deep-loop scan: focused BOARD/state grep for OdeUp, ODE, ordinary-differential, and local-flow returned no target hits. The file defines local-flow rows with initial/end time-state cells and Picard/limit continuations at papers/bedc/parts/concrete_instances/171_ode_namecert_construction.tex:9-40, proves adjacent Picard packages compose inside scope at :71-99, and separately proves endpoint determinacy from shared initial data and Lipschitz ledger at :101-129. No theorem combines these into the natural concatenation endpoint law, so this is a missing middle step rather than a new abstract transport schema.

---

### B-453 - Sheaf point-germ comparison transitivity

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Sheaf point-germ comparison transitivity |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
If point-germ rows a and b over the same BHist point compare on one displayed common neighborhood and b and c compare on another, then a and c compare on the finite-intersection refinement neighborhood after restriction.

Local inputs:
- `papers/bedc/parts/concrete_instances/129_sheaf_point_germ_ledger.tex`
- `papers/bedc/parts/concrete_instances/sheaf/01_carrier_and_cover_surface.tex`
- `papers/bedc/parts/concrete_instances/sheaf/03_gluing_classifier_rows.tex`
- `papers/bedc/parts/concrete_instances/topology/namecert_construction_core.tex`

Rationale:
Sheaf work on BOARD covers gluing uniqueness and global-restriction compatibility, but the point-germ subarea remains only scoped/readback. The point-germ relation is defined by common neighborhoods and one restricted section-classifier row at papers/bedc/parts/concrete_instances/129_sheaf_point_germ_ledger.tex:5-21; the existing theorems prove carrier scope and restriction/gluing readback at :24-79. Focused grep for point-germ transitivity or equivalence found no theorem label, while sheaf/root_threshold_certificate_surface.tex:3-15 says the point-germ ledger is exported to downstream threshold certificates. Transitivity is the concrete classifier law needed before treating these comparisons as a germ equality surface.

---

### B-454 - Weyl reflection words preserve roots

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Weyl reflection words preserve roots |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 7/10 |
| Novelty | 10/10 |

Problem:
If a WeylGroupUp element is represented by a finite word of simple-root reflections from a RootSystemUp carrier, then acting on any carried root yields another root carried by the same RootSystemUp carrier.

Local inputs:
- `papers/bedc/parts/concrete_instances/122_rootsystem_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/123_weylgroup_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/64_innerproduct_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/90_finset_namecert_construction.tex`

Rationale:
Root-system and Weyl-group territory is under-represented: BOARD/state hits mention RootSystemUp only as a dependency of InnerProduct-side targets, with no direct RootSystemUp or WeylGroupUp target. The root-system file states that RootSystemUp is a finite set of nonzero vectors closed under generated reflections at papers/bedc/parts/concrete_instances/122_rootsystem_namecert_construction.tex:1-10, and the Weyl-group file states that WeylGroupUp is the finite reflection group generated by simple roots at papers/bedc/parts/concrete_instances/123_weylgroup_namecert_construction.tex:1-10. The finite-word preservation theorem is the first concrete generated-action consequence of those two interfaces, narrower than the existing Lie-algebra Jacobi/adjoint target and not a general Lie-theory survey.

---

### B-455 - RandomVar total-event preimage exactness

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | RandomVar total-event preimage exactness |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 7/10 |

Problem:
Under a carried RandomVarUp map X:S->T with source total event Omega_S, target total event Omega_T, and measurable-preimage readback, preimage_X(Omega_T) is source-measurable and source-event-classifier equal to Omega_S.

Local inputs:
- `papers/bedc/parts/concrete_instances/163_randomvar_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/162_probspace_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/measure/carrier_surface_rows.tex`

Rationale:
Belongs in the RandomVar chapter. This is the standard inverse-image law f^{-1}(Y)=X from introductory set theory and probability texts, and it is already needed as an assumption by the Distribution total-mass theorem at papers/bedc/parts/concrete_instances/164_distribution_namecert_construction.tex:17. The RandomVar chapter has union, relative-difference, and complement preimage theorems at papers/bedc/parts/concrete_instances/163_randomvar_namecert_construction.tex:13, :59, and :111, but no labeled total-preimage theorem. It should close directly from the total-event classifier/readback rows already used in the surrounding proofs.

---

### B-456 - RandomVar empty-event preimage exactness

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | RandomVar empty-event preimage exactness |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 7/10 |

Problem:
Under a carried RandomVarUp map X:S->T with source empty event empty_S, target empty event empty_T, and measurable-preimage readback, preimage_X(empty_T) is source-measurable and source-event-classifier equal to empty_S.

Local inputs:
- `papers/bedc/parts/concrete_instances/163_randomvar_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/162_probspace_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/measure/carrier_surface_rows.tex`

Rationale:
Belongs in the RandomVar chapter. The theorem is the textbook inverse-image law f^{-1}(empty)=empty, used throughout measure-theory introductions before pushforward measures. It is presently only consumed as an assumption by the Distribution empty-target theorem at papers/bedc/parts/concrete_instances/164_distribution_namecert_construction.tex:59, while papers/bedc/parts/concrete_instances/163_randomvar_namecert_construction.tex states only union, relative-difference, and complement preimage laws at :13, :59, and :111. The proof is a boundary readback argument, not new infrastructure.

---

### B-457 - Distribution nonnegative value inheritance

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Distribution nonnegative value inheritance |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 6/10 |

Problem:
Under a DistributionUp pushforward for X:S->T, every target measurable event B has nonnegative pushed-forward value mu_X(B).

Local inputs:
- `papers/bedc/parts/concrete_instances/164_distribution_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/163_randomvar_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/measure/relative_difference_rows.tex`

Rationale:
Belongs in the Distribution chapter. Nonnegativity of a pushforward measure is a first-page theorem in standard measure/probability treatments. The source-side theorem is already present as Measure nonnegative value obligation at papers/bedc/parts/concrete_instances/measure/relative_difference_rows.tex:1, and Distribution currently has only total mass, empty target zero, and finite disjoint additivity at papers/bedc/parts/concrete_instances/164_distribution_namecert_construction.tex:13, :55, and :94. The proof is just pushforward readback plus the existing measure nonnegativity row.

---

### B-458 - Distribution pushforward monotonicity

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Distribution pushforward monotonicity |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 7/10 |

Problem:
Under a DistributionUp pushforward for X:S->T, if target measurable events B and C satisfy B subset C and the RandomVar preimage row supplies the corresponding source inclusion, then mu_X(B) <=_R mu_X(C).

Local inputs:
- `papers/bedc/parts/concrete_instances/164_distribution_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/163_randomvar_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/measure/relative_difference_rows.tex`

Rationale:
Belongs in the Distribution chapter. Monotonicity of pushforward measures is standard in Billingsley or Folland-style introductions. The needed ingredients already exist: RandomVar relative-difference exactness records the target-to-source inclusion behavior at papers/bedc/parts/concrete_instances/163_randomvar_namecert_construction.tex:59, and source Measure monotonicity is present at papers/bedc/parts/concrete_instances/measure/relative_difference_rows.tex:26. No labeled Distribution monotonicity theorem appears beside the existing Distribution theorems at papers/bedc/parts/concrete_instances/164_distribution_namecert_construction.tex:13, :55, and :94.

---

### B-459 - Distribution relative-difference additivity

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Distribution relative-difference additivity |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |

Problem:
Under a DistributionUp pushforward for X:S->T, if target events B subset A have a target relative-difference event A_minus_B and RandomVar preserves that relative difference, then mu_X(A) is classifier-equal to mu_X(B)+mu_X(A_minus_B).

Local inputs:
- `papers/bedc/parts/concrete_instances/164_distribution_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/163_randomvar_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/measure/relative_difference_rows.tex`

Rationale:
Belongs in the Distribution chapter. The decomposition mu(A)=mu(B)+mu(A\B) for B subset A is a standard elementary measure theorem, and the pushforward version is the direct curricular next step after defining distributions. RandomVar relative-difference exactness is already a theorem at papers/bedc/parts/concrete_instances/163_randomvar_namecert_construction.tex:59, and Measure relative-difference additivity is present in papers/bedc/parts/concrete_instances/measure/relative_difference_rows.tex. The Distribution chapter has no relative-difference theorem among its current labels at papers/bedc/parts/concrete_instances/164_distribution_namecert_construction.tex:13, :55, and :94, so this is closeable without new definitions.

---

### B-460 - OperatorIdeal trace-class scalar closure

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | OperatorIdeal trace-class scalar closure |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
Under the OperatorIdeal trace-class setup, if T is carried by TC(H) and a is a carried scalar for the inherited Hilbert module action, then a times T is carried by TC(H).

Local inputs:
- `papers/bedc/parts/concrete_instances/191_operatorideal_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/198_densitymatrix_namecert_construction.tex`

Rationale:
This is a concrete closure row for an existing OperatorIdeal surface and it appears to support a visible downstream DensityMatrix dependency. It is not a marker, status, or parameter-echo target, and it is distinct from the existing BOARD entries and the listed paper labels.

---

### B-461 - ConvexSet linear-image affine closure

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | ConvexSet linear-image affine closure |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
Under ConvexSetUp and LinearMapUp, if C has binary affine-combination closure and f is carried by the linear-map certificate, then the pointwise image f[C] has binary affine-combination closure.

Local inputs:
- `papers/bedc/parts/concrete_instances/186_convexset_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/linearmap/the_certificate.tex`

Rationale:
This is a concrete image-closure theorem using the paper's ConvexSet and LinearMap rows. It is not duplicated by the existing finite affine-spine or intersection closure labels, and it lands cleanly in an existing concrete_instances surface.

---

### B-462 - Distribution pushforward monotone events

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | Distribution pushforward monotone events |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
Under DistributionUp, RandomVarUp, and ProbSpaceUp, if B is a target measurable subevent of A for X, then mu_X(B) <= mu_X(A) under the target RealAlgOrder row.

Local inputs:
- `papers/bedc/parts/concrete_instances/164_distribution_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/163_randomvar_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/162_probspace_namecert_construction.tex`

Rationale:
This is a concrete composite consequence of the probability surface: pushforward measure, random-variable preimage exactness, and source monotonicity. It is not a duplicate of the existing total-mass, empty-event, or disjoint-union distribution rows.

---

### B-463 - Network-flow residual exhaustion optimality

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | Network-flow residual exhaustion optimality |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 7/10 |

Problem:
Under finite NetworkFlowUp feasibility, if a flow has a residual-cut augmenting-path exhaustion certificate, then the flow is maximal among feasible flows and its residual cut is minimal among finite cuts.

Local inputs:
- `papers/bedc/parts/concrete_instances/211_networkflow_namecert_construction.tex`

Rationale:
This is a focused certificate-consumption corollary that exposes the direct payload of residual exhaustion by composing existing network-flow results. It is concrete, scoped, and distinct from the existing BOARD targets.

---

### B-464 - Hash collision gives reversed second-preimage

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | Hash collision gives reversed second-preimage |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
Under HashUp, if HashCollisionSuccess_H(x,x') holds, then HashSecondPreimageSuccess_H(x',x) holds over the same two hash-evaluation rows.

Local inputs:
- `papers/bedc/parts/concrete_instances/220_hash_namecert_construction.tex`

Rationale:
This is a concrete transcript bridge between two existing hash success predicates. It is not just collision symmetry or the already stated second-preimage-to-collision direction, and it makes a missing converse relation explicit.

---

### B-465 - Quadrature degree-bound reflexivity

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | Quadrature degree-bound reflexivity |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 7/10 |
| Novelty | 7/10 |

Problem:
Under QuadratureUp, for every unary degree bound d, DegBoundLe(d,d) holds.

Local inputs:
- `papers/bedc/parts/concrete_instances/205_quadrature_namecert_construction.tex`

Rationale:
This is small but valid certificate infrastructure for the paper-defined exactness-degree comparison. Existing weakening and transitivity rows do not by themselves provide the missing reflexive row, and no listed BOARD entry covers quadrature degree-bound structure.

---

### B-466 - Distribution monotone under target inclusion

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (codex) |
| Object | Distribution monotone under target inclusion |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |

Problem:
Under a DistributionUp pushforward setup for a RandomVarUp map X from a ProbSpaceUp source, if B and A are target measurable events with B \subseteq A, then \mu_X(B) \le_R \mu_X(A).

Local inputs:
- `papers/bedc/parts/concrete_instances/164_distribution_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/163_randomvar_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/measure/relative_difference_rows.tex`
- `papers/bedc/parts/concrete_instances/162_probspace_namecert_construction.tex`

Rationale:
This is a concrete DistributionUp consequence, not a marker or verification-axis task. The paper has MeasureUp monotonicity and RandomVar preimage relative-difference exactness, while the DistributionUp chapter currently states total mass, empty-event zero mass, finite disjoint-union additivity, and nonnegative value inheritance, but not target-inclusion monotonicity for the pushforward endpoint. It is distinct from the existing BOARD entries and lands safely in the short distribution chapter with focused measure and random-variable support inputs.

---

### B-467 - Matroid FinSet intersection right subset projection

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Matroid FinSet intersection right subset projection |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |

Problem:
If J is a FinSetIntersection(J; I,K) over one ground, then FinSetSubset(J,K) holds under the same FinSetUp ground.

Local inputs:
- `papers/bedc/parts/concrete_instances/180_matroid_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/90_finset_namecert_construction.tex`
- `lean4/BEDC/Derived/MatroidUp.lean`

Rationale:
Definition evidence: FinSetSubset and FinSetIntersection are introduced at papers/bedc/parts/concrete_instances/180_matroid_namecert_construction.tex:12-31. The only projection theorem is the left factor projection, labeled lem:matroid-finset-intersection-left-subset at :59-72, and the independence theorem at :85-103 uses that left projection explicitly at :111-115. Lean mirrors only left-subset variants at lean4/BEDC/Derived/MatroidUp.lean:25, :59, and :141. Focused rg for 'right subset|right-subset|right projection|intersection projects to the right|intersection.*right.*subset' in the Matroid paper file and MatroidUp.lean returned 0 hits. This is a concrete one-side-without-dual gap, not a parameter-transport echo.

---

### B-468 - ConvexSet linear image finite affine-spine closure

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | ConvexSet linear image finite affine-spine closure |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
If f is carried by LinearMapUp(V,W) and ConvAffSpine over the image carrier f[C] has nonnegative unit-sum weights and endpoint z, then f[C](z) holds under the shared FieldUp, VecSpaceUp, and ConvexSetUp data.

Local inputs:
- `papers/bedc/parts/concrete_instances/186_convexset_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/linearmap/module_linearmap_certificates.tex`
- `lean4/BEDC/Derived/ConvexSetUp.lean`

Rationale:
Definition evidence: the binary affine-combination row is at papers/bedc/parts/concrete_instances/186_convexset_namecert_construction.tex:12-30, finite affine-spine data are at :102-152, and finite affine-spine closure for the original carrier is at :155-170. The classifier image carrier is defined at :235-241, and only binary image closure is proved at :244-256. Focused rg for 'linear.*image.*finite|finite.*linear.*image|image.*affine-spine|affine-spine.*image|linear-image.*spine' in the ConvexSet paper file and lean4/BEDC/Derived/ConvexSetUp.lean returned 0 hits; the Lean file has only singleton affine-spine entries at lean4/BEDC/Derived/ConvexSetUp.lean:8-31. The claim is a concrete closure theorem for a named image carrier, not generic transport.

---

### B-469 - Simplicial intersection inherits dimension grading

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Simplicial intersection inherits dimension grading |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
If K and L share the simplex-code source, face relation, and a common face-dimension grading row, then Simplex_KcapL(alpha), Simplex_KcapL(beta), and Face_KcapL(alpha,beta) imply dim(alpha) <= dim(beta).

Local inputs:
- `papers/bedc/parts/concrete_instances/216_simplicialcomplex_namecert_construction.tex`
- `lean4/BEDC/Derived/SimplicialComplexUp.lean`

Rationale:
Definition evidence: the finite face carrier records face-incidence and dimension-grading data at papers/bedc/parts/concrete_instances/216_simplicialcomplex_namecert_construction.tex:12-38, the explicit face dimension grading row is at :82-98, and the intersection carrier rows are defined at :145-164. The existing intersection theorem at :166-205 proves enumeration, face closure, transitivity, and two-step face closure, but it does not mention dimension. Focused rg for 'intersection.*dimension|dimension.*intersection|grading.*intersection|intersection.*grading|intersection.*face.*dimension' in the SimplicialComplex paper file and lean4/BEDC/Derived/SimplicialComplexUp.lean returned 0 hits. Lean separately has face-chain dimension monotonicity at :64 and intersection face-chain closure at :93, confirming the missing combination.

---

### B-470 - QuantumChannel composition associativity law

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | QuantumChannel composition associativity law |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
If Phi, Psi, and Theta are composable QuantumChannelUp carriers, then both bracketed triple composites are QuantumChannelUp carriers and are pointwise classifier-equal as maps from the first trace-class carrier to the last.

Local inputs:
- `papers/bedc/parts/concrete_instances/199_quantumchannel_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/linearmap/module_linearmap_certificates.tex`
- `papers/bedc/parts/concrete_instances/198_densitymatrix_namecert_construction.tex`

Rationale:
Definition evidence: the CPTP carrier is defined at papers/bedc/parts/concrete_instances/199_quantumchannel_namecert_construction.tex:23-34, binary composition closure is proved at :59-75, and the identity channel is proved at :279-293. The Linearmap chapter already supplies the underlying module-linear associativity package at papers/bedc/parts/concrete_instances/linearmap/module_linearmap_certificates.tex:238-260, but no channel-level theorem lifts the CPTP and density-output rows through triple composition. Focused rg for 'QuantumChannel.*associat|QChan.*associat|channel.*composition.*associat|composition.*associat.*channel' in the QuantumChannel paper file returned 0 hits, and marker grep over that file returned 0 hits. This is a concrete composition law for an existing object, not a closurestatus or marker task.

---

### B-471 - \label{ch:capstones-reasoning-by-contradiction-boundary}

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | \label{ch:capstones-reasoning-by-contradiction-boundary} |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 7/10 |
| Novelty | 7/10 |

Problem:
\label{ch:capstones-reasoning-by-contradiction-boundary}

Local inputs:
- `papers/bedc/parts/capstones/reasoning_by_contradiction_boundary.tex`

Rationale:
Surfaced from paper gap scan: open_prose at papers/bedc/parts/capstones/reasoning_by_contradiction_boundary.tex:4.

Snippet:
\label{ch:capstones-reasoning-by-contradiction-boundary}

BEDC accepts certain forms of reasoning by contradiction and rejects others, and the boundary is not a stylistic preference but a structural one. The permitted patterns -- proving a negation by deriving falsity from the assumption, eliminating double negation on a decidable proposition, refuting a false existence claim by exhibiting a counterexample to its witness -- all operate within the closed ground loop and never touch the meta level. The forbidden patterns -- proving an existence statement by contradiction, eliminating double negation on an undecidable proposition, splitting on the law of excluded middle for a predicate over the carrier of naming certificates -- all, on inspection, reduce to a single underlying move: closing the meta-level self-reference loop that \autoref{ch:capstones-reflection-and-limits}'s two-loops theorem requires to remain open. This chapter (i) catalogues the permitted refutation patterns as they appear in \autoref{ch:core-relational-extension-and-continuation}'s extension and continuation calculus, (ii) catalogues the forbidden patterns and traces each to its meta-closure consequence via a Tarski-style fragment of the truth predicate, (iii) states the unifying theorem that every forbidden pattern implements meta-closure, and (iv) records that the boundary thus identified is the same boundary that separates the closed ground loop from the open meta loop, with the halting capstone (\autoref{ch:capstones-halting-as-form-of-distinction-limit}) as the canonical sibling instance.

\section{Permitted refutation patterns}
\label{sec:reasoning-by-contradiction-permitted}

\begin{definition}[Permitted refutation pattern]
\label{def:reasoning-permitted-pattern}
A \emph{permitted refutation pattern} is a derivation rule of the form ``from $A \Rightarrow \bot$, conclude $\neg A$'' or one of its decidable specialisations, where the derivation of $\bot$ uses only $\Cont$, $\hsame$, $\msame$, and the closure laws of a fixed naming certificate. The conclusion $\neg A$ is read as the BEDC predicate ``every witness of $A$ produces $\bot$ inside the certificate's classifier'', not as ``$A$ holds in no possible world''.
\end{definition}

\begin{example}[Negation by derived falsity]
\label{ex:reasoning-negation-by-falsity}
The kernel theorem $\neg \msame(\bzero, \bone)$ of \autoref{ch:core-raw-marks-and-mark-sameness} is a permitted refutation. Assuming a witness $w$ of $\msame(\bzero, \bone)$ produces $\bot$ by inversion on the constructor pattern: $\msame$ is a closed inductive whose only constructor identifies a mark with itself, and the constructors of $\Mark$ are different. The derivation never leaves the inductive carrier of $\Mark$ and never appeals to a meta-level predicate.

---

### B-472 - \label{ch:capstones-reflection-and-limits}

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | \label{ch:capstones-reflection-and-limits} |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 7/10 |
| Novelty | 7/10 |

Problem:
\label{ch:capstones-reflection-and-limits}

Local inputs:
- `papers/bedc/parts/capstones/reflection_and_limits.tex`

Rationale:
Surfaced from paper gap scan: open_prose at papers/bedc/parts/capstones/reflection_and_limits.tex:4.

Snippet:
\label{ch:capstones-reflection-and-limits}

This chapter answers one question: in what precise senses does BEDC describe itself, and where does each sense fail? The answer is two-fold and the asymmetry between the two halves is the main mathematical content. At the ground, the primitive distinction between two raw marks is \emph{self-instantiating}: stating it is already an act of it. This is a closed loop, and it must close for the rest of BEDC to begin. At the meta-level, the naming-certificate framework can internally describe the structure of any well-founded formal system, the host calculus of inductive constructions included. This second loop must remain open: closing it would, by Tarski undefinability, force inconsistency.

The two loops together characterise what kind of foundation BEDC is. The chapter develops them in turn. \autoref{sec:reflection-ground-loop} isolates the ground loop. \autoref{sec:reflection-def-as-classifier} establishes the correspondence between formal definition and classifier choice. \autoref{sec:reflection-inductive-internalisation} interprets closed inductive types as classifier closures inside BEDC. \autoref{sec:reflection-self-description} extends the interpretation to a structural copy of the host calculus. \autoref{sec:reflection-limit} fixes the Tarski-M\"unchhausen boundary. \autoref{sec:reflection-two-loops} contrasts the closed ground loop with the open meta loop and locates BEDC's specific contribution to foundations.

\section{The primitive distinction as generative loop}
\label{sec:reflection-ground-loop}

\begin{definition}[Form of distinction]
\label{def:form-of-distinction}
Let $\bzero$ and $\bone$ denote the two raw marks of \autoref{def:raw-marks}. The \emph{form of distinction} is the closed inductive judgment generating $\Mark$, given by the two formation rules of \autoref{ch:core-raw-marks-and-mark-sameness} together with the kernel-level recognition that $\bzero$ and $\bone$ are not the same constructor. The form is the data of: two formal tokens, and the capacity to tell them apart.
\end{definition}

\begin{remark}[Self-instantiation]

---

### B-473 - \begin{remark}[Structure-existence boundary]

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | \begin{remark}[Structure-existence boundary] |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 7/10 |
| Novelty | 7/10 |

Problem:
\begin{remark}[Structure-existence boundary]
\label{rem:reflection-structure-existence-boundary}
The internal $\mathrm{CIC}^{*}$ of \autoref{thm:internal-cic-interpretation} is a \emph{structural} reproduction of the host calculus. It is not the host calculus considered as a runtime: every Lean proof of every theorem appearing in this manuscript is checked by an external Lean kernel, which is itself implemented in a programming language whose semantics is not BEDC-internal. The isomorphism between $\mathrm{CIC}^{*}$ and the host CIC holds at the level of formal structure; it does not hold at t

Local inputs:
- `papers/bedc/parts/capstones/reflection_and_limits.tex`

Rationale:
Surfaced from paper gap scan: open_prose at papers/bedc/parts/capstones/reflection_and_limits.tex:111.

Snippet:
\begin{remark}[Structure-existence boundary]
\label{rem:reflection-structure-existence-boundary}
The internal $\mathrm{CIC}^{*}$ of \autoref{thm:internal-cic-interpretation} is a \emph{structural} reproduction of the host calculus. It is not the host calculus considered as a runtime: every Lean proof of every theorem appearing in this manuscript is checked by an external Lean kernel, which is itself implemented in a programming language whose semantics is not BEDC-internal. The isomorphism between $\mathrm{CIC}^{*}$ and the host CIC holds at the level of formal structure; it does not hold at the level of executing the structure. No formal system can include the runtime that interprets it. This boundary is the formal content of the M\"unchhausen impossibility: the bootstrap remains open at the runtime level even when it is closed at the structural level.
\end{remark}

\begin{remark}[Tarski undefinability]
\label{rem:reflection-tarski-undefinability}
The self-description of \autoref{cor:bedc-self-description} is a description of the formal structure of BEDC inside BEDC; it is not a definition of a BEDC truth predicate inside BEDC. By Tarski undefinability, every formal system rich enough to describe its own syntactic structure cannot define its own truth predicate. BEDC is no exception, and \autoref{cor:bedc-self-description} does not attempt this. Recovering truth requires a metalanguage strictly stronger than the language being described, and that metalanguage is again hosted externally.
\end{remark}

\section{The two loops of BEDC}
\label{sec:reflection-two-loops}

\begin{theorem}[Closed ground loop and open meta loop]
\label{thm:two-loops}

---

### B-474 - RandomVar countable preimage union exactness

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | RandomVar countable preimage union exactness |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 9/10 |

Problem:
If a RandomVarUp map has measurable preimage readback and a target measurable sequence has a countable-union row, then the source preimage of the target countable union is classifier-equal to the source countable union of the pointwise preimages, and pairwise disjointness pulls back, under the source MeasureUp surface.

Local inputs:
- `papers/bedc/parts/concrete_instances/163_randomvar_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/measure/carrier_surface_rows.tex`
- `papers/bedc/parts/concrete_instances/measure/carrier_surface.tex`

Rationale:
RandomVar has theorem rows for binary disjoint preimage exactness at papers/bedc/parts/concrete_instances/163_randomvar_namecert_construction.tex:12-13, relative difference at :58, complement/relative difference at :110, empty event at :181, and total-event rows later, but no countable preimage theorem. The MeasureUp surface already exposes the needed countable inputs: countable-sum endpoint, countable-union closure, sigma-additivity, and countable-sum classifier rows at papers/bedc/parts/concrete_instances/measure/carrier_surface_rows.tex:44-48, with the public sigma-additivity obligation at papers/bedc/parts/concrete_instances/measure/carrier_surface.tex:205-223. Focused grep for `randomvar.*countable|preimage.*sequence|preimage.*sigma` under parts returned 0 theorem labels; the only relevant RandomVar hit in the sigma search was the existing binary theorem use at 163_randomvar_namecert_construction.tex:22. The proposed landing file has 728 lines, below the 760-line avoidance threshold.

---

### B-476 - Unitary conjugation is a QuantumChannel

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Unitary conjugation is a QuantumChannel |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 9/10 |

Problem:
If U is a UnitaryGroupUp automorphism of a Hilbert carrier H, then the conjugation map rho maps to U rho U^{-1} is carried by QuantumChannelUp(H,H), and therefore sends DensityMatrixUp(H) endpoints to DensityMatrixUp(H) endpoints.

Local inputs:
- `papers/bedc/parts/concrete_instances/197_unitarygroup_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/198_densitymatrix_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/199_quantumchannel_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/191_operatorideal_namecert_construction.tex`

Rationale:
QuantumChannel already defines the CPTP carrier at papers/bedc/parts/concrete_instances/199_quantumchannel_namecert_construction.tex:23, proves density-matrix image at :36, composition closure at :59, and identity channel CPTP at :279. UnitaryGroup is present as the Hilbert-space inner-product-preserving automorphism interface at papers/bedc/parts/concrete_instances/197_unitarygroup_namecert_construction.tex:4, but focused grep for `unitary.*conjug|conjug.*density|quantumchannel.*unitary|unitary channel` under concrete_instances returned no theorem labels and only roadmap-level hits. This is not a parameter-transport echo: the proof must show linearity, complete positivity, and trace preservation for a concrete conjugation map. The natural landing file, 199_quantumchannel_namecert_construction.tex, has 418 lines.

---

### B-477 - Independence invariance under finite reindexing

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Independence invariance under finite reindexing |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 7/10 |
| Novelty | 8/10 |

Problem:
If a finite family of RandomVarUp variables satisfies IndependenceUp through joint-distribution factorisation and pi is a PermutationUp bijection of the finite index carrier, then the reindexed family also satisfies IndependenceUp with the product-of-marginals factorisation reindexed by pi.

Local inputs:
- `papers/bedc/parts/concrete_instances/165_independence_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/94_permutation_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/163_randomvar_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/164_distribution_namecert_construction.tex`

Rationale:
The IndependenceUp chapter states the interface as joint-distribution factorisation for a finite family of random variables at papers/bedc/parts/concrete_instances/165_independence_namecert_construction.tex:4, and PermutationUp supplies bijections of a FinSetUp carrier at papers/bedc/parts/concrete_instances/94_permutation_namecert_construction.tex:4. The independence file has 10 lines, 0 theorem environments, and 0 Lean markers in the inventory. Focused grep for `independence.*(perm|symm|reindex|factor|marginal)|joint.*factor|marginal.*factor|PermutationUp` returned no theorem labels for independence; the hits were roadmap prose, the permutation interface, and the independence interface line itself. The claim is a concrete finite reindexing closure property, not a generic carrier-equivalence transport.

---

### B-479 - Empty edge predicate is a matching

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Empty edge predicate is a matching |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 6/10 |

Problem:
Under a GraphUp carrier G, if the selected edge predicate is empty, then MatchingEdgeSet_G(empty) holds.

Local inputs:
- `papers/bedc/parts/concrete_instances/212_matching_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/96_graph_namecert_construction.tex`
- `lean4/BEDC/Derived/MatchingUp.lean`

Rationale:
Belongs in concrete_instances MatchingUp. Introductory graph theory treats the empty edge set as the first matching before hereditary and union facts. The chapter defines MatchingEdgeSet_G(M) by edge support and a no-shared-vertex implication at papers/bedc/parts/concrete_instances/212_matching_namecert_construction.tex:12-23, and its only matching theorems are finite-subset closure at papers/bedc/parts/concrete_instances/212_matching_namecert_construction.tex:38 and compatible union closure at papers/bedc/parts/concrete_instances/212_matching_namecert_construction.tex:77. Focused search found no labeled empty-matching theorem or board entry. It closes in one round: both defining obligations are implications from the empty predicate, so the proof is vacuous and needs no new graph infrastructure.

---

### B-480 - Banach zero bounded-linear operator carrier

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | Banach zero bounded-linear operator carrier |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
Under Banach candidates C and D with their vector zero rows and the RealUp zero bound row, the zero endpoint map C_V -> D_V is carried as BanachBLOp(C,D,0,0,Lambda0).

Local inputs:
- `papers/bedc/parts/concrete_instances/banach/bounded_linear_operator_obligations.tex`
- `papers/bedc/parts/concrete_instances/191_operatorideal_namecert_construction.tex`

Rationale:
This is a concrete missing existence theorem for the Banach bounded-linear-operator carrier, not a marker or verification-status item. It is distinct from existing BOARD entries and from the listed paper coverage, and it supplies a base zero-operator row consumed by the later operator-ideal surface.

---

### B-482 - Trace-class binary linear-combination closure

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | Trace-class binary linear-combination closure |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 6/10 |

Problem:
If TC(H)(T), TC(H)(S), and a,b are carried RealUp scalars, then TC(H)((a odot_H T) +_{TC(H)} (b odot_H S)).

Local inputs:
- `papers/bedc/parts/concrete_instances/191_operatorideal_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/198_densitymatrix_namecert_construction.tex`

Rationale:
This packages existing trace-class additive and scalar closure into a concrete reusable binary linear-combination theorem used by downstream density-matrix surfaces. It is close to known closure rows but still distinct from the listed paper labels and existing BOARD targets.

---

### B-483 - DensityMatrix constant affine-spine exactness

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | DensityMatrix constant affine-spine exactness |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
If DensAffSpine_H(xs,lambda,rho_mix) holds and every displayed density entry of xs is density-classifier equal to a fixed carried rho, then rho_mix is density-classifier equal to rho.

Local inputs:
- `papers/bedc/parts/concrete_instances/198_densitymatrix_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/186_convexset_namecert_construction.tex`

Rationale:
This is a concrete determinacy/exactness theorem for the existing density-matrix affine-spine construction. It is not a field-transport echo, and no existing BOARD item or listed paper label covers constant-spine endpoint exactness.

---

### B-484 - QuantumChannel identity composition units

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | QuantumChannel identity composition units |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
If QChan_{H,K}(Phi) holds, then Phi composed with id_TC(H) and id_TC(K) composed with Phi are carried quantum channels and are pointwise classifier-equal to Phi.

Local inputs:
- `papers/bedc/parts/concrete_instances/199_quantumchannel_namecert_construction.tex`

Rationale:
This fills a concrete category-like unit gap in the quantum-channel surface after identity, composition, and associativity are already present. It is distinct from the Banach operator unit target because it concerns CPTP channel composition and pointwise channel classification.

---

### B-481 - Banach bounded-operator identity units

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | Banach bounded-operator identity units |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
If BanachBLOp(C,D,T,K,Lambda) holds and the identity maps on C and D carry the unit bound, then T composed with id_C and id_D composed with T are carried and classify with T.

Local inputs:
- `papers/bedc/parts/concrete_instances/banach/bounded_linear_operator_obligations.tex`
- `papers/bedc/parts/concrete_instances/banach/bounded_linear_operator_composition.tex`

Rationale:
This is a concrete two-sided unit law for an existing Banach operator composition surface. Existing coverage includes carrier and composition structure but not the identity-unit theorem, and the target is not duplicated by any current BOARD entry.

---

### B-485 - Simplicial union carrier face closure

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | Simplicial union carrier face closure |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 7/10 |

Problem:
If finite simplicial carriers K and L share the simplex-code source, classifier, and face relation, and js enumerates the pointwise union predicate Simplex_K or Simplex_L, then the union predicate is face-closed and inherits face transitivity.

Local inputs:
- `papers/bedc/parts/concrete_instances/216_simplicialcomplex_namecert_construction.tex`

Rationale:
This is a concrete closure counterpart to the existing simplicial intersection carrier results. It belongs cleanly in the simplicial-complex chapter, has a direct implication shape, and does not duplicate any current BOARD target or listed paper theorem.

---

### B-486 - Unitary conjugation channel composition law

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (codex) |
| Object | Unitary conjugation channel composition law |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 7/10 |

Problem:
Under the QuantumChannelUp and UnitaryGroupUp setup on a Hilbert carrier H, carried unitary automorphisms U and V imply that Ad_U composed with Ad_V is the QuantumChannel endpoint classified by Ad_{U\circ V}.

Local inputs:
- `papers/bedc/parts/concrete_instances/199_quantumchannel_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/197_unitarygroup_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/191_operatorideal_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/69_hilbert_namecert_construction.tex`

Rationale:
The candidate is a concrete implication landing directly in the existing quantum-channel surface. It is distinct from the paper's current QuantumChannel composition closure and Unitary conjugation is a QuantumChannel theorem: those establish channel closure and single-unitary conjugation, but do not state the endpoint-identification law for the composite conjugation channel against the product unitary. It is not marker-only, not a BOARD duplicate, and the main landing file is below the line cap.

---

### B-487 - Simplicial union face dimension grading

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (codex) |
| Object | Simplicial union face dimension grading |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 6/10 |

Problem:
If K and L share a face relation and a common grading row, then every face chain in Simplex_{K\cup L} inherits the carried dimension comparisons by case analysis on the upper simplex branch.

Local inputs:
- `papers/bedc/parts/concrete_instances/216_simplicialcomplex_namecert_construction.tex`

Rationale:
This is a concrete closure-style simplicial-complex theorem that lands in the same surface as B-485 without duplicating it: B-485 covers face closure and face transitivity for the union carrier, while this target adds the inherited grading/face-dimension monotonicity row. The claim is a single implication under shared carrier, face, and grading setup, and it is not marker-only or verification-axis work.

---

### B-488 - Simplicial union append enumeration

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (codex) |
| Object | Simplicial union append enumeration |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 6/10 |

Problem:
If ks enumerates Simplex_K and ls enumerates Simplex_L under the shared simplex-code source and classifier, then ks++ls enumerates Simplex_{K\cup L}.

Local inputs:
- `papers/bedc/parts/concrete_instances/216_simplicialcomplex_namecert_construction.tex`

Rationale:
This is a concrete enumeration lemma for the simplicial union carrier and is a useful sibling/prerequisite to B-485 rather than a duplicate of its face-closure theorem. It has a precise implication shape, stays within the concrete_instances chapter, and supplies a natural construction of the union enumeration object assumed by the existing BOARD target.

---

### B-475 - Distribution pushforward sigma-additivity

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Distribution pushforward sigma-additivity |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
If a DistributionUp pushforward is induced by a RandomVarUp map whose preimages preserve countable target unions and the source MeasureUp surface is sigma-additive, then the pushed-forward target measure classifies a countable disjoint union by the countable sum of the pushed-forward component measures.

Local inputs:
- `papers/bedc/parts/concrete_instances/164_distribution_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/163_randomvar_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/measure/carrier_surface.tex`
- `papers/bedc/parts/concrete_instances/measure/carrier_surface_rows.tex`

Rationale:
Distribution currently has pushforward total mass at papers/bedc/parts/concrete_instances/164_distribution_namecert_construction.tex:12, finite binary disjoint-union additivity at :93, monotonicity at :203 and :330, and relative-difference additivity at :250. The finite additivity proof explicitly consumes the binary RandomVar preimage theorem at 164_distribution_namecert_construction.tex:105, while the MeasureUp surface already provides countable-disjoint sigma-additivity at papers/bedc/parts/concrete_instances/measure/carrier_surface.tex:205-223 and countable-sum classifier stability at :237-246. Focused grep for `distribution.*countable|pushforward.*sigma` under parts returned 0 theorem labels; hits were roadmap prose and existing finite/binary distribution material. The distribution file is 375 lines, so it is a viable body-file target.

---

### B-478 - CondExp projection idempotence

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | CondExp projection idempotence |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 7/10 |
| Novelty | 8/10 |

Problem:
If CondExpUp(X,G) is the conditional expectation of an integrable RandomVarUp endpoint onto a sub-sigma-algebra G, then applying the same CondExpUp projection again is classifier-equal to the first conditional expectation under the HilbertUp L2 projection surface.

Local inputs:
- `papers/bedc/parts/concrete_instances/166_condexp_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/163_randomvar_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/69_hilbert_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/hilbert_orthogonal_projection_row.tex`

Rationale:
CondExpUp is described as the L2 projection of an integrable random variable onto the subspace measurable with respect to a sub-sigma-algebra at papers/bedc/parts/concrete_instances/166_condexp_namecert_construction.tex:4. That chapter has 10 lines, 0 theorem environments, and 0 Lean markers in the inventory. A related singleton Hilbert projection idempotence theorem exists at papers/bedc/parts/concrete_instances/hilbert_orthogonal_projection_row.tex:60-73, but focused grep for `condexp|conditional[- ]expect|tower law|tower property|conditional expectation.*idempot|condexp.*idempot` returned no CondExp theorem labels; hits were roadmap prose, dependency mentions in Bayesian/Martingale chapters, and the CondExp chapter header. The proposed result is the concrete idempotence law for the conditional-expectation object itself.

---

### B-489 - Hash collision-freeness excludes second preimages

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | Hash collision-freeness excludes second preimages |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 7/10 |

Problem:
In the HashUp setup, CollFreeH and HashSecondPreimageSuccessH(x,y) imply contradiction by converting second-preimage success into HashCollisionSuccessH(x,y).

Local inputs:
- `papers/bedc/parts/concrete_instances/220_hash_namecert_construction.tex`

Rationale:
This is a concrete security-facing obstruction theorem over the existing HashUp transcript surface. It is not a BOARD duplicate and not already packaged in the paper labels: existing rows convert second-preimage success to collision success, while this target names the collision-free budget and closes the impossibility consequence as a reusable theorem.

---

### B-490 - PublicKey certified ciphertext plaintext uniqueness

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | PublicKey certified ciphertext plaintext uniqueness |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 7/10 |

Problem:
In the PublicKeyUp setup, PKDecryptEncryptExactP and PKDecryptOutputDetP together with PKKeyGenP(pk,sk), PKCertifiedEncP(pk,m,c), and PKCertifiedEncP(pk,n,c) imply muP(m,n).

Local inputs:
- `papers/bedc/parts/concrete_instances/221_publickey_namecert_construction.tex`

Rationale:
This is a concrete inversion theorem for certified ciphertext rows, distinct from the existing decrypt-encrypt and arbitrary-decryption statements. It packages the consequence that one generated keypair and one certified ciphertext cannot certify two classifier-distinct plaintexts, using existing exactness and output determinacy rows.

---

### B-492 - Simplicial union inherits dimension grading

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | Simplicial union inherits dimension grading |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |

Problem:
If finite simplicial carriers K and L share the simplex-code source, face relation, and dimension map d, and the union predicate is finite and face-closed, then carried union faces and two-step face chains satisfy the inherited dimension inequalities.

Local inputs:
- `papers/bedc/parts/concrete_instances/216_simplicialcomplex_namecert_construction.tex`

Rationale:
This is a distinct union-side counterpart to the existing intersection dimension-grading theorem and to the active union face-closure target. It lands on a concrete finite simplicial carrier statement and gives a reusable grading row once the union carrier rows are in place.

---

### B-494 - Distribution↑ continuity-from-below pushforward bridge

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | Distribution↑ continuity-from-below pushforward bridge |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
If preimages under RandomVarUp preserve increasing unions and the source MeasureUp has continuity-from-below, then for any increasing target-measurable sequence (B_n) with union B, the pushforward satisfies μ_X(B) = lim_n μ_X(B_n).

Local inputs:
- `papers/bedc/parts/concrete_instances/164_distribution_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/163_randomvar_namecert_construction.tex`

Rationale:
This is a clean, concrete closure statement that is not a rephrasing of existing sigma-additivity; it exercises the monotone-limit axis of DistributionUp behavior and should be a useful bridge lemma for later limit-based arguments in MeasureUp/DistributionUp interoperability.

---

### B-491 - Banach bounded-operator bound weakening

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | Banach bounded-operator bound weakening |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |

Problem:
If BanachBLOp(C,D,T,K,Lambda), K <= Kprime, and Kprime is a carried nonnegative RealUp bound endpoint, then T is carried as BanachBLOp(C,D,T,Kprime,LambdaPrime) with the same structural rows and a weakened bound ledger.

Local inputs:
- `papers/bedc/parts/concrete_instances/banach/bounded_linear_operator_obligations.tex`

Rationale:
This fills a useful budget-monotonicity gap in the Banach bounded-linear-operator surface. It is not just classifier transport: it constructs a reusable weakened operator-bound carrier row from RealUp order transitivity, norm nonnegativity, and multiplication monotonicity.

---

### B-493 - Network-flow residual cut capacity determinacy

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | Network-flow residual cut capacity determinacy |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 7/10 |

Problem:
For a fixed feasible finite NetworkFlowUp s-t flow F, any two residual-cut augmenting-path exhaustion certificates Xi and Eta for F induce NatUp-classifier-equal residual cut capacities.

Local inputs:
- `papers/bedc/parts/concrete_instances/211_networkflow_namecert_construction.tex`

Rationale:
This is a compact determinacy theorem over the existing NetworkFlowUp residual-exhaustion surface. Existing paper content proves each residual exhaustion cut capacity equals FlowValue(F); this target packages the certificate-independence consequence, which is distinct from optimality.

---

### B-495 - Distribution↑ null-completion random-variable descent

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | Distribution↑ null-completion random-variable descent |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |

Problem:
If for every target-measurable B, the symmetric difference X^{-1}(B) △ Y^{-1}(B) is μ_S-null, then for every target-measurable B, the pushforward measures satisfy μ_X(B) ∼ μ_Y(B).

Local inputs:
- `papers/bedc/parts/concrete_instances/163_randomvar_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/164_distribution_namecert_construction.tex`

Rationale:
This provides a concrete determinacy/stability theorem converting a.s. transport-level equality of RandomVarUp maps into distribution-level equality, which is a meaningful obstruction and reuse point for security-relevant and stochastic reasoning.

---

### B-496 - Independence↑ measurable-image bridge

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | Independence↑ measurable-image bridge |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
If X and Y are independent under IndependenceUp and maps f,g satisfy the readable-product preimage setup on RandomVarUp, then f ∘ X is independent of g ∘ Y.

Local inputs:
- (auto-spawn — no specific inputs declared)

Rationale:
This is a distinct, high-value propagation law for independence across measurable images, directly connecting independence, random-variable transport, and measurable readback structure; it is nontrivial relative to current board targets and extends closure behavior rather than duplicating existing single-object statements.

---

### B-497 - Measure↑ Dynkin closure from Distribution↑ generator agreement

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | Measure↑ Dynkin closure from Distribution↑ generator agreement |
| Layer | proof_obligations |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
If μ_X and ν agree on a π-system that generates the target measurable class and both satisfy target countable disjoint-union sigma-additivity, then μ_X and ν classify equal on every generated measurable event.

Local inputs:
- `papers/bedc/parts/proof_obligations/lean_scaffold_contract.tex`

Rationale:
This gives a principled uniqueness transfer from generators to full sigma closure in the Distribution↑ vs Measure↑ interface and is foundational for downstream determinacy/comparison results; it is broader and structurally different from the existing finite/countable distribution rows.

---

### B-498 - CondExp↑ pushforward tower compatibility

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | CondExp↑ pushforward tower compatibility |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
If G ⊆ H are sub-sigma structures and CondExpUp has the projection setup on H and G, then E_{μ_X}(E_{μ_X}(Z | H) | G) = E_{μ_X}(Z | G).

Local inputs:
- `papers/bedc/parts/concrete_instances/166_condexp_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/163_randomvar_namecert_construction.tex`

Rationale:
This is a substantive conditional-expectation law for nested sigma-algebras that is not redundant with self-idempotence: it enables filtration-consistent rewriting and bridges distribution pushforward to conditional projection calculus.

---

### B-499 - Finite family measurable-image independence

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | Finite family measurable-image independence |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |

Problem:
For any finite index family of random variables that is independent under IndependenceUp, if each component map has readable-product preimage transport, then applying those maps to each component yields a finite family that is again independent.

Local inputs:
- (auto-spawn — no specific inputs declared)

Rationale:
This is a concrete, one-shot implication that is not marker-only and sits in existing independent/random-variable infrastructure. It is a natural and valuable closure extension beyond the pairwise measurable-image law already present, enabling finite-family transport of independence without repeated ad hoc rewrites. It is distinct enough from the current board item on the binary case while remaining on-target for BEDC.

---

### B-500 - causal dependence implies positive max-rate

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | causal dependence implies positive max-rate |
| Layer | capstones |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 6/10 |

Problem:
If CrossHistCausal(h_a, h_b, k), then max_causal_rate(h_a, h_b, k) > 0.

Local inputs:
- `papers/bedc/parts/capstones/inter_hist_locality.tex`

Rationale:
The local capstone has schema-only definitions for CrossHistCausal and MaxCausalRate but no closed implication connecting dependence to a strictly positive rate. This is a direct closure target aligned with the multi-Hist causal chain and upgrades the roadmap into a concrete obstruction/coverage theorem rather than prose.

---

### B-501 - zero max-rate forbids causal dependence

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | zero max-rate forbids causal dependence |
| Layer | capstones |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 7/10 |

Problem:
If max_causal_rate(h_a, h_b, k) = 0, then not CrossHistCausal(h_a, h_b, k).

Local inputs:
- `papers/bedc/parts/capstones/inter_hist_locality.tex`

Rationale:
Although nearby schema-only statements discuss degeneracy/triviality, no formal contrapositive is present as a theorem. This gives a concrete negative-direction lemma useful for contradiction/falsification surfaces and is distinct from mere observer-symmetric constancy claims.

---

### B-502 - unary seed yields finite-prefix derived interface

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | unary seed yields finite-prefix derived interface |
| Layer | proof_sprint |
| Route | proof |
| Risk | unknown |
| Fit | 7/10 |
| Novelty | 9/10 |

Problem:
For unary history h with a nonempty unary right-tail condition, every finite prefix p of h determines a first-derived interface instance, and such instances are unique up to hsame.

Local inputs:
- `papers/bedc/parts/proof_sprint/10_first_derived_interface_seeds.tex`

Rationale:
Current proof-sprint text explicitly records only a seed-level guarantee and explicitly notes that full arithmetic reconstruction is not yet closed. This candidate turns the hinted constructive gap into a concrete existence+uniqueness closure target directly on the existing unary-prefix machinery, without duplicating known unary-tail or seed facts.

---

### B-505 - Sheaf refinement composition is classifier-associative on three-step towers

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | Sheaf refinement composition is classifier-associative on three-step towers |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |

Problem:
For displayed refinements (r,\epsilon):\mathcal V\to\mathcal U, (s,\eta):\mathcal W\to\mathcal V, (t,\zeta):\mathcal X\to\mathcal W of indexed sheaf covers, the composites ((r\circ s)\circ t) and (r\circ(s\circ t)) yield classifier-equal pulled-back compatible families on each indexed open of \mathcal X.

Local inputs:
- `papers/bedc/parts/concrete_instances/sheaf/05_refinement_composition_and_presentation.tex`

Rationale:
Composite consequence of two binary theorems already proved in sheaf/05_refinement_composition_and_presentation.tex (binary refinement composition + binary refinement-pullback composition). Three-step composition is invoked downstream by sheaf/08_triple_overlap_route_ledger.tex and sheaf/06_restricted_common_refinement_exactness.tex but never packaged as a named theorem. Closure proof is a routine two-application argument plus carrier-section classifier transitivity. Lands as a sibling theorem in a 198-line file — well below cap. No BOARD entry on sheaf refinement associativity, no overlap with B-352 (sheaf gluing uniqueness) or B-365 (global restriction local-family compatibility).

---

### B-504 - Composite gap policy n-fold pullback preserves coverage and separation

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | Composite gap policy n-fold pullback preserves coverage and separation |
| Layer | proof_obligations |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 7/10 |

Problem:
If \GapPol(\Pi,D) and \tau_1:D_1\to D, \tau_2:D_2\to D_1, \ldots, \tau_k:D_k\to D_{k-1} each carry a classifier-preserving pullback ledger over \Pi, then the k-fold composite \tau_1\circ\cdots\circ\tau_k carries a classifier-preserving pullback ledger satisfying coverage and separation over D_k.

Local inputs:
- `papers/bedc/parts/proof_obligations/gap_policy.tex`

Rationale:
Strict generalization, not a paraphrase. gap_policy.tex packages the single-step (line 152) and binary composite (line 196) cases, but the n-fold version is the form invoked downstream by proof_standing/04 and core/07's 'finite chain of compressions' arguments. Direct induction on chain length using the binary theorem closes it; lands in a 266-line chapter with no cap risk. No BOARD entry covers iterated pullback of gap policies, and the proof discharges as a clean inductive packaging — exactly the 'why only the binary case?' senior-referee gap that earns its own slot.

---

### B-503 - ProbSpace binary inclusion-exclusion identity

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | ProbSpace binary inclusion-exclusion identity |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
If A,B are measurable events in a ProbSpace, then \mu(A\cup B)+\mu(A\cap B)\sim_R\mu(A)+\mu(B).

Local inputs:
- `papers/bedc/parts/concrete_instances/162_probspace_namecert_construction.tex`

Rationale:
Genuinely missing companion in 162_probspace_namecert_construction.tex. BOARD has B-358 (complement-mass additivity), B-400 (complement = 1 − event-mass), B-435 (monotone bounds), and B-433 (measure binary-union subadditivity), but none packages the equality form for non-disjoint two-event pairs. The relative-difference row + finite-disjoint-union additivity decompose A∪B and B into disjoint pairs that add up to μ(A)+μ(B), giving the identity directly. This is the prerequisite shape downstream Distribution↑/Independence↑/CondExp↑ joint-event reasoning will repeatedly want, and the file (~178 lines) lands it cleanly without needing a split. Concrete implication form, in scope, not a parameter echo.

---

### B-506 - Distribution pushforward inclusion-exclusion identity

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | Distribution pushforward inclusion-exclusion identity |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
For a carried RandomVar X:S\to T and target measurable events B,C\in\mathcal A_T, \mu_X(B\cup C)+\mu_X(B\cap C)\sim_R\mu_X(B)+\mu_X(C).

Local inputs:
- `papers/bedc/parts/concrete_instances/164_distribution_namecert_construction.tex`

Rationale:
Distinct companion to candidate 1. Existing BOARD coverage on Distribution↑ pushforward is sigma/finite/disjoint additive (B-475, B-438, B-390) and monotone events (B-462, B-466, B-458) — no entry handles the general two-event overlap case via X^{-1} commutation with union/intersection. The proof transports the source-side ProbSpace inclusion-exclusion (candidate 1) through the existing pushforward row (thm:distribution-pushforward-row) using preimage-commutation lemmas already in the chapter. Lands in 164_distribution_namecert_construction.tex — at 749 lines this is near cap, but the new theorem can land in an obvious sibling file under concrete_instances/distribution/ to honor the split-out discipline rather than landing in the hub.

---

### B-507 - Halting predicate exists iff meta-loop closes at certificate stratum

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | Halting predicate exists iff meta-loop closes at certificate stratum |
| Layer | capstones |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 9/10 |

Problem:
There exists a halting predicate \NameCert_H over the carrier of all naming certificates if and only if there exists a \NameCert-level decision procedure indexed by the certificate-of-certificates carrier.

Local inputs:
- `papers/bedc/parts/capstones/halting_as_form_of_distinction_limit.tex`

Rationale:
Genuine missing dual. halting_as_form_of_distinction_limit.tex packages the forward direction (thm:halting-meta-loop-closure) but not the converse, even though the proof sketch already cites the equivalence. Filling the gap aligns the chapter with the parallel iffs in three_axioms_one_closure.tex (Choice/Quot.sound/propext stratum closures), which are all packaged as full equivalences. The chapter is 56 lines, safely below cap, and the converse is a one-step re-interpretation. No BOARD entry covers halting predicate existence dualities. Concrete biconditional, fits capstones-stratum surface, not a parameter echo.

---

### B-508 - InnerProduct Pythagorean theorem

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | InnerProduct Pythagorean theorem |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 10/10 |
| Novelty | 6/10 |

Problem:
For an $\InnerProductUp$ BHist source, if $x \perp_I y$ for carried vector endpoints $x,y:C_V$, then the diagonal scalar endpoints satisfy $\|x+_V y\|_I^2 \sim_{\mathbb{K}} \|x\|_I^2 +_{\mathbb{K}} \|y\|_I^2$.

Local inputs:
- `papers/bedc/parts/concrete_instances/innerproduct/orthogonality_closure.tex`
- `papers/bedc/parts/concrete_instances/innerproduct/parallelogram_norm_seed.tex`
- `papers/bedc/parts/concrete_instances/innerproduct/norm_metric_seed.tex`
- `papers/bedc/parts/concrete_instances/innerproduct/core_surface.tex`

Rationale:
Halmos/Axler textbook chapter on inner-product spaces opens with three results: orthogonality symmetry, Pythagorean theorem, and parallelogram identity. The chapter has orthogonality symmetry (thm:innerproduct-orthogonality-symmetry-row at orthogonality_closure.tex:1), zero-side and additive-closure rows for orthogonality (thm:innerproduct-orthogonal-additivity-row at orthogonality_closure.tex:67), and the parallelogram identity (thm:innerproduct-parallelogram-identity-row at parallelogram_norm_seed.tex:30) — but Pythagorean is missing. Verified absent: grep across all parts/ finds 'Pythagorean' only in trig identity files (thm:real-analytic-pythagorean, thm:cplx-pythagorean), not in inner-product context. Inputs all present: linearity row thm:innerproduct-vecspace-linearity-row ✓ (used in parallelogram proof to expand $\langle x+y, x+y\rangle$), thm:innerproduct-orthogonality-symmetry-row gives $\langle x,y\rangle\sim_K 0_K \Rightarrow \langle y,x\rangle\sim_K 0_K$ ✓, thm:innerproduct-norm-squared-carrier-row interprets $\|\cdot\|^2$ as the diagonal $\langle\cdot,\cdot\rangle$ ✓, ring zero-addition laws ✓. Proof sketch is a 4-line specialization of the parallelogram proof: expand $\langle x+y,x+y\rangle$ by linearity into $\langle x,x\rangle + \langle x,y\rangle + \langle y,x\rangle + \langle y,y\rangle$, drop the two cross terms by orthogonality + symmetry, repack. 1-3 round closeable. Lands in parallelogram_norm_seed.tex (125 lines) as adjacent theorem.

---

### B-509 - EnumPerm composition associativity

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | EnumPerm composition associativity |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 6/10 |

Problem:
For finite BEDC-history spines $xs,ys,zs,ws$, if $\mathsf{EnumPerm}_{A,\sim_A}(xs,ys)$, $\mathsf{EnumPerm}_{A,\sim_A}(ys,zs)$, and $\mathsf{EnumPerm}_{A,\sim_A}(zs,ws)$ hold, then the two composite enumeration permutations from $xs$ to $ws$ obtained by left-association versus right-association coincide as $\mathsf{EnumPerm}$ witnesses (their forward and inverse position maps are identified).

Local inputs:
- `papers/bedc/parts/concrete_instances/90_finset_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/94_permutation_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/95_symgroup_namecert_construction.tex`

Rationale:
Hungerford ch.I.3 opens with the three group axioms applied to Sym(n): identity, inverse, associativity of permutation composition. The FinSet chapter has reflexivity (thm:enumperm-identity-reflexivity at 90_finset_namecert_construction.tex:528), symmetry (thm:enumperm-inverse-symmetry at 90_finset_namecert_construction.tex:487), and transitivity / composition closure (thm:enumperm-transitivity-by-bijection-composition at 90_finset_namecert_construction.tex:197), with the building-block lem:finset-enum-position-bijection-composition (90_finset_namecert_construction.tex:178). The fourth group axiom — composition associativity — is missing. Verified absent: grep for 'enumperm.assoc' / 'enumeration-permutation-association' returns nothing. SymGroup composition associativity is asserted in thm:symgroup-composition-inverse-action-obligations (95_symgroup_namecert_construction.tex:75) but routes through 'BHist graph reads + Pkg transport' rather than the underlying EnumPerm associativity, leaving the FinSet chapter's permutation algebra incomplete. Closes in 1-3 rounds: function composition over Pos(_) is associative by primitive Lean identity; the EnumPerm definition (forward + inverse + two inverse identities) carries through both bracketings to the same forward-and-inverse pair. Lands in 90_finset_namecert_construction.tex (621 lines, room).

---
