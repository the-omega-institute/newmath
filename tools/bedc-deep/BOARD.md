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

