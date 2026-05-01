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

### B-07 - Descent certificate composition

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Descent certificate composition |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 7/10 |

Problem:
Under the NameCert descent setup, if δ : DescentCertificate Source Mid sourceSame midSame and ε : DescentCertificate Mid Target midSame targetSame, then λ a => ε.map (δ.map a) carries a DescentCertificate Source Target sourceSame targetSame.

Local inputs:
- `papers/bedc/parts/hardening/02_typed_name_certificate_instances.tex`
- `papers/bedc/parts/core/08_typed_naming_certificates.tex`
- `lean4/BEDC/FKernel/NameCert.lean`
- `lean4/BEDC/FKernel/NameCert/Descent.lean`

Rationale:
The descent layer exposes a single certificate with a map and a sameness-respect proof, and the surrounding text uses descent as a reusable transport mode across concrete certificate families. The missing structural step is closure under composition: without it, chained payload or certificate transports must be rebuilt manually instead of following from the descent interface itself.

---


### B-08 - Semantic certificate presentation weakening

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Semantic certificate presentation weakening |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |

Problem:
Under the SemanticNameCert setup, if cert : SemanticNameCert S P L C, ∀h, P h -> P' h, and ∀h, L h -> L' h, then SemanticNameCert S P' L' C.

Local inputs:
- `papers/bedc/parts/core/08_typed_naming_certificates.tex`
- `papers/bedc/parts/hardening/02_typed_name_certificate_instances.tex`
- `lean4/BEDC/FKernel/NameCert.lean`

Rationale:
Concrete certificates repeatedly separate a core semantic certificate from presentation predicates and ledger predicates. Existing theorems project fields out of a semantic certificate and build selected concrete certificates, but there is no general lemma saying that weakening the public pattern and ledger presentations preserves the same semantic certificate.

---


### B-09 - Tagged option map relation endpoint transport

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Tagged option map relation endpoint transport |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 7/10 |

Problem:
Under the tagged option payload descent setup, if TaggedOptionMapRel S T δ h k, hsame h h', and hsame k k', then TaggedOptionMapRel S T δ h' k'.

Local inputs:
- `papers/bedc/parts/concrete_instances/option/06_tagged_option_payload_descent.tex`
- `papers/bedc/parts/concrete_instances/option/02_tagged_option_namecert.tex`
- `lean4/BEDC/Derived/OptionUp/PayloadDescent.lean`
- `lean4/BEDC/Derived/OptionUp.lean`

Rationale:
TaggedOptionMapRel is the concrete bridge between a nullable source endpoint and its mapped target endpoint, and its definition is expressed through endpoint sameness to empty or one-step histories. The current theory proves classification preservation, but the relation itself lacks the expected closure under replacing either endpoint by an hsame endpoint.

---


### B-10 - Option ledger source monotonicity

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Option ledger source monotonicity |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 6/10 |

Problem:
Under nullable option source inclusion, if ∀h, S h -> T h and OptionHistoryLedgerPolicy S raw visible holds, then OptionHistoryLedgerPolicy T raw visible holds.

Local inputs:
- `papers/bedc/parts/concrete_instances/option/02_tagged_option_namecert.tex`
- `lean4/BEDC/Derived/OptionUp.lean`

Rationale:
The option layer has source monotonicity for the carrier and classifier predicates, while the ledger policy is the carrier together with the raw-to-visible endpoint link. Since ledger predicates are used as certificate-facing evidence, the monotonicity theorem should also exist at that level instead of requiring consumers to unfold the ledger definition.

---


### B-11 - Product ledger source monotonicity

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Product ledger source monotonicity |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 6/10 |

Problem:
Under product source inclusions, if ∀h, L h -> L' h, ∀h, R h -> R' h, and ProdHistoryLedgerPolicy L R raw visible holds, then ProdHistoryLedgerPolicy L' R' raw visible holds.

Local inputs:
- `papers/bedc/parts/concrete_instances/09_prod_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/09_prod_ledger_and_semantic_certificate.tex`
- `lean4/BEDC/Derived/ProdUp.lean`
- `lean4/BEDC/Derived/ProdUp/SourceMonotonicity.lean`

Rationale:
Product source monotonicity is already represented for carriers and classifiers, but the public ledger policy sits one layer above those predicates. A direct ledger monotonicity theorem would connect the source-weakening results to the semantic certificate ledger interface without exposing the internal carrier conjunction at every use site.

---


### B-12 - Sum ledger source weakening

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Sum ledger source weakening |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 6/10 |

Problem:
Under sum source inclusions, if ∀h, Left h -> Left' h, ∀h, Right h -> Right' h, and SumHistoryLedgerPolicy Left Right raw visible holds, then SumHistoryLedgerPolicy Left' Right' raw visible holds.

Local inputs:
- `papers/bedc/parts/concrete_instances/10_sum_carrier_aware_branch_partition.tex`
- `papers/bedc/parts/concrete_instances/sum/ledger_and_semantic_certificate.tex`
- `lean4/BEDC/Derived/SumUp/Ledger.lean`
- `lean4/BEDC/Derived/SumUp/Branch.lean`

Rationale:
The sum development contains branch and source weakening results for the carrier/classifier layer, while the ledger policy is the form consumed by certificate construction. A one-step ledger weakening theorem would make the connection explicit and prevent the ledger certificate path from relying on manual unfolding.

---


### B-13 - Framed list bridge endpoint transport

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Framed list bridge endpoint transport |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |

Problem:
Under the framed list bridge setup, if FramedListBridgeClassifier A Rel h k, hsame h h', and hsame k k', then FramedListBridgeClassifier A Rel h' k'.

Local inputs:
- `papers/bedc/parts/concrete_instances/list/11_framed_endpoint_bridge.tex`
- `lean4/BEDC/Derived/ListUp/FramedEndpoint.lean`

Rationale:
The framed list bridge classifier packages represented source and displayed endpoints, and the file already proves hsame transport for framed spine representations. The classifier built from those representations should inherit endpoint transport, but that closure is not stated as its own theorem.

---


### B-14 - Framed list bridge source refinement

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Framed list bridge source refinement |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |

Problem:
Under framed list source refinement, if ∀x, A x -> B x, ∀x y, RelA x y -> RelB x y, and FramedListBridgeClassifier A RelA h k holds, then FramedListBridgeClassifier B RelB h k holds.

Local inputs:
- `papers/bedc/parts/concrete_instances/list/11_framed_endpoint_bridge.tex`
- `papers/bedc/parts/concrete_instances/list/11_cons_boundary_and_source.tex`
- `lean4/BEDC/Derived/ListUp/FramedEndpoint.lean`

Rationale:
The unframed list layer discusses source and relation weakening, while the framed endpoint bridge is the certificate-facing package for displayed list endpoints. The framed bridge lacks the analogous refinement theorem, leaving a gap between source weakening and the framed semantic certificate construction.

---


### B-15 - Product pair fixed-left tail uniqueness

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Product pair fixed-left tail uniqueness |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 7/10 |

Problem:
Under product pair representation, if ProdPairRep L R h l r and ProdPairRep L R h l r' hold for the same endpoint and left component, then hsame r r'.

Local inputs:
- `papers/bedc/parts/concrete_instances/09_prod_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/09_prod_componentwise_history_classifier_endpoints.tex`
- `lean4/BEDC/Derived/ProdUp/PairRepresentation.lean`
- `lean4/BEDC/FKernel/Cont.lean`

Rationale:
The product theory distinguishes generated endpoint facts from stronger coherence assumptions about pair readback. Fixed-left tail uniqueness is a narrow generated fact obtainable from continuation cancellation, and stating it would clarify exactly which part of product pair coherence is theorem-level rather than policy-level.

---


### B-16 - Product pair fixed-right head uniqueness

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Product pair fixed-right head uniqueness |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 7/10 |

Problem:
Under product pair representation, if ProdPairRep L R h l r and ProdPairRep L R h l' r hold for the same endpoint and right component, then hsame l l'.

Local inputs:
- `papers/bedc/parts/concrete_instances/09_prod_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/09_prod_componentwise_history_classifier_endpoints.tex`
- `lean4/BEDC/Derived/ProdUp/PairRepresentation.lean`
- `lean4/BEDC/FKernel/Cont.lean`

Rationale:
This is the dual fixed-component fact to tail uniqueness. It belongs directly to the product pair representation layer and would help separate cancellation consequences of the continuation kernel from the stronger external coherence premise used for full componentwise readback.

---

