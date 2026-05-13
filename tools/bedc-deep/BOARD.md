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

### B-728 - Module LinearMap pointwise zero additive identity

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Module LinearMap pointwise zero additive identity |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 6/10 |
| Landing kind | existing_chapter_lemma |

Problem:
If f has LinearMapCert_R(M,N;f) and z is a pointwise-zero certified LinearMap from M to N, then the pointwise sums x |-> f(x)+_N z(x) and x |-> z(x)+_N f(x) are certified LinearMaps and are pointwise classified with f.

Local inputs:
- `papers/bedc/parts/concrete_instances/linearmap/module_linearmap_certificates.tex`
- `papers/bedc/parts/concrete_instances/linearmap/module_linearmap_kernel_image_and_zero.tex`


Logic packet discipline:
- `axiom_budget`: B0_finite_witness
- `strength_level`: B0_finite_witness
- `budget_reason`: The proof only projects existing finite certificate rows for pointwise sum, pointwise zero, target additive unit, and pointwise classifier packaging; no search, choice, quotient, or limit resource is needed.
- `witness_extractor`: pointwise_sum_and_zero_linear_map_witnesses
- `existence_mode`: constructive_witness
- `cut_rank`: 0
- `equality_kind`: propositionally_equal
- `interpretation_kind`: definitional_extension
- `resource_trace`: Consumes LinearMapCert_R(M,N;f), the pointwise-zero rows for z, two applications of the pointwise-sum certificate, target additive unit rows in the ModuleUp-to-AbGroupUp reduct, and pointwise classifier packaging.
- `dependency_trace`: Uses def:module-linearmap-certificate-package at papers/bedc/parts/concrete_instances/linearmap/module_linearmap_certificates.tex:98, thm:module-linearmap-pointwise-sum-certificate at papers/bedc/parts/concrete_instances/linearmap/module_linearmap_certificates.tex:343, thm:module-zero-linearmap-certificate at papers/bedc/parts/concrete_instances/linearmap/module_linearmap_kernel_image_and_zero.tex:150, and def:linearmap-classifier-specification from papers/bedc/parts/concrete_instances/linearmap/the_certificate.tex:15.
- `oracle_mode`: forbid
Rationale:
This belongs in the LinearMap body, preferably near the pointwise Hom_R(M,N) laws in papers/bedc/parts/concrete_instances/linearmap/module_linearmap_kernel_image_and_zero.tex. The theorem is the textbook additive-identity law for the abelian group of module homomorphisms, standard in any introductory algebra text covering modules, e.g. Dummit-Foote or Hungerford. Evidence for closeability is strong: the paper already has pointwise sum closure at module_linearmap_certificates.tex:343, zero linear-map certification at module_linearmap_kernel_image_and_zero.tex:150, pointwise sum commutativity at module_linearmap_kernel_image_and_zero.tex:100, and associativity at module_linearmap_kernel_image_and_zero.tex:184. A focused grep for pointwise sum identity, additive identity, and zero pointwise sum found only generic zero-row mentions and no theorem label for the identity law, so the target is open and should close by two applications of existing certificates plus the target module additive-unit row.

---


### B-729 - Module LinearMap pointwise inverse additive cancellation

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Module LinearMap pointwise inverse additive cancellation |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 6/10 |
| Landing kind | existing_chapter_lemma |

Problem:
If f has LinearMapCert_R(M,N;f), h(x):=-_N f(x) is its pointwise inverse, and z is a pointwise-zero LinearMap, then the pointwise sums f+h and h+f are certified LinearMaps classified with z.

Local inputs:
- `papers/bedc/parts/concrete_instances/linearmap/module_linearmap_certificates.tex`
- `papers/bedc/parts/concrete_instances/linearmap/module_linearmap_kernel_image_and_zero.tex`
- `papers/bedc/parts/concrete_instances/linearmap/zero_linearmap_classifier_uniqueness.tex`


Logic packet discipline:
- `axiom_budget`: B0_finite_witness
- `strength_level`: B0_finite_witness
- `budget_reason`: The proof is a finite pointwise certificate composition using the already-proved pointwise inverse certificate, pointwise sum certificate, zero map certificate, additive inverse laws, and classifier transitivity.
- `witness_extractor`: pointwise_inverse_sum_zero_witness
- `existence_mode`: constructive_witness
- `cut_rank`: 0
- `equality_kind`: propositionally_equal
- `interpretation_kind`: definitional_extension
- `resource_trace`: Consumes the input LinearMap certificate, constructs h with the existing pointwise inverse certificate, constructs f+h and h+f with the pointwise-sum certificate, compares each value to 0_N by target additive inverse laws, then invokes the zero-map classifier package.
- `dependency_trace`: Uses thm:module-linearmap-pointwise-inverse-certificate at papers/bedc/parts/concrete_instances/linearmap/module_linearmap_certificates.tex:485, thm:module-linearmap-pointwise-sum-certificate at papers/bedc/parts/concrete_instances/linearmap/module_linearmap_certificates.tex:343, thm:module-zero-linearmap-certificate at papers/bedc/parts/concrete_instances/linearmap/module_linearmap_kernel_image_and_zero.tex:150, and thm:module-zero-linearmap-classifier-uniqueness at papers/bedc/parts/concrete_instances/linearmap/zero_linearmap_classifier_uniqueness.tex:1.
- `oracle_mode`: forbid
Rationale:
This is the missing inverse law for the textbook abelian group structure on Hom_R(M,N). The chapter already proves closure under pointwise inverse at module_linearmap_certificates.tex:485 and closure under pointwise addition at module_linearmap_certificates.tex:343, but the law that f plus its pointwise inverse is classified with the zero linear map is not stated as a theorem or labelled corollary; grep for pointwise inverse zero, sum inverse zero, and additive inverse pointwise found only the closure theorem and supporting inverse rows. It should close in one or two Codex rounds because all required ingredients already exist, including zero-map certification and uniqueness in module_linearmap_kernel_image_and_zero.tex:150 and zero_linearmap_classifier_uniqueness.tex:1.

---

