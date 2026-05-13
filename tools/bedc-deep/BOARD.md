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

### B-730 - RegularCauchyMesh finite submesh restriction

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | RegularCauchyMesh finite submesh restriction |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |
| Landing kind | existing_chapter_lemma |

Problem:
If an accepted RegularCauchyMeshUp packet restricts its finite mesh-index row to a displayed submesh while retaining the corresponding StreamName windows, RegSeqRat readbacks, DyadicRatCore tolerance rows, DyadicMesh compatibility row, RealUp handoff, transport, continuation, provenance, and local NameCert rows, then the restricted packet is again an accepted RegularCauchyMeshUp carrier and every retained consumer read factors through the restricted rows.

Local inputs:
- `papers/bedc/parts/concrete_instances/3168_regularcauchymesh_namecert_construction.tex`


Pre-TasteGate admission:
- `tastegate_mode`: existing_chapter
- `elimination_plan`: Project the finite mesh-index row to the displayed submesh, restrict each dependent StreamName, RegSeqRat, DyadicRatCore, DyadicMesh, RealUp handoff, transport, continuation, provenance, and NameCert row along that projection, and repack the resulting finite tuple.
- `ripeness_risk`: low, the source chapter is seed-level and the theorem is a direct finite-row restriction companion to the carrier definition

Logic packet discipline:
- `axiom_budget`: B0_finite_witness
- `strength_level`: B0_finite_witness
- `budget_reason`: The weakest visible resource is a finite witness because the submesh is a displayed finite row projection and no choice, compactness, quotient, or limit construction is needed.
- `witness_extractor`: submesh_row_projection
- `existence_mode`: constructive_witness
- `cut_rank`: 1
- `elimination_plan`: Project the finite mesh-index row to the displayed submesh, restrict each dependent StreamName, RegSeqRat, DyadicRatCore, DyadicMesh, RealUp handoff, transport, continuation, provenance, and NameCert row along that projection, and repack the resulting finite tuple.
- `equality_kind`: propositionally_equal
- `interpretation_kind`: conservative_extension
- `resource_trace`: Consumes the finite request row, mesh-index row, StreamName window row, RegSeqRat readback row, DyadicRatCore tolerance ledger, DyadicMesh compatibility row, RealUp handoff row, componentwise hsame transports, Cont routes, Pkg provenance, and local NameCert rows restricted to the displayed submesh.
- `dependency_trace`: Uses def:regular-cauchy-mesh-carrier, def:regular-cauchy-mesh-classifier, thm:regular-cauchy-mesh-namecert-obligation-sketch, and the chapter upgrade path asking for finite mesh coverage in papers/bedc/parts/concrete_instances/3168_regularcauchymesh_namecert_construction.tex.
- `rate_modulus_surface`: The restricted packet preserves the same displayed DyadicRatCore tolerance ledger and StreamName window row for retained mesh cells; no new rate, tail modulus, limit, or completeness principle is introduced.
- `oracle_mode`: proof_search
Rationale:
This is a concrete finite-row locality theorem for an existing RegularCauchyMeshUp chapter. It is not a marker, closurestatus update, or verification-axis item, and it is not already present as a theorem label. The target fills a visible obligation-level gap: the chapter currently gives the carrier, classifier, and five-row NameCert sketch, while the natural downstream use of a finite mesh packet requires restriction to displayed submeshes without exporting any additional analytic structure.

---

### B-731 - HankelVandermonde spectral-shadow bridge

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | HankelVandermonde spectral-shadow bridge |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 6/10 |
| Landing kind | existing_chapter_lemma |

Problem:
If an accepted HankelVandermondeUp packet shares its displayed atom, weight, moment-index, determinant ledger, pairwise-difference, and Vandermonde-square rows with an accepted CollisionKernelSpectrumUp packet through the FoldMomentKernelUp moment surface, then every spectral-shadow consumer read factors through the HankelVandermonde finite determinant ledger and no host matrix or analytic spectrum row is exported.

Local inputs:
- `papers/bedc/parts/concrete_instances/1796_hankelvandermonde_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/1732_collisionkernelspectrum_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/1289_foldmomentkernel_namecert_construction.tex`


Pre-TasteGate admission:
- `tastegate_mode`: existing_chapter
- `elimination_plan`: Cut first through the FoldMomentKernelUp moment-index rows, then through the CollisionKernelSpectrumUp spectral-shadow projection, and finally read the resulting consumer route through the HankelVandermondeUp determinant and Vandermonde-square ledgers.
- `ripeness_risk`: medium, the intended bridge is stated in prose but the proof must align three existing packet surfaces without turning into a restated non-escape theorem

Logic packet discipline:
- `axiom_budget`: B0_finite_witness
- `strength_level`: B0_finite_witness
- `budget_reason`: All visible resources are finite ledgers: determinant-expansion rows, pairwise-difference rows, Vandermonde-square rows, moment-index rows, collision-kernel rows, and spectral-shadow rows.
- `witness_extractor`: hankel_vandermonde_spectral_shadow_route
- `existence_mode`: constructive_witness
- `cut_rank`: 2
- `elimination_plan`: Cut first through the FoldMomentKernelUp moment-index rows, then through the CollisionKernelSpectrumUp spectral-shadow projection, and finally read the resulting consumer route through the HankelVandermondeUp determinant and Vandermonde-square ledgers.
- `equality_kind`: propositionally_equal
- `interpretation_kind`: conservative_extension
- `resource_trace`: Consumes HankelVandermonde rows A,W,M,D,Delta,Q,H,C,P,N; FoldMomentKernel finite moment-index and finite-window rows; and CollisionKernelSpectrum rows G,F,V,I,K,S,H,T,P,N.
- `dependency_trace`: Uses thm:hankel-vandermonde-namecert-obligations, thm:fold-moment-kernel-standard-bridge-surface, thm:fold-moment-kernel-finite-window-restriction-carrier, thm:collision-kernel-spectrum-finite-window-spectral-shadow, thm:collision-kernel-spectrum-ledger-non-escape, and thm:collision-kernel-spectrum-moment-index-projection.
- `oracle_mode`: proof_search
Rationale:
The candidate is not a new object or survey item; it is a bridge lemma between three already-existing finite certificate chapters. It is close to existing non-escape and spectral-shadow projection theorems, so novelty is only threshold-level, but the proposed statement adds a specific HankelVandermonde-to-CollisionKernelSpectrum consumer route that is currently only described in prose. Kept as an existing-chapter lemma, not a new chapter.

---

### B-732 - AuditMapFrontierIndex neighbor restriction

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | AuditMapFrontierIndex neighbor restriction |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |
| Landing kind | existing_chapter_lemma |

Problem:
If an accepted AuditMapFrontierIndexUp packet restricts its neighbouring-map row to a displayed finite subfamily while retaining the local audit row, positive rows, conditional route row, obstruction row, frontier row, synthesis-consumer row, transports, continuations, provenance, and local NameCert rows for that subfamily, then the restricted packet is an accepted frontier index and no unlisted neighbouring map can supply a frontier entry.

Local inputs:
- `papers/bedc/parts/concrete_instances/4518_auditmapfrontierindex_namecert_construction.tex`


Pre-TasteGate admission:
- `tastegate_mode`: existing_chapter
- `elimination_plan`: Project the neighbouring-map row to the displayed finite subfamily and restrict the positive, conditional-route, obstruction, frontier, synthesis-consumer, transport, continuation, provenance, and local NameCert rows to the retained entries.
- `ripeness_risk`: low, the source chapter is a finite frontier-index carrier and the proposed theorem is a direct finite-subfamily locality statement

Logic packet discipline:
- `axiom_budget`: B0_finite_witness
- `strength_level`: B0_finite_witness
- `budget_reason`: The weakest visible resource is a finite witness because the theorem only projects a displayed neighbouring-map row and repacks retained finite certificate coordinates.
- `witness_extractor`: frontier_neighbor_subfamily_projection
- `existence_mode`: constructive_witness
- `cut_rank`: 1
- `elimination_plan`: Project the neighbouring-map row to the displayed finite subfamily and restrict the positive, conditional-route, obstruction, frontier, synthesis-consumer, transport, continuation, provenance, and local NameCert rows to the retained entries.
- `equality_kind`: propositionally_equal
- `interpretation_kind`: conservative_extension
- `resource_trace`: Consumes T,A,E,P,R,O,F,S,H,C,K,N with E restricted to a displayed finite neighbouring-map subfamily and all frontier, obstruction, route, consumer, transport, continuation, provenance, and NameCert rows retained only for that subfamily.
- `dependency_trace`: Uses def:audit-map-frontier-index-carrier and thm:audit-map-frontier-index-namecert-obligations in papers/bedc/parts/concrete_instances/4518_auditmapfrontierindex_namecert_construction.tex.
- `oracle_mode`: proof_search
Rationale:
This is a concrete finite-subfamily restriction theorem inside an existing audit-map frontier chapter. It is not already covered by the carrier or the five NameCert obligations: those bind the frontier index and synthesis handoff, but do not explicitly state locality under displayed neighbouring-map restriction or the corresponding no-unlisted-neighbour non-escape result. The file is a short non-hub landing, so it is safe as an existing-chapter lemma.

---
