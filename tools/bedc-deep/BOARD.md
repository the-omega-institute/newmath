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

### B-741 - KernelAcceptanceWitness public export package

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | KernelAcceptanceWitness public export package |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 6/10 |
| Landing kind | existing_chapter_ledger_row |

Problem:
Under the KernelAcceptanceWitness NameCert setup, if K=(G,A,E,Q,R,H,C,P,N) is an accepted KernelAcceptanceWitness packet satisfying candidate-to-acceptance matching, environment replay, purity-query visibility, and refusal separation, then the public BEDC acceptance-witness export consists exactly of G,A,E,Q,R,H,C,P,N and exports no refused or unresolved row as accepted content.

Local inputs:
- `papers/bedc/parts/concrete_instances/2358_kernelacceptancewitness_namecert_construction.tex`


Pre-TasteGate admission:
- `tastegate_mode`: existing_chapter
- `elimination_plan`: cut_rank 1: project the nine-row KernelAcceptanceWitness carrier, use the local NameCert obligations to identify the accepted, environment, query, refusal, transport, route, provenance, and naming rows, then compose ledger purity with refusal separation to eliminate any route that exports R-side evidence as accepted content.
- `ripeness_risk`: low, the source chapter is short, non-hub, and explicitly names this public export package as the next paper-axis step.

Logic packet discipline:
- `axiom_budget`: B0_finite_witness
- `strength_level`: B0_finite_witness
- `budget_reason`: The claim is a finite packet projection and boundary-separation theorem over displayed certificate rows, with no semantic kernel-completeness or infinite construction requirement.
- `witness_extractor`: acceptance_witness_packet_projection
- `existence_mode`: constructive_witness
- `cut_rank`: 1
- `elimination_plan`: cut_rank 1: project the nine-row KernelAcceptanceWitness carrier, use the local NameCert obligations to identify the accepted, environment, query, refusal, transport, route, provenance, and naming rows, then compose ledger purity with refusal separation to eliminate any route that exports R-side evidence as accepted content.
- `equality_kind`: propositionally_equal
- `interpretation_kind`: conservative_extension
- `resource_trace`: Generated-candidate row G, accepted-declaration row A, environment-ledger row E, axiom-query row Q, refusal-boundary row R, transport row H, continuation row C, provenance row P, and local naming row N.
- `dependency_trace`: Uses def:kernel-acceptance-witness-carrier, thm:kernel-acceptance-witness-namecert-obligations, thm:kernel-acceptance-witness-ledger-purity, and thm:kernel-acceptance-witness-refusal-separation.
- `oracle_mode`: proof_search
Rationale:
This is a BEDC-native finite certificate export theorem in an existing concrete_instances chapter. It is not a Lean marker, closurestatus edit, or general discussion item; it would add a theorem-level public export row that packages existing acceptance, environment, query, and refusal boundaries into the chapter's named next paper-axis step. It is close to existing ledger-purity and refusal-separation results, so novelty is moderate rather than high, but it is not already labeled in the paper and does not duplicate an existing BOARD title.

---


### B-742 - MetaCICCriticalPath NameCert obligation surface

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | MetaCICCriticalPath NameCert obligation surface |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |
| Landing kind | existing_chapter_obligation |

Problem:
Under the MetaCICCriticalPath setup, if K=(S,N,O,U,D,H,C,P,L) is an accepted MetaCICCriticalPath carrier, then its local NameCert obligation surface consists exactly of S,N,O,U,D,H,C,P,L and exports no closed subject-reduction theorem or full closed-consistency theorem.

Local inputs:
- `papers/bedc/parts/concrete_instances/4237_metaciccriticalpath_namecert_construction.tex`


Pre-TasteGate admission:
- `tastegate_mode`: existing_chapter
- `elimination_plan`: cut_rank 1: project the nine-row critical-path packet, use the consistency-handoff theorem for the S,N,H,C,P,L route, use the obstruction-boundary theorem for O,U,D,H, and close by row exhaustion of the carrier without introducing a subject-reduction or full-consistency coordinate.
- `ripeness_risk`: low, the landing file is short, non-hub, and already contains the carrier plus the two component theorems needed for the obligation surface.

Logic packet discipline:
- `axiom_budget`: B0_finite_witness
- `strength_level`: B0_finite_witness
- `budget_reason`: The claim only enumerates and bounds a finite NameCert packet surface; it does not construct normalization, confluence, consistency, or a quotient over terms.
- `witness_extractor`: critical_path_packet_row_projection
- `existence_mode`: constructive_witness
- `cut_rank`: 1
- `elimination_plan`: cut_rank 1: project the nine-row critical-path packet, use the consistency-handoff theorem for the S,N,H,C,P,L route, use the obstruction-boundary theorem for O,U,D,H, and close by row exhaustion of the carrier without introducing a subject-reduction or full-consistency coordinate.
- `equality_kind`: propositionally_equal
- `interpretation_kind`: conservative_extension
- `resource_trace`: Closed-strong-normalization route S, normal-form consistency row N, subject-reduction obstruction row O, substitution-confluence-decidability handoff U, discharge socket D, transport row H, continuation row C, provenance row P, and local naming row L.
- `dependency_trace`: Uses def:metacic-critical-path-packet, thm:metacic-critical-path-consistency-handoff, and thm:metacic-critical-path-obstruction-boundary.
- `oracle_mode`: proof_search
Rationale:
This belongs as an existing-chapter obligation theorem for the MetaCICCriticalPath concrete packet. The paper already has the carrier, the consistency handoff, and the obstruction boundary, but it lacks the single NameCert obligation theorem that states the exact local surface and the non-escape conditions together. It is distinct from the completed MetaCIC discharge-obligation BOARD items, which target specific proof-obligation names rather than this critical-path packet surface.

---

### B-743 - Polynomial normalized addition commutativity

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (codex) |
| Object | Polynomial normalized addition commutativity |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 6/10 |
| Landing kind | existing_chapter_lemma |

Problem:
If a scalar ring supplies additive commutativity together with the polynomial raw-add and trim data, then every pair of finite coefficient spines p and q satisfies PolySame_R(PolyAdd_R(p,q), PolyAdd_R(q,p)).

Local inputs:
- `papers/bedc/parts/concrete_instances/25_polynomial_literal_addtrim_algebra.tex`
- `papers/bedc/parts/concrete_instances/25_polynomial_literal_addtrim_eval.tex`


Pre-TasteGate admission:
- `tastegate_mode`: existing_chapter
- `ripeness_risk`: low, raw-add commutativity and PolyAdd are already present and the landing files are below the line cap

Logic packet discipline:
- `axiom_budget`: B0_finite_witness
- `strength_level`: B0_finite_witness
- `budget_reason`: The theorem only repackages finite coefficient-spine raw-add commutativity through trim normalization and uses no search, limit, quotient, or choice principle.
- `witness_extractor`: finite-spine structural swap plus trim-normalization witness
- `existence_mode`: constructive_witness
- `cut_rank`: 0
- `equality_kind`: propositionally_equal
- `interpretation_kind`: definitional_extension
- `resource_trace`: Consumes the existing raw-add structural swap, scalar additive commutativity row, PolyAdd definition, PolySame classifier, and trim idempotence/zero-tail normalization rows.
- `dependency_trace`: Uses def:polynomial-raw-add-comparison-data, def:polynomial-stability-certificate, thm:polynomial-raw-add-commutativity-from-scalar-additive-commutativity, and the PolyAdd definition in papers/bedc/parts/concrete_instances/25_polynomial_literal_addtrim_eval.tex.
- `oracle_mode`: forbid
Rationale:
This is a small but real normalized-polynomial algebra gap: the paper already has raw-add commutativity and defines PolyAdd as trimmed raw addition, while the existing BOARD index contains polynomial multiplication, raw addition associativity, and distributivity targets but no normalized PolyAdd commutativity target. It is concrete, local to the polynomial add/trim files, and should close by applying raw commutativity to trimmed representatives and folding back PolySame.

---


### B-744 - Polynomial normalized addition zero identity

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (codex) |
| Object | Polynomial normalized addition zero identity |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 6/10 |
| Landing kind | existing_chapter_lemma |

Problem:
If a scalar ring supplies additive zero laws together with the polynomial raw-add and trim data, then every finite coefficient spine p satisfies PolySame_R(PolyAdd_R(p,nil),p) and PolySame_R(PolyAdd_R(nil,p),p).

Local inputs:
- `papers/bedc/parts/concrete_instances/25_polynomial_literal_addtrim_algebra.tex`
- `papers/bedc/parts/concrete_instances/25_polynomial_literal_addtrim_eval.tex`


Pre-TasteGate admission:
- `tastegate_mode`: existing_chapter
- `ripeness_risk`: low, the needed zero-tail trim stability and PolyAdd definition already exist

Logic packet discipline:
- `axiom_budget`: B0_finite_witness
- `strength_level`: B0_finite_witness
- `budget_reason`: The proof is finite recursion over coefficient spines plus trim stability, so the weakest visible resource is a finite constructive witness.
- `witness_extractor`: finite-spine raw-add zero classifier plus trim witness
- `existence_mode`: constructive_witness
- `cut_rank`: 0
- `equality_kind`: propositionally_equal
- `interpretation_kind`: definitional_extension
- `resource_trace`: Consumes raw-add recursion, nil zero-remainder, scalar additive left-zero and right-zero rows, trim idempotence, and the normalized PolySame classifier.
- `dependency_trace`: Uses def:polynomial-raw-add-comparison-data, def:classified-zero-remainder-spine, def:polynomial-stability-certificate, lem:polynomial-raw-add-zero-tail-trim-stability, prop:polynomial-raw-add-right-zero-tail-invariance, and PolyAdd in papers/bedc/parts/concrete_instances/25_polynomial_literal_addtrim_eval.tex.
- `oracle_mode`: forbid
Rationale:
This fills a distinct normalized-addition identity row, not just another spelling of the existing raw zero-tail invariance. The paper has multiplication zero and raw-add trim-stability material, but no close label for PolyAdd zero identity; the theorem is standard, local, and useful before any larger polynomial-ring package.

---


### B-745 - Module LinearMap zero-map kernel is whole source

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (codex) |
| Object | Module LinearMap zero-map kernel is whole source |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 6/10 |
| Landing kind | existing_chapter_lemma |

Problem:
If z:M->N is pointwise classified with 0_N under ModuleUp(R,M) and ModuleUp(R,N), then every carried source endpoint x lies in Ker_z, and every Ker_z witness projects to carriedness of x.

Local inputs:
- `papers/bedc/parts/concrete_instances/linearmap/module_linearmap_kernel_image_and_zero.tex`
- `papers/bedc/parts/concrete_instances/linearmap/module_linearmap_certificates.tex`


Pre-TasteGate admission:
- `tastegate_mode`: existing_chapter
- `ripeness_risk`: low, the kernel predicate and zero-map certificate are already present in nearby linear-map files

Logic packet discipline:
- `axiom_budget`: B0_finite_witness
- `strength_level`: B0_finite_witness
- `budget_reason`: The theorem unfolds a predicate-defined zero fiber and packages pointwise-zero rows; no quotient, extensionality, or non-finite construction is needed.
- `witness_extractor`: source carried endpoint paired with the pointwise zero comparison z(x)~0_N
- `existence_mode`: constructive_witness
- `cut_rank`: 0
- `equality_kind`: equivalent
- `interpretation_kind`: definitional_extension
- `resource_trace`: Consumes the kernel predicate, source carried endpoint, pointwise-zero LinearMap rows, target zero classifier, and kernel witness projection.
- `dependency_trace`: Uses def:module-linearmap-kernel-predicate in papers/bedc/parts/concrete_instances/21_module_linearmap_kernel_and_inverse_action.tex and thm:module-zero-linearmap-certificate plus related zero-map rows in papers/bedc/parts/concrete_instances/linearmap/module_linearmap_kernel_image_and_zero.tex.
- `oracle_mode`: forbid
Rationale:
This is a concrete exactness theorem for an existing predicate carrier, not a parameter echo: it identifies the zero map's kernel with the whole carried source. Existing BOARD entries cover LinearMap additive identity and inverse cancellation, and the paper has kernel submodule closure and the injectivity-kernel criterion, but not the zero-map kernel exactness row.

---


### B-746 - Module identity LinearMap image is whole target

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (codex) |
| Object | Module identity LinearMap image is whole target |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 6/10 |
| Landing kind | existing_chapter_lemma |

Problem:
If id_M carries the Module LinearMap identity certificate, then every carried endpoint y:M satisfies Im_id(y), and every Im_id(y) witness projects to carriedness of y.

Local inputs:
- `papers/bedc/parts/concrete_instances/linearmap/module_linearmap_kernel_image_and_zero.tex`
- `papers/bedc/parts/concrete_instances/linearmap/module_linearmap_certificates.tex`


Pre-TasteGate admission:
- `tastegate_mode`: existing_chapter
- `ripeness_risk`: low, the identity LinearMap certificate and image predicate are already in the local linearmap surface

Logic packet discipline:
- `axiom_budget`: B0_finite_witness
- `strength_level`: B0_finite_witness
- `budget_reason`: The proof chooses y as its own finite image witness and unfolds the image predicate, so a finite constructive witness is sufficient.
- `witness_extractor`: identity-image witness x:=y with id_M(y)~y
- `existence_mode`: constructive_witness
- `cut_rank`: 0
- `equality_kind`: equivalent
- `interpretation_kind`: definitional_extension
- `resource_trace`: Consumes the identity LinearMap certificate, source and target carriedness rows for the same module, image predicate witness, and module classifier reflexivity.
- `dependency_trace`: Uses thm:module-linearmap-identity-certificate and def:module-linearmap-image-predicate in papers/bedc/parts/concrete_instances/linearmap/module_linearmap_certificates.tex, together with image closure material in papers/bedc/parts/concrete_instances/linearmap/module_linearmap_kernel_image_and_zero.tex.
- `oracle_mode`: forbid
Rationale:
This is a concrete image-coverage row for an existing LinearMap predicate, and it is not covered by the current BOARD titles or the paper's image submodule closure theorem. It gives the expected exactness boundary for the identity map using only the existing image predicate and identity certificate.

---

