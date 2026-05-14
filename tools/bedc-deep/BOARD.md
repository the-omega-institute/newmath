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

### B-735 - OptionalStopping post-stop tail erasure

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | OptionalStopping post-stop tail erasure |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |
| Landing kind | existing_chapter_lemma |

Problem:
If an accepted OptionalStoppingUp finite carrier has a first displayed stopping branch before the visible bound and a truncation keeps exactly the rows through that branch while deleting later filtration-window rows, then the truncated packet is accepted and its stopped-value row is classifier-equal to the original stopped value.

Local inputs:
- `papers/bedc/parts/concrete_instances/1288_optionalstopping_namecert_construction.tex`


Logic packet discipline:
- `axiom_budget`: B0_finite_witness
- `strength_level`: B0_finite_witness
- `budget_reason`: The claim only projects and repacks a finite carrier tuple already containing the bound, stopped-value row, filtration-window ledger, integrability row, transports, continuation routes, package provenance, and local NameCert row; no limiting, countable, or compactness resource is needed.
- `witness_extractor`: first_stopping_branch_truncation
- `existence_mode`: constructive_witness
- `cut_rank`: 1
- `elimination_plan`: Project the first displayed stopping branch from the original finite carrier, rebuild the truncated carrier from the retained coordinates, and eliminate the stopped-value cut with the bounded stopped-value readback theorem.
- `equality_kind`: propositionally_equal
- `interpretation_kind`: none
- `resource_trace`: Consumes the OptionalStopping finite carrier O=(Omega,X,T,b,V,F,I,H,C,P,N), the stopping-time decision rows T, the bounded index b, the stopped value V, filtration ledger F, integrability row I, componentwise hsame transports H, continuation routes C, package provenance P, and local NameCert row N.
- `dependency_trace`: Uses def:optional-stopping-carrier, thm:optional-stopping-namecert-obligations, thm:optional-stopping-bounded-stopped-value-readback, and thm:optional-stopping-finite-expectation-window from papers/bedc/parts/concrete_instances/1288_optionalstopping_namecert_construction.tex.
- `oracle_mode`: candidate_generation
Rationale:
OptionalStopping is a clear under-covered stochastic subarea: the file gives the finite carrier at papers/bedc/parts/concrete_instances/1288_optionalstopping_namecert_construction.tex:9, says the stopped value is read from the first displayed stopping branch before the bound at :19-:22, proves only bounded stopped-value readback at :56-:65 and finite expectation-window/no-escape boundaries at :69-:91, while rg over BOARD/state found no completed OptionalStopping target beyond paper_index entries. The missing theorem is not a new optional-stopping theorem; it is the canonical finite ledger erasure property forced by the existing carrier.

---


### B-736 - Topology subspace pullback image-factorization

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Topology subspace pullback image-factorization |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |
| Landing kind | existing_chapter_lemma |

Problem:
If a classifier-respecting BHist map f:Y->X lands in a displayed subspace S and i is an ambient open index, then pulling back the subspace-open row S and OpenAt(i,-) along f is equivalent to the ordinary pullback of the ambient open row i along f.

Local inputs:
- `papers/bedc/parts/concrete_instances/topology/pullback_open_rows.tex`
- `papers/bedc/parts/concrete_instances/topology/subspace_open_surface.tex`


Logic packet discipline:
- `axiom_budget`: B0_finite_witness
- `strength_level`: B0_finite_witness
- `budget_reason`: The image-in-subspace witness is supplied pointwise and the proof only rewrites the two displayed membership predicates; it does not construct opens, choose subsets, or use arbitrary-union existence.
- `witness_extractor`: subspace_pullback_image_factor
- `existence_mode`: constructive_witness
- `cut_rank`: 1
- `elimination_plan`: Use the image-in-subspace row S(f(y)) to remove the subspace conjunct from SubOpenAt(i,f(y)), then refold the BHist pullback-open predicate for the ambient open row; classifier transport is inherited from the pullback and subspace transport rows.
- `equality_kind`: equivalent
- `interpretation_kind`: none
- `resource_trace`: Consumes the BHist pullback-open row, the classifier-respecting map row f, the subspace carrier predicate S, same_S projection to same_X, and the ambient indexed-open membership predicate OpenAt(i,-).
- `dependency_trace`: Uses def:topology-bhist-pullback-open-row and thm:topology-pullback-open-row-classifier-transport from papers/bedc/parts/concrete_instances/topology/pullback_open_rows.tex, plus def:topology-bhist-subspace-open-surface and thm:topology-subspace-open-carrier-transport from papers/bedc/parts/concrete_instances/topology/subspace_open_surface.tex.
- `oracle_mode`: candidate_generation
Rationale:
Topology has generic indexed-union and metric-ball BOARD coverage, but the split child files expose two adjacent surfaces without their connecting image-factorization row: pullback rows are defined and closed under finite meet/arbitrary union in papers/bedc/parts/concrete_instances/topology/pullback_open_rows.tex:1-:77, while subspace opens are defined as S(h) and OpenAt(i,h) in papers/bedc/parts/concrete_instances/topology/subspace_open_surface.tex:1-:17 and closed under finite intersection at :38-:55. The missing claim is a concrete bridge between these two existing child-body files, not a new abstract topology schema.

---

