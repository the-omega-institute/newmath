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

### B-725 - DoCalculus intervention prefix locality

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | DoCalculus intervention prefix locality |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |
| Landing kind | existing_chapter_lemma |

Problem:
If an accepted \DoCalculusUp packet restricts its finite intervention ledger to a displayed prefix whose observed-variable, adjustment, independence, distribution, and expectation rows are retained, then every intervention-facing read for that prefix factors through the retained rows and cannot read a later intervention row.

Local inputs:
- `papers/bedc/parts/concrete_instances/1784_docalculus_namecert_construction.tex`


Logic packet discipline:
- `axiom_budget`: B0_finite_witness
- `strength_level`: B0_finite_witness
- `budget_reason`: The target is a finite prefix projection of an already displayed intervention ledger; all rows are inherited from the packet, so the weakest adequate resource is a finite witness for the retained prefix and its retained route entries.
- `witness_extractor`: intervention_prefix_subledger
- `existence_mode`: constructive_witness
- `cut_rank`: 1
- `elimination_plan`: Eliminate the cut through the full intervention packet by projecting the prefix rows from I,V,A,M,R,H,C,P,N, then reusing the existing non-escape argument on the restricted route family.
- `equality_kind`: propositionally_equal
- `interpretation_kind`: none
- `resource_trace`: Consumes the finite intervention ledger I, observed-variable row V, adjustment ledger A, distribution rows M, independence certificates R, expectation row J, export row E, hsame rows H, Cont routes C, package row P, and local naming row N; no causal graph or counterfactual selector is introduced.
- `dependency_trace`: The DoCalculus carrier defines I as a finite intervention ledger with displayed intervention order at papers/bedc/parts/concrete_instances/1784_docalculus_namecert_construction.tex:35-37, and the intervention non-escape theorem says every intervention-facing consumer factors through I,V,A,M,R,H,C,P,N at papers/bedc/parts/concrete_instances/1784_docalculus_namecert_construction.tex:136-145.
- `oracle_mode`: witness_synthesis
Rationale:


---


### B-726 - EnrichedCat two-step composition reassociation

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | EnrichedCat two-step composition reassociation |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |
| Landing kind | existing_chapter_lemma |

Problem:
If an accepted \EnrichedCatUp packet contains three composable hom-object rows and both displayed two-step composition routes, then the consumed \MonoidalCatUp associator row classifies the two composite endpoint rows through the same public packet surface.

Local inputs:
- `papers/bedc/parts/concrete_instances/160_enrichedcat_namecert_construction.tex`


Logic packet discipline:
- `axiom_budget`: B0_finite_witness
- `strength_level`: B0_finite_witness
- `budget_reason`: The associator and both composition routes are supplied as finite packet rows; the proof only follows displayed hom-object, tensor-composition, hsame, Cont, and Pkg rows.
- `witness_extractor`: enriched_two_step_associator_route
- `existence_mode`: constructive_witness
- `cut_rank`: 1
- `elimination_plan`: Cut through the consumed MonoidalCatUp boundary: project the two composition routes, apply the displayed associator transport row, and repack the resulting endpoint comparison into the EnrichedCat public packet.
- `equality_kind`: propositionally_equal
- `interpretation_kind`: none
- `resource_trace`: Consumes C_obj, M_tensor, H_hom, H_comp, T_hsame, P_Pkg, and R_Cont; the only coherence resource is the associator row already exposed by the consumed MonoidalCatUp dependency.
- `dependency_trace`: The packet stores hom-object, identity, composition, hsame, Pkg, and finite Cont rows at papers/bedc/parts/concrete_instances/160_enrichedcat_namecert_construction.tex:9-33; the tensor-composition scope theorem says compositions read adjacent hom-object rows and the tensor-composition boundary at papers/bedc/parts/concrete_instances/160_enrichedcat_namecert_construction.tex:61-68; the monoidal boundary isolates associator and unit-transport rows at papers/bedc/parts/concrete_instances/160_enrichedcat_namecert_construction.tex:161-181.
- `oracle_mode`: proof_search
Rationale:


---


### B-727 - ContextFreeGrammar derivation prefix carrier

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | ContextFreeGrammar derivation prefix carrier |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |
| Landing kind | existing_chapter_lemma |

Problem:
If an accepted \ContextFreeGrammarUp packet has a finite derivation ledger split into a displayed prefix and suffix, then the prefix ledger repacks as an accepted derivation segment over the same start row, production ledger, transport rows, continuation routes, and package provenance.

Local inputs:
- `papers/bedc/parts/concrete_instances/1007_contextfreegrammar_namecert_construction.tex`


Logic packet discipline:
- `axiom_budget`: B0_finite_witness
- `strength_level`: B0_finite_witness
- `budget_reason`: A displayed split of a finite derivation ledger supplies the witness; the proof is finite prefix projection and repacking over already visible production and continuation rows.
- `witness_extractor`: cfg_derivation_prefix_subledger
- `existence_mode`: constructive_witness
- `cut_rank`: 1
- `elimination_plan`: Eliminate the split cut by projecting the prefix entries from d, keeping production witnesses from P and route entries from c, then applying production stability to each retained step.
- `equality_kind`: propositionally_equal
- `interpretation_kind`: none
- `resource_trace`: Consumes Sigma,N,S,P,w,d,y,h,c,p,n but retains only S, P, the prefix of d, the corresponding hsame transports, Cont routes, Pkg provenance, and local NameCert row; no parse tree, pumping theorem, Chomsky normal form, or recognizer completeness is used.
- `dependency_trace`: The carrier records the finite production ledger P and finite derivation ledger d at papers/bedc/parts/concrete_instances/1007_contextfreegrammar_namecert_construction.tex:27-39; derivation concatenation is already available at papers/bedc/parts/concrete_instances/1007_contextfreegrammar_namecert_construction.tex:75-98; terminal-yield windows are handled only when a final terminal readback row is present at papers/bedc/parts/concrete_instances/1007_contextfreegrammar_namecert_construction.tex:124-160.
- `oracle_mode`: witness_synthesis
Rationale:


---
