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

### B-751 - Module zero LinearMap image is the zero fiber

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (both) |
| Object | Module zero LinearMap image is the zero fiber |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 6/10 |
| Landing kind | existing_chapter_lemma |

Problem:
Under certified modules over a shared scalar certificate and a pointwise-zero LinearMap certificate z:M\to N, Im_z(y) implies y\sim_N0_N, and any carried y with y\sim_N0_N lies in Im_z.

Local inputs:
- `papers/bedc/parts/concrete_instances/linearmap/module_linearmap_certificates.tex`
- `papers/bedc/parts/concrete_instances/linearmap/module_linearmap_kernel_image_and_zero.tex`


Pre-TasteGate admission:
- `tastegate_mode`: existing_chapter
- `elimination_plan`: Direct image-witness projection and repacking with cut_rank 0: invert Im_z(y) to a carried source witness x and compose z(x)\sim_N y with the pointwise-zero row; conversely choose the carried source zero endpoint and compose the zero-map row with y\sim_N0_N.
- `ripeness_risk`: low, all required image and zero-map certificate ingredients already land in the LinearMap module files

Logic packet discipline:
- `axiom_budget`: B0_finite_witness
- `strength_level`: B0_finite_witness
- `budget_reason`: The proof consumes only one finite image witness or the distinguished source-zero witness plus classifier symmetry and transitivity, with no search, rate, cover, or choice surface.
- `witness_extractor`: zero_map_image_witness
- `existence_mode`: constructive_witness
- `cut_rank`: 0
- `elimination_plan`: Direct image-witness projection and repacking with cut_rank 0: invert Im_z(y) to a carried source witness x and compose z(x)\sim_N y with the pointwise-zero row; conversely choose the carried source zero endpoint and compose the zero-map row with y\sim_N0_N.
- `equality_kind`: propositionally_equal
- `interpretation_kind`: conservative_extension
- `resource_trace`: For Im_z(y), consume the displayed source witness x with carried evidence and comparison z(x)\sim_N y; for the converse, consume the carried source zero endpoint 0_M and the target comparison y\sim_N0_N.
- `dependency_trace`: Uses def:module-linearmap-image-predicate, thm:module-linearmap-image-submodule-closure for the existing image surface, thm:module-zero-linearmap-certificate for pointwise zero-map certification, and target NameCert equivalence symmetry/transitivity rows.
- `oracle_mode`: forbid
Rationale:
This is a concrete first-course module fact that fits exactly beside the existing LinearMap kernel/image surface. Existing BOARD already covers the zero-map kernel and identity-map image, but not the dual zero-map image exactness. It is not a marker, closurestatus, or Lean-axis task, and it is not merely a parameter echo: it gives a concrete inversion-and-coverage characterization of the image predicate for the zero LinearMap. The local files are below the line cap and include a natural child-file landing, so the downstream theorem can be added without risky hub edits.

---

