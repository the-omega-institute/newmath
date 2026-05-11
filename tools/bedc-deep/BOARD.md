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

### B-680 - GeneratedSameSig inhabitation iff sameSig

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | GeneratedSameSig inhabitation iff sameSig |
| Layer | proof_obligations |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 7/10 |

Problem:
For any Π, h, and k, Nonempty(GeneratedSameSig(Π,h,k)) holds if and only if sameSig_Π(h,k).

Local inputs:
- `papers/bedc/parts/proof_obligations/exact_globalize.tex`
- `papers/bedc/parts/core/probe_bundles/02_signature_generation.tex`

Rationale:
This is a concrete bridge between the core signature-sameness predicate and the checker-friendly GeneratedSameSig witness object used by exact Globalize. Existing text defines both sides and gives witness projections, but the paper does not appear to contain a theorem label aligning the two interfaces directly. It is a useful low-risk bridge target rather than a marker-only or closurestatus item.

---

### B-681 - GeneratedSameSig append closure

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | GeneratedSameSig append closure |
| Layer | proof_obligations |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 7/10 |

Problem:
If GeneratedSameSig(Π,h,k) and GeneratedSameSig(Θ,h,k), then GeneratedSameSig(BAppend(Π,Θ),h,k).

Local inputs:
- `papers/bedc/parts/proof_obligations/exact_globalize.tex`
- `papers/bedc/parts/core/probe_bundles/02_signature_generation.tex`

Rationale:
This lifts the existing core append closure for sameSig to the checker-facing GeneratedSameSig witness layer consumed by exact Globalize. It is a concrete closure target with downstream proof utility, not a duplicate of the core sameSig append theorem because the conclusion is at the witness-object interface. The proposed files are not hubs and are below the 800-line cap.

---

### B-682 - Entropy public readback bridge boundary

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Entropy public readback bridge boundary |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |

Problem:
If an EntropyUp public readback surface exposes the displayed source carrier, log-partition rows, transported log-weight and IntegralUp readback rows, Cont ledger, Pkg provenance, and consumer-exact boundary, then a conservative paper bridge may read only those rows and cannot import convergence, measure completion, host entropy equality, or host integral equality.

Local inputs:
- `papers/bedc/parts/concrete_instances/170_entropy_namecert_construction.tex`

Rationale:
EntropyUp has public paper closure but no bridge boundary: the BHist measure source and log-partition carrier are defined at papers/bedc/parts/concrete_instances/170_entropy_namecert_construction.tex:9-32; the chapter proves log-partition consumer exhaustion and transport closure at lines 34-89, distribution-integral boundary at lines 91-111, NameCert obligation surface at lines 116-136, log-weight transport determinacy at lines 138-169, and inventory/ledger stability at lines 171-232. Its closure block states that the next paper-axis step is a bridge boundary for the public entropy readback surface at lines 234-245. Prior discovery rejected a generic 'Entropy exported readback surface' as already covered by the distribution-integral boundary, so this candidate deliberately targets the different missing bridge-boundary implication and keeps the exclusions concrete.

---

