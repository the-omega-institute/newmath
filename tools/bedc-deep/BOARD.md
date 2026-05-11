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

### B-677 - Signature empty-result iff empty bundle

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | Signature empty-result iff empty bundle |
| Layer | core |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 6/10 |

Problem:
Under Sig(Π,h,r,Δ), hsame(r,emp) holds if and only if Π = Bnil.

Local inputs:
- `papers/bedc/parts/core/probe_bundles/02_signature_generation.tex`

Rationale:
This is a concrete inversion/classification theorem over the existing signature-generation surface. The paper already has the two directional ingredients in adjacent theorem blocks, but not the hsame-level iff for an arbitrary generated result r under a single Sig premise. It would make the empty-result boundary explicit without duplicating an existing BOARD title or paper theorem label, and the landing file is below the line cap.

---

### B-679 - Three-bundle signature cut inversion

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | Three-bundle signature cut inversion |
| Layer | core |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
Under Sig(BAppend(Π,BAppend(Θ,Ω)),h,u,Λ), there exist component results s, t, w, intermediate continuations b and u′, and ledgers witnessing Sig(Π,h,s), Sig(Θ,h,t), Sig(Ω,h,w), Cont(w,t,b), Cont(b,s,u′), and hsame(u,u′).

Local inputs:
- `papers/bedc/parts/core/probe_bundles/01_bundle_grammar.tex`
- `papers/bedc/parts/core/probe_bundles/02_signature_generation.tex`

Rationale:
This is a genuine reverse factorization theorem for triple append at the signature-generation layer. The paper already has binary append inversion and forward three-bundle coherence, but not the reverse cut decomposition from one right-associated signature into three component signatures and two continuation cuts. It is distinct from existing gap-composition BOARD entries and has safe local landing files.

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
