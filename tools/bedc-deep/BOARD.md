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

### B-710 - FiniteMultiHist subpacket restriction

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | FiniteMultiHist subpacket restriction |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 6/10 |
| Landing kind | existing_chapter_lemma |

Problem:
If an accepted FiniteMultiHistPacketUp carrier is restricted to a finite displayed subfamily of observer rows and the corresponding component ledgers, pairwise hsame rows, Cont routes, package provenance, and no-global-sync boundary are projected with it, then the projected packet is again an accepted FiniteMultiHistPacketUp carrier with the same no-sync boundary.

Local inputs:
- `papers/bedc/parts/concrete_instances/1941_finite_multihist_packet_namecert_construction.tex`

Rationale:
The candidate is a concrete closure lemma for an existing short concrete-instance chapter, not a marker or closurestatus task. The current FiniteMultiHistPacketUp file defines the finite observer-history packet and proves NameCert obligations, hsame transport, no-sync boundary, and causal-interface input, but it does not state the finite subfamily restriction closure. The target is distinct from existing BOARD restriction carriers because it concerns the multi-Hist packet rows and preserves the no-global-sync boundary, while still fitting a standard BEDC carrier-projection proof shape. The landing file is safe and not a hub.

---


### B-711 - AuditGateBoundary to AuditMembrane refusal bridge

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | AuditGateBoundary to AuditMembrane refusal bridge |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |
| Landing kind | existing_chapter_obligation |

Problem:
If an AuditMembraneUp packet uses as its gate surface the source-token, dependency, target-resolution, origin/import, and GAP rows of an accepted AuditGateBoundaryUp packet, then every item refused by the AuditGateBoundary row remains refused at the AuditMembrane boundary and cannot be exported as substrate theorem content.

Local inputs:
- `papers/bedc/parts/concrete_instances/2248_auditgateboundary_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/2243_auditmembrane_namecert_construction.tex`

Rationale:
The candidate is a concrete bridge obligation between two existing audit chapters. AuditGateBoundaryUp already exposes source-token, dependency, target-resolution, origin/import, and GAP boundary rows, while AuditMembraneUp already states its own refusal and consumer boundary for a gate surface; the missing claim is the preservation bridge when the membrane gate is instantiated by the AuditGateBoundary packet. This is not a generic parameter-transport echo because it links two named concrete carriers and preserves refusal/non-export across the boundary. The files are short, non-hub landing files, and the theorem can land locally without creating a new chapter.

---

