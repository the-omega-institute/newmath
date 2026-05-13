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

### B-714 - Decompiler right-inverse classifier theorem

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | Decompiler right-inverse classifier theorem |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 10/10 |
| Novelty | 9/10 |
| Landing kind | existing_chapter_lemma |

Problem:
If two accepted \(\DecompilerRightInverseUp\) packets share the same displayed compiler graph, decompiler graph, target optimisation row, and paired right-inverse ledger up to componentwise \(\hsame\), then their target-row right-inverse comparisons classify together and no extra inverse data is exported.

Local inputs:
- `papers/bedc/parts/concrete_instances/2833_decompiler_right_inverse_namecert_construction.tex`

Rationale:
This directly fills the gap named by the chapter itself: the current \(\DecompilerRightInverseUp\) surface has carrier, NameCert obligations, and a non-escape boundary, while its closure block says a finite right-inverse classifier theorem is still needed. The claim is a single local classifier-determinacy implication over displayed packet rows and has no BOARD duplicate or matching paper theorem.

---

### B-715 - ContinuationBigStep terminal-read determinacy

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | ContinuationBigStep terminal-read determinacy |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |
| Landing kind | existing_chapter_lemma |

Problem:
If two accepted \(\ContinuationBigStepUp\) packets have classifier-same source row, small-step trace ledger, replay route, and terminal row, then their terminal-read witnesses are classifier-same and both big-step reads factor through the same finite route.

Local inputs:
- `papers/bedc/parts/concrete_instances/3293_continuationbigstep_namecert_construction.tex`

Rationale:
The chapter already exposes the terminal-read witness \(Q\), componentwise transport, replay route, and small-step factorization theorem, but it does not state endpoint determinacy for \(Q\) under fixed source, trace, route, and terminal rows. This is a concrete determinacy target for an existing finite computation packet and is not covered by the existing BOARD title index.

---

### B-716 - TypePreservingCompiler sequential composition

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | TypePreservingCompiler sequential composition |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |
| Landing kind | existing_chapter_lemma |

Problem:
If accepted \(\TypePreservingCompilerUp\) packets compile \(S\) to \(T\) and \(T\) to \(U\), then the relational composite of their compiler graphs determines an accepted \(\TypePreservingCompilerUp\) packet from \(S\) to \(U\) preserving target \(\Ext\) membership and the source/target subject-reduction ledgers.

Local inputs:
- `papers/bedc/parts/concrete_instances/3009_typepreservingcompiler_namecert_construction.tex`

Rationale:
The existing \(\TypePreservingCompilerUp\) chapter has subject-reduction handoff, morphism reading, and ledger boundary theorems, but no sequential composition theorem for two accepted compiler packets. The claim is a concrete closure result over compiler graphs and subject-reduction ledgers, distinct from already-present generic classifier-morphism composition and not merely a verification-axis update.

---

### B-717 - AnalyticContinuationOperation socket extraction

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | AnalyticContinuationOperation socket extraction |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 7/10 |
| Landing kind | existing_chapter_lemma |

Problem:
If an accepted \(\AnalyticContinuationOperationUp\) packet has continuation ledger \(L\) whose branch-obstruction coordinate is displayed as \(B\), then the rows \(F,G,U,A,O,B,H,C,P,N\) determine an accepted \(\AnalyticContinuationSocketUp\) packet and every output \(\HolomorphicUp\) read through the operation factors through that socket.

Local inputs:
- `papers/bedc/parts/concrete_instances/2519_analyticcontinuationoperation_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/2506_analyticcontinuationsocket_namecert_construction.tex`

Rationale:
This is a concrete bridge between two existing adjacent analytic-continuation packet surfaces. The operation chapter exports the larger operation packet and the socket chapter proves socket-internal handoff and non-escape rows, but no paper theorem extracts the socket carrier from an accepted operation packet. The landing is safe in existing concrete instance files and the target is a BEDC-native bridge, not a general analytic-continuation claim.

---

### B-718 - ZetaContinuationSocket to witness carrier bridge

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | ZetaContinuationSocket to witness carrier bridge |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 6/10 |
| Landing kind | existing_chapter_lemma |

Problem:
If an accepted \(\ZetaContinuationSocketUp\) carrier is supplied with the displayed \(\Pkg\) provenance row over the same zeta, eta, pole, functional-equation, trivial-zero, Gamma-boundary, transport, and route coordinates, then it determines an accepted \(\ZetaContinuationWitnessUp\) carrier with the same downstream non-escape boundaries.

Local inputs:
- `papers/bedc/parts/concrete_instances/2589_zetacontinuationsocket_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/2584_zetacontinuationwitness_namecert_construction.tex`

Rationale:
The socket and witness chapters already expose closely aligned zeta-continuation packets, but the paper states only their separate obligation, handoff, and concretization surfaces. A bridge from socket plus provenance to witness is distinct enough to merit a local target because it turns one accepted BEDC packet into the other without exporting RH, zero-location, branch-choice, or completed Gamma data. Novelty is moderate because the two chapters are adjacent and structurally similar, but no existing BOARD entry or paper label covers this carrier bridge.

---
