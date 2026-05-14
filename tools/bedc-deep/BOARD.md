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

### B-750 - CookFrontierWitness replay-audit route determinacy

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | CookFrontierWitness replay-audit route determinacy |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |
| Landing kind | existing_chapter_lemma |

Problem:
If two accepted CookFrontierWitnessUp packets share the frontier-coordinate row, three compile-stage rows, halted-target row, replay-audit row, obstruction boundary, componentwise transport, continuation route, provenance, and local naming rows, then any frontier-coordinate read exposed by either packet is hsame under that same finite replay route.

Local inputs:
- `papers/bedc/parts/concrete_instances/6347_cookfrontierwitness_namecert_construction.tex`


Pre-TasteGate admission:
- `tastegate_mode`: existing_chapter
- `elimination_plan`: cut_rank 1: project F,M,Y,R,T,A,O,H,C,P,N from both accepted packets, use A as the replay-audit cut through R,Y,M back to T, then apply componentwise hsame transport to identify the exposed frontier-coordinate read.
- `ripeness_risk`: low, the source file is short and already states the finite carrier and obligation surface needed for a local lemma.

Logic packet discipline:
- `axiom_budget`: B0_finite_witness
- `strength_level`: B0_finite_witness
- `budget_reason`: The theorem only compares displayed finite BHist rows and a recorded replay-audit route, with no halting oracle, host compiler equality, unbounded trace, or universality principle.
- `witness_extractor`: cook_replay_audit_route_projection
- `existence_mode`: constructive_witness
- `cut_rank`: 1
- `elimination_plan`: cut_rank 1: project F,M,Y,R,T,A,O,H,C,P,N from both accepted packets, use A as the replay-audit cut through R,Y,M back to T, then apply componentwise hsame transport to identify the exposed frontier-coordinate read.
- `equality_kind`: bisimilar
- `interpretation_kind`: none
- `resource_trace`: Consumes the CookFrontierWitnessUp packet rows F,M,Y,R,T,A,O,H,C,P,N: frontier coordinate, three compile-stage rows, halted target, replay audit, obstruction boundary, hsame transports, Cont continuation, Pkg provenance, and local NameCert row.
- `dependency_trace`: Uses the CookFrontierWitnessUp carrier and local NameCert obligation surface in papers/bedc/parts/concrete_instances/6347_cookfrontierwitness_namecert_construction.tex; adjacent anchors are Cook frontier coordinate, cellular automaton NameCert, and halting diagonal NameCert as already cited by that packet.
- `oracle_mode`: candidate_generation
Rationale:
The candidate is a concrete two-packet determinacy lemma for an existing finite BEDC packet. The paper currently exposes the CookFrontierWitnessUp carrier and obligations, including the replay-audit row, but it does not already contain a theorem that duplicate accepted packets with the same displayed route expose the same frontier-coordinate read. It is not a marker, closurestatus item, or abstract parameter echo; it is a local route-determinacy closure target with safe landing-file size.

---

