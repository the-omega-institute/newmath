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

### B-708 - CauchyOscillation seal handoff factorization

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | CauchyOscillation seal handoff factorization |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |
| Landing kind | existing_chapter_obligation |

Problem:
If an accepted CauchyOscillationUp packet exports a RealUp seal handoff S, then every consumer read of S factors through the same finite tail window W, threshold schedule M, dyadic tolerance Q, and oscillation ledger T before the seal is available.

Local inputs:
- `papers/bedc/parts/concrete_instances/1734_cauchyoscillation_namecert_construction.tex`

Rationale:
This is a concrete finite-packet obligation inside the existing CauchyOscillationUp chapter. The current paper defines the tail window, modulus schedule, tolerance, oscillation ledger, seal handoff, transports, continuation routes, provenance, and local NameCert rows, and it states oscillation-bound exactness and ledger non-escape, but it does not isolate the RealUp seal handoff as its own consumer factorization theorem. It is not a new chapter: the smallest BEDC-native landing is an existing-chapter obligation/lemma tying the displayed seal row to the already named W,M,Q,T dependency surface.

---


### B-709 - CertificateCompiler triple composition associativity

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | CertificateCompiler triple composition associativity |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |
| Landing kind | existing_chapter_ledger_row |

Problem:
If three accepted CertificateCompilerUp packets are composable along displayed middle NameCert rows, then the two relational graph composites classify by the same displayed graph, edge-landing, classifier-transport, and continuation-compatibility rows.

Local inputs:
- `papers/bedc/parts/concrete_instances/1965_certificatecompiler_namecert_construction.tex`

Rationale:
This lands cleanly as a finite ledger row for the existing CertificateCompilerUp chapter. The paper already contains the carrier, classifier, NameCert obligations, binary composition stability, and identity ledger, while the proposed target asks for the missing three-packet associativity boundary of the displayed relational graph composite. It stays within graph rows, landing rows, classifier transport, continuation compatibility, hsame, provenance, and local NameCert evidence, so it is not an external categorical-law expansion and is distinct from existing BOARD entries.

---

