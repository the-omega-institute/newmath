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

### B-662 - Bundle append Levi residual decomposition

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | Bundle append Levi residual decomposition |
| Layer | core |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
Under BAppend setup, if BAppend(Π,Θ)=BAppend(Ω,Λ), there exists a residual R with either (Ω=BAppend(Π,R) and Θ=BAppend(R,Λ)) or (Π=BAppend(Ω,R) and Λ=BAppend(R,Θ)).

Local inputs:
- `papers/bedc/parts/core/probe_bundles/01_bundle_grammar.tex`

Rationale:
Bundle append currently has fixed-length cancellations and fixed-length split uniqueness but no Levi/overlap classification that drops the length-equality hypothesis. This is the unrestricted structural classifier that the existing cancellation theorems specialize from, and is a natural prerequisite for the unrestricted signature append split (candidate 2). Not a parameter-echo, not a wording variant of any B-### entry.

---


### B-663 - Append sameSig exact split into both components

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | Append sameSig exact split into both components |
| Layer | core |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 7/10 |

Problem:
Under BundleAskPolicy(Π,D), BundleAskPolicy(Θ,D), and h,k admitted by D, sameSig_{BAppend(Π,Θ)}(h,k) implies sameSig_Π(h,k) and sameSig_Θ(h,k).

Local inputs:
- `papers/bedc/parts/core/probe_bundles/02_signature_generation.tex`
- `papers/bedc/parts/core/probe_bundles/01_bundle_grammar.tex`

Rationale:
B-660 covers residual exactness with a known Θ-component; B-659 covers bundle-local same-source membership sharing signatures. Neither gives the unconditional component-split converse to append closure of sameSig. This is the appended-classifier → two-component-classifiers exact split, a genuine converse of the append closure theorem rather than a paraphrase. Lands cleanly in 02_signature_generation.tex.

---


### B-664 - Strict unary prefix trichotomy

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | Strict unary prefix trichotomy |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |

Problem:
Under Unary(h) and Unary(k), exactly one of hsame(h,k), StrictUnaryPrefix(h,k), or StrictUnaryPrefix(k,h) holds.

Local inputs:
- `papers/bedc/parts/concrete_instances/04_nat_namecert_construction.tex`

Rationale:
Nat↑ seeds totality, directed common upper, and strict-prefix asymmetry separately; this is the order-classifier trichotomy that assembles them into a rigid three-way exhaustive-and-exclusive partition. Concrete classification target, not a transport echo, not in paper labels under nat/unary. Single-file landing in the unary section of 04_nat_namecert_construction.tex; file is not near line cap.

---


### B-665 - Second-layer separation is necessary for composite gaps

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | Second-layer separation is necessary for composite gaps |
| Layer | proof_obligations |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 9/10 |

Problem:
There exists a finite CompGap setup with firstGap coverage+separation and secondGap coverage but not separation such that the same source falls into composite gaps of two distinct final tokens with finalSame failing.

Local inputs:
- `papers/bedc/parts/proof_obligations/gap_policy.tex`

Rationale:
Existing ledger composition theorems give the forward direction (first+second separation ⇒ composite separation). The paper currently does not record a witness/obstruction showing second-layer separation cannot be weakened. A concrete two-point witness on b0,b1 final tokens with finalSame=msame closes a genuine gap and converts a sufficient-condition theorem into a tight one. High-novelty obstruction target, fits the proof_obligations layer exactly.

---

