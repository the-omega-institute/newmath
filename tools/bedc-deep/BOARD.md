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

### B-687 - FreeMonoid empty concatenation inversion

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | FreeMonoid empty concatenation inversion |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |

Problem:
If accepted FreeMonoidUp words u and v have concatenation u·v classified with the empty word under the FreeMonoidUp classifier, then u and v are each classified with the empty word under the same payload, ListUp, NatUp, and MonoidUp setup.

Local inputs:
- `papers/bedc/parts/concrete_instances/642_freemonoid_namecert_construction.tex`

Rationale:
The local carrier explicitly presents a FreeMonoidUp word as a finite BHist spine with ListUp positions, a NatUp length row, payload entries, and Cont routes for empty word, singleton insertion, and concatenation at papers/bedc/parts/concrete_instances/642_freemonoid_namecert_construction.tex:11-30. The chapter proves empty word unit laws at lines 32-40 and concatenation associativity at lines 53-66, and its normal-form theorem says consumer reads have exactly three ledger shapes: empty word, singleton insertion, or concatenation at lines 117-124. Focused rg for `freemonoid.*empty.*concat|concat.*empty.*freemonoid|freemonoid.*inversion|empty word.*inversion` returned only one FreeMonoid hit, the scope sentence at line 168, and no theorem label for empty-concat inversion. This is a concrete inversion result about the existing concatenation ledger, not parameter transport, and the target file has 174 lines with 5 theorem-like blocks.

---

### B-688 - Trie prefix subledger restriction carrier

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Trie prefix subledger restriction carrier |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
If an accepted TrieUp source packet is restricted to a finite displayed prefix-closed subledger of its key-path, optional-payload, branch, depth, transport, continuation, and provenance rows, then the restricted packet is again accepted as a TrieUp source packet under the same BoolUp, ListUp, OptionUp, NatUp, and BitVectorUp dependencies.

Local inputs:
- `papers/bedc/parts/concrete_instances/789_trie_namecert_construction.tex`

Rationale:
TrieUp is locally defined as the finite packet T=(k,v,l,b,p), with key-path, optional terminal payload, NatUp depth ledger, BoolUp branch ledger, and package provenance coordinates at papers/bedc/parts/concrete_instances/789_trie_namecert_construction.tex:10-37. Existing theorem coverage proves carrier stability under displayed hsame/Cont transport at lines 39-45, ledger coverage at lines 83-90, and lists prefix-branch determinacy as a NameCert obligation item at lines 115-123, but no standalone closure theorem restricts the finite branch ledger to a prefix-closed subpacket. Focused rg for `trie.*prefix.*restriction|trie.*restriction|trie.*subledger` returned no Trie theorem label; hits were unrelated files and one BOARD analogy for PersistentHomUp, not TrieUp. This is a finite-carrier restriction theorem, not a classifier-transport echo, and the target file has 163 lines with 4 theorem-like blocks.

---

### B-690 - LocatedCauchy constant window degeneracy

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | LocatedCauchy constant window degeneracy |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 7/10 |
| Novelty | 7/10 |

Problem:
If a LocatedCauchyUp packet is the constant dyadic-stream carrier from the local carrier definition, then every requested precision window reads a located dyadic ball classified with the same degenerate dyadic endpoint under the displayed StreamNameUp, DyadicRatCoreUp, and CauchyModulusUp rows.

Local inputs:
- `papers/bedc/parts/concrete_instances/809_locatedcauchy_namecert_construction.tex`

Rationale:
The LocatedCauchyUp carrier is the finite packet L=(S,D,M,W,H,C,P,N), with schedule S, dyadic endpoint family D, Cauchy modulus M, located-ball witnesses W, transport H, and Cont readback routes C at papers/bedc/parts/concrete_instances/809_locatedcauchy_namecert_construction.tex:11-41. The definition says a constant dyadic stream inhabits the carrier by repeating one scheduled dyadic endpoint and using degenerate located balls at each requested window at lines 37-40, and the window-stability theorem only handles refined requested windows generally at lines 61-70. The NameCert theorem uses constant-stream habitation at lines 86-103 but does not isolate the per-window degenerate readback as a theorem. Focused rg for `locatedcauchy.*degenerate|locatedcauchy.*constant.*window|constant dyadic.*window` returned no LocatedCauchy theorem label; the only nonlocal hit was a LocatedReal proof sentence. This is a boundary exactness theorem about a concrete existing carrier, and the target file has 200 lines with 4 theorem-like blocks.

---
