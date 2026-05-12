# rule110-m3 ROADMAP — BHist / Ext / SigRel ground-up encoding

**Branch**: `rule110-m3` (base: `rule110` vertical slice)
**Milestone**: M3 per `docs/superpowers/specs/2026-05-12-rule110-init-design.md` §12 (BHist 移植)
**Goal**: Extend the cyclic-tag substrate from BMark (finite 2-element) to BHist (countably infinite inductive), then layer Ext and SigRel relations on top. This is the first encoding where the `algo` form genuinely matters — vacuous productions are insufficient since BHist cases cannot be enumerated.
**Estimated wall clock**: 14-21 days; upper bound 30 days if `P_eq`-on-BHist proves harder than estimated.
**Parallel sibling**: `rule110-m2` (Cook construction) runs concurrently. Both branch off `rule110`; eventually both merge back. Independent file scopes (M2: `encoder/cook_*`, `manifests/mark/*.r110`; M3: `manifests/hist/`, `tests/test_hist.c`, `encoder/groundcompiler_encoding.c` BHist extensions, `tests/manifest_runner.c` if needed). Shared `Makefile` — additive changes only, merge by union.

## /loop instructions (for each tick)

1. Read this file. Find first `- [ ]` task.
2. Execute it: design + write code (inline or via codex worker dispatch on `/tmp/wt-m3-task-N`) + verify (build + test) + commit on `rule110-m3` branch.
3. Change `- [ ]` → `- [x]` for that task; commit the check-off.
4. If task blocked after 2 attempts: change `- [ ]` → `- [!]`, add brief reason to `rule110/NOTES-m3.md`, skip to next task.
5. Halt. Next /loop tick fires automatically.

Each task is bounded to ~1 wall-clock day. Codex worker preferred for code-heavy tasks; orchestrator inline for design / merge / verify steps.

## Reference

Primary source: `lean4/BEDC/FKernel/Hist.lean` (BHist + hsame), `lean4/BEDC/FKernel/Ext.lean` (Ext relation), `lean4/BEDC/FKernel/Sig.lean` (SigRel). Plus `lean4/BEDC/GroundCompiler/ChannelEncoding.lean` for the encoding convention to extend.

## Phase A: BHist data type encoding (3-5 days)

- [ ] A1: Read `lean4/BEDC/FKernel/Hist.lean` (~100 LOC). Document the 3-constructor structure (`Empty | e0 BHist | e1 BHist`) and how it differs from BMark (finite 2-element vs countable inductive). Draft BHist encoding strategy in new `rule110/docs/bhist_encoding.md`: every BHist value is a finite sequence of bits, naturally fitting the `EventEncoding` convention extended to *one event encodes one BHist*. Empty → `[]`; e0 h → `[b0, ...encoding(h)]` (or some canonical wrapper); e1 h → `[b1, ...]`. Commit `docs/bhist_encoding.md`.

- [ ] A2: Extend `encoder/groundcompiler_encoding.c` with `bhist_encode(BHistNode *root, uint8_t *out, size_t out_cap)` and `bhist_decode(uint8_t *in, size_t in_len, ...)`. Add `BHistNode` struct (or equivalent representation) in `encoder/groundcompiler_encoding.h`. Round-trip test in `tests/test_encoder.c` (extend, not replace existing tests): encode Empty / e0(Empty) / e1(e0(Empty)) etc., verify decode reproduces.

- [ ] A3: Document edge cases in `docs/bhist_encoding.md`: deep nesting (e.g., 100-level e0 chain), max depth handling, decoder fuel parameter.

## Phase B: hsame relation (5-7 days)

- [ ] B1: Read `lean4/BEDC/FKernel/Hist.lean` for `hsame` definition + theorems (refl, symm, trans, empty inversion, constructor distinctness). List target theorems to encode.

- [ ] B2: Design CT manifest format for BHist pairs (analogous to BMark pairs in vertical slice). New directory `rule110/manifests/hist/`. Create `hsame_refl.enum.ct` with representative cases (Empty/Empty, e0(Empty)/e0(Empty), e1(Empty)/e1(Empty), and a deep case like e0(e1(e0(Empty)))/itself). Enum is documentary only — runtime check via decoder.

- [ ] B3: **Real algorithm-form P_eq for BHist** (the honest task that BMark vertical slice deferred). Design a cyclic-tag program that recognizes "two BHist payloads are bit-by-bit equal". This may require 10-30 productions and careful tape engineering. Document the design in `docs/bhist_algo_design.md` before implementing. Write the productions into `hsame_refl.algo.ct`.

- [ ] B4: Add `test_hsame_refl_*` functions to a new `tests/test_hist.c` (mirror of `tests/test_mark.c` for BHist). Add `enum_assert_reflexive_hist` and `decode_two_bhist_equal` helpers leveraging the BHist decoder from Phase A. Make sure `make tests/test_hist && ./tests/test_hist` passes.

- [ ] B5: hsame_symm: 4+ cases (reflexive + vacuous mismatches). Both `.enum.ct` and `.algo.ct`.

- [ ] B6: hsame_trans: 8+ cases. Algo manifest reuses P_eq from B3.

- [ ] B7: hsame Empty inversion: Empty matches Empty only — manifest + test.

- [ ] B8: hsame constructor distinctness: e0(h) ≠ e1(h'), e0(h) ≠ Empty, e1(h) ≠ Empty for arbitrary h, h'. Manifest + test (use representative deep cases).

## Phase C: Ext relation (3-5 days)

- [ ] C1: Read `lean4/BEDC/FKernel/Ext.lean`. Document the inductive structure of `Ext : BHist → BMark → BHist → Prop` and its 3 constructors.

- [ ] C2: Design `Ext` encoding strategy: a CT manifest with input = encoded triple (BHist, BMark, BHist) and accept = whether Ext holds. The algorithm reuses BHist decoder + checks the inductive condition.

- [ ] C3: Encode the Ext constructor cases as manifests in `rule110/manifests/ext/`. Each major Ext theorem from Ext.lean gets a manifest pair.

- [ ] C4: Test functions in `tests/test_ext.c`. Verify against `Ext.lean` examples.

## Phase D: SigRel + sameSig (3-5 days)

- [ ] D1: Read `lean4/BEDC/FKernel/Sig.lean` and `lean4/BEDC/FKernel/Sig/SameSig.lean`. SigRel involves ProbeBundle parameterization — design how to encode an abstract ProbeBundle in CT manifests.

- [ ] D2: Implement ProbeBundle encoding (list of probe names, each name itself bit-encoded).

- [ ] D3: Encode SigRel manifests for the canonical examples in Sig.lean.

- [ ] D4: sameSig equivalence theorems → manifests + tests.

## Phase E: Documentation + ship (1-2 days)

- [ ] E1: Update `rule110/docs/trust_chain.md` to mention BHist + Ext + SigRel encoding (Layer 4 extended).

- [ ] E2: Add `rule110/docs/bhist_encoding.md`, `rule110/docs/bhist_algo_design.md`, and (if non-trivial) `rule110/docs/ext_sigrel_design.md`.

- [ ] E3: Update `rule110/README.md` to list new manifest directories (`manifests/hist/`, `manifests/ext/`, `manifests/sig/`).

- [ ] E4: Final `make clean && make && make test`. All existing tests still pass + new test_hist / test_ext (and possibly test_sig) pass.

- [ ] E5: Commit + push `rule110-m3` to origin. Update top of this ROADMAP.md to mark milestone complete + suggest next milestone.

## Acceptance criteria

- [ ] All Phase A tasks `- [x]` or `- [!]` with documented blocker
- [ ] All Phase B-E tasks `- [x]` or `- [!]` with documented blocker
- [ ] BHist encoder/decoder round-trip verified for representative cases (Empty, e0(Empty), e1(Empty), deep nestings to depth 10+)
- [ ] Real algorithm-form `P_eq` for BHist payloads working (no vacuous-production fallback)
- [ ] `hsame_*` theorems encoded as manifest pairs (enum + algo); all assertions pass
- [ ] `Ext` theorems encoded; assertions pass
- [ ] `SigRel` + `sameSig` theorems encoded; assertions pass
- [ ] `make test` exit 0, all manifest assertions + unit tests pass
- [ ] No regression in existing rule110 vertical slice tests (32 manifest assertions + 11 unit tests still pass)
- [ ] `rule110-m3` branch pushed to origin

## Risk register

- **Real P_eq design** (Phase B3): the honest hard task. Designing a cyclic-tag program for "two payloads bit-by-bit equal" is the first non-trivial CT programming exercise. May take 3-5 days alone. If stuck, document partial progress + fallback to enum-only encoding for hsame (note as limitation).
- **Encoding ambiguity** (Phase A1): naive `e0 → b0, e1 → b1` collides with the BMark escape convention. Need careful wrapper bits (e.g., `e0 → "00", e1 → "01"` or some scheme). Settle this in A1 design doc *before* implementing.
- **ProbeBundle abstraction** (Phase D1-D2): the Lean version uses `Type` parameter for ProbeName, which has no ground-up analog. Choose a concrete representation (e.g., natural numbers in unary, encoded as bit strings) and document the choice.
- **Wall clock blowout**: 14-21-day estimate; if Phase B exceeds 10 days, replan Phase C+D scope.
