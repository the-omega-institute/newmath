# rule110 — Master ROADMAP

**Project**: BEDC ground-up minimal-trust substrate on Rule 110 cellular automaton.
**Branch**: `rule110` (single trunk; M2 + M3 sub-branches archived in `history/`).
**Sibling to**: `lean4/BEDC/` (Lean 4 formalization), `papers/bedc/` (LaTeX manuscript).
**Hard constraint**: zero external dependencies, ANSI C99, Rule 110 + cyclic tag system as the only substrate primitives.

---

## 最终目标 (Final Goal — Level 6)

**BEDC as a bisubstrate-verified theory.** Every theorem in `lean4/BEDC/` has a verified ground-up counterpart on the rule110 substrate. The `rule110/` directory is a first-class peer to `lean4/BEDC/`; either substrate independently proves the same theorems. New BEDC content commits trigger both Lean check and rule110 manifest regeneration; both must agree before merge. This removes the asymmetric trust in any single proof system: BEDC is "true" iff *both* substrates (Lean CIC and Rule 110 cellular automaton) verify it.

This goal is open-ended. Levels below are the ascending path toward it.

---

## Current State (Level 0 plateau — Behavioral Scaffold Complete)

- 8,213 LOC ANSI C (`evaluator/` + `encoder/` + `tests/`)
- 44 `.ct` cyclic-tag manifests across 13 FKernel modules
- ~470 semantic test cases, `make test` exit 0
- 0 external dependencies (only `<stdio.h>` `<stdlib.h>` `<string.h>` `<stdint.h>` `<assert.h>`)
- Branch tree: `rule110` (trunk, this branch); legacy: `rule110-m2`, `rule110-m3` (both merged + archived in `history/`)

### What's encoded

| Layer | Component | Status |
|---|---|---|
| L1 | Rule 110 evaluator (`evaluator/rule110.c`, ~50 LOC) | ✓ |
| L2 | Cyclic tag evaluator (`evaluator/cyclic_tag.c`, ~80 LOC) | ✓ |
| L3 | GroundCompiler encoding (escape + decoder + 6 reject reasons) | ✓ |
| L4 | Mark theorem manifests (8 .ct, 4 `msame` lemmas) | ✓ vertical slice |
| L4 | BHist/hsame (66 cases + 5 bounded CT certs) | ✓ M3 Phase A+B |
| L4 | Ext relation (16 cases) | ✓ M3 Phase C |
| L4 | SigRel + sameSig (36 cases) | ✓ M3 Phase D |
| L4 | Cont, Bundle, Unary, Ask, ExternalBinary, Gap, Package, NameCert, Settled (9 modules, ~370 cases) | ✓ M3 extensions |
| L5 | Self-consistent test suite (decoder-based verification) | ✓ |
| L6 | Cook construction primitives (ether + 8 gliders + gun + leader/ossifier/data_block + cook_encode behavioral) | ✓ M2 |
| L6 | Phase-exact Cook universality (8 `.r110` manifests + round-trip ≡ CT) | ✗ Level 3 |

### What's deliberately deferred

- **Vacuous `*.algo.ct` productions** (most algo manifests): semantic verification is via decoder, not real CT recognition. Honest trade-off documented in module design docs.
- **B3 P_eq for BHist (bounded scope)**: 16-production marker certifier for 5 representative reflexive inputs only. Universal BHist equality recognizer deferred (per ROADMAP risk register).
- **Phase-exact Cook construction**: `cook_encode` ships best-effort behavioral; phase-exact transcription of Cook 2004 §5-6 is Level 3.
- **`.r110` manifest generation + round-trip**: depends on phase-exact Cook (Level 3).
- **Lean ↔ rule110 cross-check**: deliberate "self-consistent only" posture per spec §3.2; cross-check is Level 4.

---

## Level Ascent

### Level 1: Ship signal (1 day, ~5h)

Lock current state as a citable artifact.

- [x] L1.1: Honestly mark all `[!]` items in `history/ROADMAP-m2-cook-construction.md` and `history/ROADMAP-m3-fkernel-modules.md` (M2 C5+D3 = phase-exact deferred; M3 B3 already done).
- [x] L1.2: Update `rule110/README.md` to reflect both milestones merged.
- [x] L1.3: Write `rule110/STATUS.md` snapshot (LOC, manifest count, test case count, modules covered, deliberate gaps).
- [x] L1.4: Final `make clean && make && make test` confirm exit 0; record output to `STATUS.md`.
- [x] L1.5: Tag git release `rule110-v1.0-behavioral-scaffold` on origin.

### Level 2: Sharpen algo manifests (3-6 months, hard task)

Replace vacuous productions with real cyclic-tag programs.

Current state: each `*.algo.ct` (except `manifests/hist/hsame_refl.algo.ct` which is bounded P_eq) has `PRODUCTIONS 1` + a single zero-bit production, and the test driver verifies via decoder. This is honest "structure preserved" but not "CT actually computes the relation".

**Goal**: every `*.algo.ct` is a real CT program whose halt state encodes the relation outcome for *arbitrary* input (not just representative cases).

- [ ] L2.1: Universal BHist equality recognizer (M3 B3 unbounded continuation). Estimated alone: 1-2 months wall clock (CT program complexity).
- [!] L2.2: Universal Ext step recognizer. Bounded positional-certificate CTS covers the representative Ext fixtures, source depth `<= 3` / candidate result depth `<= 4` sweep, and malformed/trailing samples; the unbounded source-copy/result-tail compare machine is specified, but not implemented, in `docs/ext_algo_design.md`.
- [ ] L2.3: Universal SigRel + sameSig recognizers (ProbeBundle-parameterized; needs hash-like fingerprinting in CT productions).
- [!] L2.4: Universal Cont (append) recognizer. Bounded positional-certificate CTS covers the representative and depth `<= 2` Cont corpus; the unbounded queue-copy/compare machine is specified, but not implemented, in `docs/cont_algo_design.md`.
- [!] L2.5: Bundle length + membership recognizers: bounded positional-certificate CTS for the manifest fixtures; universal parsing and probe-name comparison remain open.
- [!] L2.6: Universal Unary classifier. `manifests/unary/unary_basic.algo.ct` contains an eight-production CT scan certificate; the binary CTS runner lacks a complete unbounded accept/reject convention for negative Unary inputs.
- [!] L2.7: Universal Ask fixture recognizer. Bounded positional-certificate CTS covers the representative Ask corpus and bounded parity fixture sweep; the full four-event lexer/parity decider is specified, but not implemented, in `docs/ask_algo_design.md`.
- [!] L2.8: Universal ExternalBinary recognizer. Bounded positional-certificate CTS covers the representative and depth `<= 2` ExternalBinary corpus; because ExternalBinary append is definitionally Cont append, the universal queue-copy/compare recognizer is the same deferred unbounded problem as L2.4.
- [!] L2.9: Universal Gap (InGapSig + CompGap) recognizer. Bounded positional-certificate CTS covers the representative Gap fixtures and depth `<= 2` InGapSig/CompGap sweep; the unbounded bundle-signature parser/compare machine is specified, but not implemented, in `docs/gap_algo_design.md`.
- [!] L2.10: Universal Package (psame + TokenPolicy) recognizer. Bounded positional-certificate CTS covers the representative Package fixtures and the generated depth `<= 2` token/psame/TokenPolicy/chain corpus; the universal recognizer is blocked on the unbounded `hsame` equality machine needed for `TokIntro := hsame`.
- [ ] L2.11: Universal NameCert (Carrier + Equiv + descent + composition + stability mode) recognizer.
- [ ] L2.12: Universal Settled (aggregator) recognizer.

**Risk register**: each item is comparable to "designing a string-rewriting decision procedure" — 1-4 weeks median per module, much more if novel encoding tricks needed. Some relations may be Π⁰₁-hard and not admit Σ⁰₁ CT recognition; in that case mark `[!]` with explicit "halts iff" reformulation.

### Level 3: Phase-exact Cook construction (4-8 weeks)

Make `cook_encode` produce correct Rule 110 initial patterns.

- [!] L3.1: Glider A phase word `A(f1_1)=111110` is emitted and verified as a period-3, displacement-2 Rule 110 orbit. B-H and full Cook Figure 4 multi-row masks remain blocked pending direct figure access or a trusted machine-readable phase catalog; see `docs/cook_glider_phases.md`.
- [ ] L3.2: Build collision lookup table by direct simulation (current `cook_collisions.c` simulator is heuristic; sharpen to track outgoing particle identities + velocities).
- [ ] L3.3: Implement productive leader/ossifier/data-block patterns (current best-effort scaffolds replaced with phase-exact transcriptions).
- [ ] L3.4: Cook encoder for arbitrary cyclic-tag programs: given (productions, tape), emit Rule 110 initial pattern whose evolution simulates the CT.
- [ ] L3.5: Generate `.r110` manifests for all 8 Mark + 36 BHist/Ext/Sig/Cont/Bundle/Unary/Ask/ExtBin/Gap/Package/NameCert/Settled `.ct` manifests (so 44 `.r110` total).
- [ ] L3.6: Round-trip verification: each manifest pair (`*.ct`, `*.r110`) — CT execution outcome on input X equals Rule 110 evolution outcome on encoded(X) decoded back.
- [ ] L3.7: Update `mr_run_r110_manifest` pipeline smoke test to cover all 44 .r110.

**Risk register** (from earlier research): no public ANSI C universal Cook construction exists; machine-110 (best public attempt) abandoned at 300 LOC. Realistic budget: 4-8 weeks, lower bound 25 days (replay Martínez fixed CTS), upper bound 60+ days (arbitrary CT generality). AI assistance is weak for this task class (low pattern density, off-by-one fatal).

### Level 4: Lean ↔ rule110 cross-check (2-4 weeks)

Close the trust loop: prove each rule110 manifest corresponds to a Lean theorem.

- [!] L4.1: Design correspondence schema.  POC implemented for `mark/msame_refl.enum.ct`; full family registry remains L4.3 scope.
  - [x] L4.1.a: Define the manifest parser contract: `PRODUCTIONS`, `ASSERTIONS`, case name, `input=...`, and family-specific key/value fields.
  - [!] L4.1.b: Define typed decoders from GroundCompiler events into `BMark`, `BHist`, `ProbeName := Nat`, `ProbeBundle Nat`, tags, booleans, packages, evidence, domains, and certificate fixture payloads.  `BMark` is implemented in the POC.
  - [!] L4.1.c: Register path-to-target specs for Mark, Hist, Ext, SigRel, SameSig, Cont, Bundle, Unary, Ask, ExternalBinary, Gap, Package, NameCert, and Settled.  Mark, Hist, and Ext are registered in the script-level closed-kernel slice.
  - [!] L4.1.d: Separate positive theorem-instance checks from negative complement checks such as `ext_holds=no`, `cont_holds=no`, malformed input, and trailing-input rejection.  Ext positive and negative assertions are separated in the script-level closed-kernel slice.
  - [ ] L4.1.e: Record the concrete setup instances needed by parameterized modules: parity `AskSetup`, `Pkg := BHist`, `TokIntro := hsame`, bounded-domain fixture, depth-equivalence NameCert fixture, and identity stable transformation.
- [!] L4.2: Build the Lean 4 executable.  `lean --run` script exists; Lake exe target is outside the script-only whitelist.
  - [x] L4.2.a: Create `lean4/scripts/rule110_cross_check.lean` as a read-only checker over existing manifests.
  - [x] L4.2.b: Reuse `BEDC.GroundCompiler.ChannelEncoding.DecEvent` for event decoding; do not fork the channel encoding.
  - [x] L4.2.c: Implement one closed-kernel slice first: `mark/msame_refl.enum.ct`, `hist/hsame_refl.enum.ct`, and `ext/ext_step.enum.ct`.
  - [x] L4.2.d: Add structured PASS/FAIL output with manifest path, case name, decoded values when available, and Lean target key.
  - [x] L4.2.e: Exit nonzero on parse, decode, type, fixture, target, or semantic failure.
- [ ] L4.3: Cross-check all manifest families.
  - [ ] L4.3.a: Cover all `.enum.ct` manifests as strict Level 4 targets.
  - [ ] L4.3.b: Report `.algo.ct` manifests as semantic-only until Level 2 supplies real recognizers, except bounded `hist/hsame_refl.algo.ct` which can be checked as a finite recognizer case set.
  - [ ] L4.3.c: Reuse lower-family checkers inside aggregate files where possible, especially `settled/settled_basic.enum.ct`.
  - [ ] L4.3.d: Ensure representative finite manifests are reported as ground instances of Lean universal theorems, not as exhaustive coverage claims for infinite types.
- [ ] L4.4: Add CI gate.
  - [ ] L4.4.a: Add Lake target `rule110-cross-check` that runs the Lean executable over the registered manifest list.
  - [ ] L4.4.b: CI acceptance requires `cd rule110 && make test` and `cd lean4 && lake build rule110-cross-check`.
  - [ ] L4.4.c: Gate failure messages distinguish C evaluator failure, Lean decode failure, Lean semantic mismatch, missing target registration, and fixture incompleteness.
  - [ ] L4.4.d: Track runtime budget for roughly `44 manifests × ~30 assertions`, with startup/import time expected to dominate.
- [ ] L4.5: Document trust-loop closure.
  - [ ] L4.5.a: Keep the design source at `rule110/docs/cross_check_design.md`.
  - [ ] L4.5.b: After the checker exists, write the operational trust-chain page `rule110/docs/cross_check.md` with exact commands and acceptance criteria.
  - [ ] L4.5.c: State remaining boundaries clearly: Level 4 checks Lean correspondence for manifest assertions; Level 2 handles real CT recognizers; Level 3 handles `.r110` round-trip.

**Outcome**: rule110 is no longer self-consistent-only; it is *Lean-verified*. The bisubstrate property starts taking shape.

### Level 5: Beyond FKernel (open-ended, scope expanding)

Encode BEDC content outside the finite-kernel proof boundary.

- [ ] L5.1: `Derived/TopologyUp` thin interface (BHist-based topology constructs).
- [ ] L5.2: `Derived/RealUp` (real numbers via BHist limit construction).
- [ ] L5.3: `Derived/CircleUp` (modular arithmetic + circle group).
- [ ] L5.4: `Derived/FoldUp` (foldable structures).
- [ ] L5.5: `BaseReflection` (CIC self-reflection within rule110 substrate — challenging since rule110 is sub-Turing-complete cellular automaton; may need bridge through cyclic-tag substrate first).
- [ ] L5.6: `MetaCIC` (mini-CIC self-host on BHist; this already exists in Lean — rule110 mirror).
- [ ] L5.7: `GroundCompiler` (the channel-encoding pipeline that rule110 itself uses; meta-circular).
- [ ] L5.8: `Capstones` (vision-level constructions — see `papers/bedc/parts/visions/`).

**Note**: Levels 5.5-5.8 are increasingly ambitious. L5.5 BaseReflection on rule110 may face fundamental obstructions (rule110 has no native dependent types; would need to encode `Type` hierarchy as bit patterns). Honest expectation: L5.5+ becomes a multi-year research program if pursued strictly.

### Level 6: Bisubstrate-verified BEDC (终极目标, ongoing forever)

The final goal. BEDC ships with two equal-trust substrates, both auto-verified on commit.

- [ ] L6.1: All BEDC theorems (Lean + rule110) cross-verified by CI on every PR.
- [ ] L6.2: New BEDC content can originate from either substrate; the other auto-derives.
- [ ] L6.3: `papers/bedc/` paper bibliography cites rule110 manifests with same authority as Lean theorems.
- [ ] L6.4: External reviewers can choose to verify in Lean OR in rule110 (or both); both paths sufficient for trust.
- [ ] L6.5: Cook construction so robust that any new cyclic-tag manifest is automatically generated as a Rule 110 `.r110` artifact, and the Rule 110 evolution is observable via `evaluator/rule110.c` (~50 LOC, audit ceiling).

**Outcome**: BEDC's trust foundation is "rule110 + Lean CIC + paper", not "Lean CIC + paper". The rule110 substrate becomes one of the most minimal-trust formalization substrates publicly verified at scale — significantly smaller element trust face than Lean kernel (`evaluator/rule110.c` ~50 LOC + a 14-byte ether pattern), while covering the same BEDC theorem corpus.

---

## Honest "Levels Bypass" Considerations

The level ascent is not strictly monotonic. Real progression should consider:

- **Level 2 + Level 4 in parallel**: cross-check (L4) can validate the *intent* of L2 sharpening as it lands. Don't wait for all 12 L2 sub-items.
- **Level 3 deprioritized?**: Cook phase-exact construction is hard and not strictly necessary for Level 4 cross-check (cross-check operates on `.ct` manifests, not `.r110`). If resources tight, do L2 + L4 first, leave L3 as a "minimum-trust polish" later.
- **Level 5 selective**: not all `Derived/` modules need rule110 encoding for the final goal — only the ones used in the paper proof chain. Profile paper dependencies first, encode selectively.

---

## What `make test` should verify at each level

| Level | `make test` invariant |
|---|---|
| 0 (now) | All `.ct` manifests + decoder-based verification + Cook primitives behavioral test |
| 1 | Same as 0; tag committed; nothing changes |
| 2 | All `*.algo.ct` invoke real CT recognizer; arbitrary input (not just representative cases) classifies correctly |
| 3 | All 44 `.r110` manifests round-trip with their `.ct` siblings; Cook universality demonstrated |
| 4 | Lean ↔ rule110 correspondence checker passes for all manifests |
| 5 | Cross-check covers Derived/RealUp etc. (expanding scope) |
| 6 | CI gate: any commit changing `lean4/BEDC/` OR `rule110/manifests/` must verify in both substrates |

---

## Acceptance Criteria for "Ship Level N"

At each level, declare ship-ready iff:

1. All `[ ]` items in that level marked `[x]` or `[!]` (with documented blocker).
2. `make test` exit 0 with full test suite green.
3. Spec `docs/superpowers/specs/2026-05-12-rule110-init-design.md` §11 acceptance criteria still met (sibling experiment posture, no touching of `lean4/` or `papers/bedc/`).
4. `STATUS.md` updated with new LOC, manifest count, test case count.
5. Git tag `rule110-vN-<descriptor>` on origin.

---

## History (archived)

Active references (read these first):
- `rule110/docs/` — 14 per-module design docs + cook_construction.md (canonical current design)
- `rule110/README.md` — top-level reproducibility + trust chain summary

Historical audit trail (kept for provenance, not for active lookup):
- `history/ROADMAP-m2-cook-construction.md` — M2 milestone roadmap (Cook construction, 60% done as behavioral scaffold).
- `history/ROADMAP-m3-fkernel-modules.md` — M3 milestone roadmap (13 FKernel modules, 79% done).
- `history/NOTES-m2-cook-observations.md` — M2 worker observations (per-glider best-effort rationale, collision sim outputs).
- `history/NOTES-m3-fkernel-observations.md` — M3 worker observations (per-Lean-file LOC + theorem counts, per-module encoding choice timestamps).
- Original vertical slice spec + plan: `docs/superpowers/specs/2026-05-12-rule110-init-design.md`, `docs/superpowers/plans/2026-05-12-rule110-init.md`.

---

## /loop instructions (for autonomous progression)

When a tick fires, find the lowest-numbered Level still containing `- [ ]` items. Execute one of them via codex CLI worker dispatch on `/tmp/wt-<level>-<task>/` worktree. Each task is bounded ~1 day; harder tasks (L2.* relation recognizers, L3.* Cook phases) may take longer — split via mid-task ROADMAP refinement.

Before dispatching: read this file fresh (Levels evolve as understanding deepens). Don't blindly execute stale tasks.
