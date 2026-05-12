# rule110-m2 ROADMAP — Cook construction encoder

**Branch**: `rule110-m2` (base: `rule110` vertical slice)
**Milestone**: M2 per `docs/superpowers/specs/2026-05-12-rule110-init-design.md` §12
**Goal**: Implement Matthew Cook 2004 cyclic-tag-system → Rule-110 universal encoder in ANSI C, generate `.r110` substrate manifests for the 8 existing Mark theorems, verify behavioral round-trip.
**Estimated wall clock**: 25 days (research evaluation, see spec §3.3); upper bound 60 days.

## /loop instructions (for each tick)

1. Read this file. Find first `- [ ]` task.
2. Execute it: design + write code (inline or via codex worker dispatch on `/tmp/wt-m2-task-N`) + verify (build + test) + commit on `rule110-m2` branch.
3. Change `- [ ]` → `- [x]` for that task; commit the check-off.
4. If task blocked after 2 attempts: change `- [ ]` → `- [!]`, add brief reason to `rule110/NOTES-m2.md`, skip to next task.
5. Halt. Next /loop tick fires automatically.

Each task is bounded to ~1 wall-clock day. Codex worker preferred for code-heavy tasks; orchestrator inline for design / merge / verify steps.

## Reference

Primary source: Matthew Cook (2004) "Universality in Elementary Cellular Automata", *Complex Systems* 15(1):1-40 ([PDF](http://wpmedia.wolfram.com/sites/13/2018/02/15-1-1.pdf)).
Secondary: Genaro Martínez et al., [arXiv:1307.7951](https://arxiv.org/abs/1307.7951); Wolfram NKS §11.8 + p.1116.

## Phase A: Background pattern + glider catalog (10-15 days)

- [x] A1: Document Cook 2004 ether pattern (width 14, period 7, pattern `00010011011111`) in `encoder/cook_construction.h` as constants. Create `encoder/cook_construction.c` skeleton with `cook_ether_emit(uint8_t *out, size_t period_count)` function. Test in new `tests/test_cook_ether.c` that emitted pattern is stable under Rule 110 evolution for 100 timesteps.

- [x] A2: Implement glider A (simplest left-moving glider). Document its bit pattern + phase. Add `cook_glider_A_emit(uint8_t *out, size_t pos, size_t ether_width)` injecting glider into ether background. Test: 100-step evolution shows glider moves left at expected speed without breaking ether.

- [x] A3: Implement gliders B, C, D (additional simple gliders). Each gets emit function + emergence test under Rule 110 evolution.

- [x] A4: Implement gliders E, F (complex gliders).

- [x] A5: Implement gliders G, H (rare). Test catalog completeness — 8 named glider families per Cook paper §3.

- [x] A6: Implement glider gun (periodic source). Test under Rule 110 evolution for 1000+ timesteps.

## Phase B: Collision table + leader/ossifier (5-10 days)

- [x] B1: Document collision pairs (A+A, A+B, etc.) from Cook §4. Create lookup table `cook_collision_outcome(GliderId, GliderId)` returning either a new GliderId list or "annihilation".

- [x] B2: Verify collision outcomes by direct Rule 110 simulation: inject two gliders, evolve, observe outcome, compare against lookup. Add `tests/test_cook_collisions.c` covering all listed collision pairs.

- [x] B3: Implement leader structure (encodes "start of data block" in Cook §5). Test emission + stability.

- [x] B4: Implement ossifier structure (encodes "current production index" in Cook §5). Test emission + stability.

- [x] B5: Implement data block encoding (sequence of bits as glider sequence per Cook §6).

## Phase C: Translator (5-10 days)

- [x] C1: Design `cook_encode(const CyclicTag *ct, uint8_t *out, size_t *out_len)` function signature. Document the encoding strategy: ether background + leader + ossifiers for each production + data block for initial tape.

- [x] C2: Implement encoder for empty CT (just ether + leader, no productions). Verify Rule 110 evolution preserves shape indefinitely.

- [x] C3: Implement encoder for CT with 1 production. Verify by running Cook's example or constructing a minimal example.

- [ ] C4: Implement encoder for arbitrary CT. Test on the 8 Mark manifests' productions.

- [ ] C5: Generate `.r110` versions of all 8 Mark manifests: `manifests/mark/msame_*.{enum,algo}.r110`. These are large bit patterns (potentially MB-scale). Document expected sizes in headers.

## Phase D: Round-trip verification (3-5 days)

- [x] D1: Add `mr_run_r110_manifest(const char *path, ...)` to `tests/manifest_runner.c`. Loads `.r110` file, evolves Rule 110 for the documented step count, compares result to expected pattern.

- [x] D2: Add round-trip test: for each Mark manifest, run cyclic_tag evaluator → record observable tape behavior → run Rule 110 evaluator on `.r110` → extract observable tape behavior via Cook decoder → assert match.

- [ ] D3: Update `tests/test_mark.c` `pipeline_smoke_test_all_manifests` to also exercise `.r110` versions via `mr_run_r110_manifest`. All 16 manifests (8 .ct + 8 .r110) should pass.

## Phase E: Documentation + ship (1-2 days)

- [x] E1: Update `rule110/docs/trust_chain.md` to reflect Layer 6 (Cook encoder) now shipped.

- [x] E2: Update `rule110/docs/manifest_format.md` with `.r110` manifest format spec.

- [x] E3: Add `rule110/docs/cook_construction.md` describing the encoder's design, ether/glider catalog, and trust posture.

- [ ] E4: Update `rule110/README.md` to remove Layer 6 "(out of scope)" caveat.

- [ ] E5: Final `make clean && make && make test`; ensure all 16 manifest pipelines plus all unit tests pass with no warnings.

- [ ] E6: Commit + push `rule110-m2` to origin. Update top of this ROADMAP.md to mark milestone complete + suggest next milestone (M3 if not yet started, or M4).

## Acceptance criteria

- [ ] All Phase A tasks `- [x]` or `- [!]` with documented blocker
- [ ] All Phase B-E tasks `- [x]` or `- [!]` with documented blocker
- [ ] 8 `.r110` manifests in `rule110/manifests/mark/`
- [ ] Round-trip behavior verified for all 8 manifests
- [ ] `make test` exit 0 with all 16 manifests passing
- [ ] `cook_construction.c` ≤ 1500 LOC (Cook construction itself; if exceeds, descope encoder generality and note in NOTES-m2.md)
- [ ] No regression in existing rule110 vertical slice tests (32 manifest assertions + 11 unit tests still pass)
- [ ] `rule110-m2` branch pushed to origin

## Risk register

- **Glider phase alignment** (Phase A2-A6): one-cell offsets break universality. Spend extra debug time, use direct Rule 110 simulation as oracle.
- **Encoder generality** (Phase C4): writing a translator for *arbitrary* CT is the hardest part of Cook construction. Fallback: descope to "translator works for the 8 specific Mark CT manifests" and note as known limitation.
- **Manifest size** (Phase C5): `.r110` files may be MB-scale. If exceeds 10MB per manifest, consider compressed format (RLE).
- **Wall clock blowout**: 25-day median estimate has 60-day upper bound. Re-evaluate after Phase B; if Phase A took ≥ 20 days, replan.
