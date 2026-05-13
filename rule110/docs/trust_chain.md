# Trust chain audit guide

Each layer of `rule110/` can be independently audited. This document explains
what to check at each layer.

## Layer 0: ANSI C compiler

Trust: industry-standard. Not audited.

## Layer 1: Rule 110 evaluator (`evaluator/rule110.c`, ~50 LOC)

Audit checklist:
- Truth table `{0,1,1,1,0,1,1,0}` matches Wolfram NKS Rule 110.
- Boundary handling: cells off-grid are 0 (verified in `tests/test_rule110.c::test_boundary_fixed_at_zero`).
- No memory leaks: `r110_step` mallocs+frees a temporary buffer each call.
- Deterministic: no calls to time/rand.
- Standalone main only enabled by `-DRULE110_STANDALONE_MAIN`; library use does not include `main()`.

## Layer 2: Cyclic tag evaluator (`evaluator/cyclic_tag.c`, ~80 LOC)

Audit checklist:
- Step semantics: head=1 → append productions[pc] then drop head; head=0 → drop head only.
- pc increments unconditionally modulo num_productions.
- Halt conditions: tape_len==0 (HALT_EMPTY) or step count exceeded (HALT_STEPLIMIT).
- Tape capacity grows dynamically; OOM returns HALT_OOM (not silent corruption).
- Verified in `tests/test_cyclic_tag.c` with identity, simple growth, and step-limit CTs.

## Layer 3: GroundCompiler encoder (`encoder/groundcompiler_encoding.c`, ~120 LOC)

Audit checklist:
- Body encoding: b0 → "0" (1 bit); b1 → "10" (2 bits). Match `lean4/BEDC/GroundCompiler/ChannelEncoding.lean::BodyEncoding`.
- Event terminator: "11". Match `EventTerminator` constant in same Lean file.
- Decoder DecodeFuel mirror: `gc_dec_event(..., fuel)` returns RESOURCE_BOUND_EXCESS if fuel exhausted.
- All 6 reject reasons match `lean4/BEDC/GroundCompiler/MinimalPrototype.lean::RejectReason` enum exactly.

## Layer 4: Mark manifests (8 `.ct` files in `manifests/mark/`)

Audit checklist:
- Each manifest header documents the theorem statement and the BMark encoding of inputs.
- All input bit strings decode (via Layer 3) to exactly the documented BMark pair/triple.
- ASSERTIONS lines match `tests/test_mark.c` assertion calls 1:1.

## Layer 5: Self-consistent tests (`tests/test_mark.c`)

Audit checklist:
- 32 assertions total (2+2+4+4+8+8+2+2).
- Every assertion uses Layer 3 (decoder) as primary verification mechanism.
- Pipeline smoke test additionally exercises Layer 2 (CT evaluator) end-to-end on all 8 manifests, verifying the manifest_runner pipeline works (separate from semantic assertions).
- No external oracle (no cross-check against Lean) — this is the deliberate ground-up posture documented in spec §3.2.

## Layer 6: Cook construction scaffold (`encoder/cook_*.c`)

Trust: experimental. This layer is present as a behavioral Rule 110 encoder
scaffold, not as a phase-exact transcription of Cook 2004.

Audit checklist:
- Ether: `cook_ether_emit` emits the working width-14 ether word
  `00010011011111`; tests compare evolved ether against the local Rule 110
  evaluator.
- Glider catalog: `A` through `H` plus the glider gun have best-effort emitters.
  The tests check localized motion, persistent disturbance, and far-field ether
  preservation. They do not certify Cook-catalog phase identity.
- Leader, ossifier, and data block: the emitted structures are behavioral
  encodings over ether. They provide deterministic substrate regions for the
  encoder pipeline, but they are not certified as Cook section 5-6 packages.
- Collisions: the current simulator covers 16 ordered pairs from `A` through
  `D` under one chosen spacing. All currently observed outcomes classify as
  `passthrough` or `annihilation`; no productive collision construction is
  certified.
- `cook_encode`: empty cyclic tag inputs emit ether plus the current leader.
  Non-empty inputs remain limited; the one-production case is the next active
  construction boundary.
- Manifests: `.r110` is a documented substrate format for Rule 110 rows and
  expected final rows. It is suitable for behavioral manifest-runner checks
  once the runner and generated rows are present.

Caveat: Layer 6 is suitable for demonstrating the shape of the encoder
pipeline and for testing local Rule 110 substrate behavior. It is not a
production universality claim and must not be cited as a completed
phase-exact Cook 2004 construction.
