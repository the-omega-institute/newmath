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

## Layer 6 (out of scope)

Cook construction encoder. See spec §12.M2 (4+ week project) for milestone-2 plan.
