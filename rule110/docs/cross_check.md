# rule110 <-> Lean cross-check operational guide

This page is the operational guide for the rule110 <-> Lean cross-check trust loop.  It tells an external reviewer how to run the Lean-side checker over the supported rule110 cyclic-tag manifests, how to read the output, and what trust boundary the result closes.  The design source for the correspondence schema is `rule110/docs/cross_check_design.md`.

## Trust-chain closure

The checker reads assertion tables from registered rule110 manifests, decodes each `input=` bit string with the Lean GroundCompiler channel decoder, converts the decoded payloads into typed BEDC finite-kernel values, and checks that each assertion is a ground instance or complement case for the named Lean surface.  The covered surface is the closed-kernel slice:

- `rule110/manifests/mark/msame_refl.enum.ct` checks `BEDC.FKernel.Mark.msame_refl`.
- `rule110/manifests/hist/hsame_refl.enum.ct` checks `BEDC.FKernel.Hist.hsame_refl`.
- `rule110/manifests/ext/ext_step.enum.ct` checks positive and negative Ext step assertions against `BEDC.FKernel.Ext.Ext.e0` / `BEDC.FKernel.Ext.Ext.e1`.

## How to verify locally

Run from the repository root.  On a clean worktree, compile the Lean library once before running the script:

```bash
cd lean4
lake build
lake env lean --run scripts/rule110_cross_check.lean \
  ../rule110/manifests/mark/msame_refl.enum.ct \
  ../rule110/manifests/hist/hsame_refl.enum.ct \
  ../rule110/manifests/ext/ext_step.enum.ct
```

Expected output:

```text
PASS path=../rule110/manifests/mark/msame_refl.enum.ct family=mark case=b0_b0 decoded=(b0,b0) target=BEDC.FKernel.Mark.msame_refl
PASS path=../rule110/manifests/mark/msame_refl.enum.ct family=mark case=b1_b1 decoded=(b1,b1) target=BEDC.FKernel.Mark.msame_refl
PASS path=../rule110/manifests/hist/hsame_refl.enum.ct family=hist case=empty decoded=(Empty,Empty) target=BEDC.FKernel.Hist.hsame_refl
PASS path=../rule110/manifests/hist/hsame_refl.enum.ct family=hist case=e0_empty decoded=(e0(Empty),e0(Empty)) target=BEDC.FKernel.Hist.hsame_refl
PASS path=../rule110/manifests/hist/hsame_refl.enum.ct family=hist case=e1_empty decoded=(e1(Empty),e1(Empty)) target=BEDC.FKernel.Hist.hsame_refl
PASS path=../rule110/manifests/hist/hsame_refl.enum.ct family=hist case=e0_e1_empty decoded=(e0(e1(Empty)),e0(e1(Empty))) target=BEDC.FKernel.Hist.hsame_refl
PASS path=../rule110/manifests/hist/hsame_refl.enum.ct family=hist case=e1_e0_e1 decoded=(e1(e0(e1(Empty))),e1(e0(e1(Empty)))) target=BEDC.FKernel.Hist.hsame_refl
PASS path=../rule110/manifests/ext/ext_step.enum.ct family=ext case=empty_b0_e0_empty decoded=(Empty,b0,e0(Empty)) ext_holds=yes target=BEDC.FKernel.Ext.Ext.e0/BEDC.FKernel.Ext.Ext.e1
PASS path=../rule110/manifests/ext/ext_step.enum.ct family=ext case=empty_b1_e1_empty decoded=(Empty,b1,e1(Empty)) ext_holds=yes target=BEDC.FKernel.Ext.Ext.e0/BEDC.FKernel.Ext.Ext.e1
PASS path=../rule110/manifests/ext/ext_step.enum.ct family=ext case=e0_empty_b0_e0_e0_empty decoded=(e0(Empty),b0,e0(e0(Empty))) ext_holds=yes target=BEDC.FKernel.Ext.Ext.e0/BEDC.FKernel.Ext.Ext.e1
PASS path=../rule110/manifests/ext/ext_step.enum.ct family=ext case=e1_empty_b1_e1_e1_empty decoded=(e1(Empty),b1,e1(e1(Empty))) ext_holds=yes target=BEDC.FKernel.Ext.Ext.e0/BEDC.FKernel.Ext.Ext.e1
PASS path=../rule110/manifests/ext/ext_step.enum.ct family=ext case=e0_e1_b0_e0_e0_e1 decoded=(e0(e1(Empty)),b0,e0(e0(e1(Empty)))) ext_holds=yes target=BEDC.FKernel.Ext.Ext.e0/BEDC.FKernel.Ext.Ext.e1
PASS path=../rule110/manifests/ext/ext_step.enum.ct family=ext case=empty_b0_empty decoded=(Empty,b0,Empty) ext_holds=no target=BEDC.FKernel.Ext.Ext.e0/BEDC.FKernel.Ext.Ext.e1
PASS path=../rule110/manifests/ext/ext_step.enum.ct family=ext case=e0_empty_b0_e1_e0_empty decoded=(e0(Empty),b0,e1(e0(Empty))) ext_holds=no target=BEDC.FKernel.Ext.Ext.e0/BEDC.FKernel.Ext.Ext.e1
PASS path=../rule110/manifests/ext/ext_step.enum.ct family=ext case=e1_empty_b1_e0_e1_empty decoded=(e1(Empty),b1,e0(e1(Empty))) ext_holds=no target=BEDC.FKernel.Ext.Ext.e0/BEDC.FKernel.Ext.Ext.e1
```

The script exits `0` only when every registered manifest parses, every assertion count matches, every input decodes, every typed payload check succeeds, and every semantic assertion matches the Lean target key.  Any parse, decode, target, fixture, or semantic mismatch prints `FAIL path=...` on stderr and exits nonzero.

## Acceptance criteria

- `cd lean4 && lake env lean --run scripts/rule110_cross_check.lean ...` exits `0` for the three registered manifests above.
- Every emitted assertion line begins with `PASS`.
- The axiom audit passes from the repository root with `python3 tools/check-axioms.py`.
- The axiom audit reports `Axiom audit: 0 axioms in lean4/BEDC/.`.

## Remaining boundaries

- L4.3.a-d: all remaining `.enum.ct` families still need registered parsers, fixture instances, and semantic routing.
- L4.4 CI gate: the cross-check is still a direct `lean --run` operation, not a CI-gated Lake target.
- L2.* universal recognizers: most `*.algo.ct` files are not accepted here as universal cyclic-tag decision procedures.
- L3.* `.r110` round-trip: Rule 110 phase-exact Cook manifests and CT-to-Rule-110 round-trip checks remain outside this page.

## What it does not prove

This check only establishes that the listed manifest assertions correspond to instances or complement cases of the named Lean targets for the decoded closed-kernel inputs.  It is not a substitute for L2 universal cyclic-tag recognizers, which prove relations for arbitrary input, and it is not a substitute for the L3 phase-exact Cook construction, which proves that Rule 110 itself executes the cyclic-tag computation.
