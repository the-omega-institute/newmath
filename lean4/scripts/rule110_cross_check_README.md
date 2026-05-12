# Rule110 Lean cross-check POC

This script is a Lean-side manifest cross-check for the rule110 manifest
corpus.  Its supported strict target is
`rule110/manifests/mark/msame_refl.enum.ct`.

Run from the repository root:

```bash
cd lean4
lake build BEDC.GroundCompiler.ChannelEncoding
lake env lean --run scripts/rule110_cross_check.lean ../rule110/manifests/mark/msame_refl.enum.ct
```

Expected output:

```text
PASS msame_refl b0_b0 (b0,b0) -> BEDC.FKernel.Mark.msame_refl
PASS msame_refl b1_b1 (b1,b1) -> BEDC.FKernel.Mark.msame_refl
```

The checker parses `PRODUCTIONS` and `ASSERTIONS`, extracts each `input=`
bit string, decodes two events with
`BEDC.GroundCompiler.ChannelEncoding.DecEvent`, converts both payloads to
`BMark`, and checks the decoded pair as a ground instance of
`BEDC.FKernel.Mark.msame_refl`.

The project lakefile exposes only the `BEDC` library target, so this script is
run with `lean --run` rather than `lake exe rule110_cross_check`.  A Lake
executable target belongs with the Level 4 CI gate.
