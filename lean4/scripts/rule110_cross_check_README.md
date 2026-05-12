# Rule110 Lean cross-check

Run from the repository root:

```bash
cd lean4
lake build BEDC.GroundCompiler.ChannelEncoding
lake env lean --run scripts/rule110_cross_check.lean \
  ../rule110/manifests/mark/msame_refl.enum.ct \
  ../rule110/manifests/hist/hsame_refl.enum.ct \
  ../rule110/manifests/ext/ext_step.enum.ct
```

Supported strict targets:

- `rule110/manifests/mark/msame_refl.enum.ct`
  targets `BEDC.FKernel.Mark.msame_refl`.
- `rule110/manifests/hist/hsame_refl.enum.ct`
  targets `BEDC.FKernel.Hist.hsame_refl`.
- `rule110/manifests/ext/ext_step.enum.ct`
  targets the constructor family
  `BEDC.FKernel.Ext.Ext.e0/BEDC.FKernel.Ext.Ext.e1`.

The checker parses `PRODUCTIONS` and `ASSERTIONS`, extracts each `input=`
bit string, and decodes events with
`BEDC.GroundCompiler.ChannelEncoding.DecEvent`.

The `mark` family decodes two one-symbol events as `(BMark, BMark)` and checks
the decoded pair as a ground instance of `msame_refl`.

The `hist` family decodes two events as `(BHist, BHist)`.  Each event payload is
read as a constructor spine: empty payload is `BHist.Empty`, `b0 :: rest` is
`BHist.e0`, and `b1 :: rest` is `BHist.e1`.  The decoded pair is checked as a
ground instance of `hsame_refl`.

The `ext` family decodes three events as `(source : BHist, mark : BMark,
result : BHist)`.  Positive assertions instantiate `Ext.e0` or `Ext.e1`.
Negative assertions prove the complement for the decoded triple by checking
that `result` is not the constructor layer selected by `mark` over `source`.
The manifest name `ext_step.enum.ct` therefore maps to the constructor family
rather than to a separately named theorem.

Each `PASS` line includes the manifest path, family, case name, decoded values,
assertion polarity when relevant, and Lean target key.

The project lakefile exposes only the `BEDC` library target, so this script is
run with `lean --run` rather than `lake exe rule110_cross_check`.  A Lake
executable target belongs with the Level 4 CI gate.
