# Rule110 Lean cross-check

Run from the repository root:

```bash
cd lean4
lake build rule110-cross-check
lake exe rule110-cross-check
```

With no arguments, `lake exe rule110-cross-check` checks the registered
closed-kernel slice:

- `../rule110/manifests/mark/msame_refl.enum.ct`
- `../rule110/manifests/hist/hsame_refl.enum.ct`
- `../rule110/manifests/ext/ext_step.enum.ct`

To run a selected manifest manually:

```bash
cd lean4
lake env lean --run scripts/rule110_cross_check.lean \
  ../rule110/manifests/mark/msame_refl.enum.ct
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

## CI gate

The PR gate runs the rule110 cross-check job when a PR changes `rule110/`,
`lean4/scripts/rule110_cross_check.lean`,
`lean4/scripts/rule110_cross_check_README.md`, or `lean4/lakefile.lean`.

The job requires both substrate and Lean correspondence commands to pass:

```bash
cd rule110 && make test
cd lean4 && lake build rule110-cross-check
cd lean4 && lake exe rule110-cross-check
```

## Failure kinds

Every gate failure path prints a structured line beginning with `FAIL kind=`.
The current kinds are:

- `C-decode`: emitted by the CI wrapper when `cd rule110 && make test` fails.
- `Lean-decode`: emitted by the Lean checker when a manifest `input=` bit
  string cannot be decoded into the expected typed event payload.
- `semantic`: emitted by the Lean checker when decoded values disagree with
  the Lean theorem instance or complement expected by the manifest row.
- `missing-target`: emitted when a manifest path has no registered Lean target,
  or by CI when the Lake target cannot be built.
- `fixture`: emitted when the manifest is malformed, incomplete, internally
  inconsistent, has duplicate cases, has unexpected productions for the strict
  enum slice, or cannot be read.

The line format is:

```text
FAIL kind=<kind> path=<manifest-or-layer> case=<case-or-manifest> message=<detail>
```

The executable itself emits `Lean-decode`, `semantic`, `missing-target`, and
`fixture`.  The `C-decode` kind is owned by the GitHub Actions wrapper because
the C evaluator and manifest runner live in `rule110/`, outside this Lean
executable.

## Runtime budget

Observed locally on 2026-05-12 after `lake build rule110-cross-check` had
populated the build cache:

| Command | Scope | Wall-clock |
|---|---:|---:|
| `lake exe rule110-cross-check` | 3 registered enum manifests, 15 assertions | 0.41s |
| `lake exe rule110-cross-check` | same | 0.35s |
| `lake exe rule110-cross-check` | same | 0.34s |
| repeated registered slice | 264 manifest arguments, 1320 assertions | 0.35s |

The 1320-assertion run repeats the currently registered 3-manifest slice 88
times, matching the `44 manifests * ~30 assertions` budget shape without
claiming coverage for unregistered families.  On this machine, startup and Lean
import time dominate; per-assertion latency is below the measurement noise at
this scale.  The current evidence leaves substantial headroom under a 30s CI
budget once the executable is already built.  Cold CI time is expected to be
dominated by Lake compilation and cache restore rather than assertion checking.

The project lakefile exposes the checker as the `rule110-cross-check`
executable target.  The source file still has a `main` entry point, so the
manual `lake env lean --run scripts/rule110_cross_check.lean <manifest>...`
form remains available.
