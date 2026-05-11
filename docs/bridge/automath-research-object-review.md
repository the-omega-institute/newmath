# Automath Research Object Review

## Intake Status

This note is the durable NewMath-side review surface for the current
Automath-to-NewMath bridge index. The current inputs are useful as research
objects, but the index marks them as synthesis-only review leads. They are not
BEDC BOARD entries, not accepted proposals, and not Lean or paper writebacks.

| Field | Value |
| --- | --- |
| Source index | `docs/bridge/automath-consumption-index.md` |
| Input source | `synthesis` |
| Destination owner | BEDC board and supervisor pipelines |
| Durable action here | classify and prioritize review surfaces |
| Forbidden action here | append to `tools/bedc-deep/BOARD.completed.md` |

## Current Mathematical Families

The present Automath candidates fall into four NewMath-relevant families.
These families are useful because they name the kind of BEDC receiving surface
that would be needed before any candidate can move beyond review.

| Family | Representative sources | NewMath receiving interpretation |
| --- | --- | --- |
| Golden algebra and recovery | `GoldenAlternatingConstantsRecoverPhi.lean`, `EventEllipseGoldenMinimal.lean` | exactness, name certificate, and public readback surfaces |
| Fold and resonance mechanisms | `FoldGoldenResonanceCollisionGapHardFloor.lean`, `FoldGoldenResonanceMaxfiberLift.lean`, `FoldgaugePiGoldenLinearLaw.lean`, `FoldingGoldenEllipseRealization.lean` | mechanism candidates requiring BEDC fit, novelty, and target selection |
| Fibonacci and Lucas growth | `GoldenFibonacciAuditTwoPeriodicRigidity.lean`, `GoldenFibonacciMixedPowerSuperexponential.lean`, `GoldenLucasHankelArchimedeanCubicGrowth.lean` | audit and growth-law surfaces, best handled as exactness or determinacy review |
| Coupling and rigidity | `GoldenBiasSecondOrderUniqueness.lean`, `GoldenCouplingFiniteKRigidity.lean`, `FibadicGoldenExtensionNoIntrinsicQ5Realization.lean` | obstruction, uniqueness, and boundary surfaces |

The bridge should not treat the shared word "golden" as sufficient evidence
for BEDC intake. Each candidate needs a BEDC-native target: a carrier, source
specification, public certificate, exactness theorem, readback ledger, or
boundary statement that exists in the `BEDC.Derived.*Up` surface.

## Gate Consequences

The Automath files are useful because they already expose paper-facing theorem
packages and Lean declarations. They are still not enough for automatic BEDC
consumption. A NewMath intake candidate should pass these gates before it is
offered to `board_spawn`:

| Gate | Required evidence |
| --- | --- |
| Source evidence | exact Automath path, ref, commit, theorem name, and paper label when present |
| Mathematical role | one of exactness, readback, name certificate, public surface, boundary, or mechanism |
| BEDC receiving target | a plausible `BEDC.Derived.*Up` family or paper section |
| Fit and novelty | no duplicate target already present in BEDC board, completed archive, or current paper parts |
| Operator boundary | synthesis-only rows remain review-only until deterministic bridge gates pass |

This means the present index is meaningful, but its meaning is prioritization.
It should guide the next scanner pass toward exact receiving targets rather
than produce immediate BOARD or paper writes.

## Preferred Priority Order

The most productive next NewMath-side consumption path is:

| Priority | Candidate type | Reason |
| ---: | --- | --- |
| 1 | exactness and recovery identities | easiest to map to certificate or readback surfaces |
| 2 | rigidity and uniqueness packages | likely to become boundary or determinacy rows |
| 3 | fold/resonance mechanisms | potentially valuable, but needs stronger target selection |
| 4 | publication-level paper claims | useful for context, but too broad for direct BEDC intake |

The bridge should therefore prefer small theorem packages with explicit Lean
names over broad paper files. Paper files may remain context sources, but BEDC
production should be driven by a narrow theorem, target surface, and audit
story.

## Non-Actions

This review does not accept any Automath record into BEDC. It also does not
write BEDC Lean, modify BEDC paper parts, or mark `BOARD.completed.md`.
The next valid production step is to generate target-specific gate records for
one or two high-priority Automath theorem packages and let the existing BEDC
board adapter judge fit, novelty, deduplication, and paper coverage.
