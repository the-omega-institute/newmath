# LabVerificationLedger

## Build

Command sequence for this lab-local kernel:

```bash
cd papers/bedc-quality-lab/formal/lean
lake exe cache get
lake build
```

Measured result:

- `lake exe cache get` completed successfully.
- Cache source: Azure cache from `leanprover-community/mathlib4`.
- Cache action: no files to download; 8010 files already decompressed or
  decompressed during the run.
- `lake build` completed successfully with 620 jobs.

## Substrate

This directory is an isolated Lean package. Its `lean-toolchain` is
`leanprover/lean4:v4.28.0`, and its `lakefile.lean` requires Mathlib from
`leanprover-community/mathlib4` at tag `v4.28.0`.

The repository root `lean4/` substrate remains separate and mathlib-free.

## Proved statements

- `Classifier.sameClass_refl`
- `Classifier.sameClass_symm`
- `Classifier.sameClass_trans`
- `Classifier.sameClass_equivalence`
- `MarginStability.mark_stable_of_margin`
- `Ledger.mem_required_decidable`
- `FiniteLedgerCoverage.coverage_of_recorded_witnesses`
- `FiniteLedgerCoverage.missingRow_not_covered`

## Declared axioms

Measured `#print axioms` output:

```text
'Classifier.sameClass_refl' does not depend on any axioms
'Classifier.sameClass_symm' does not depend on any axioms
'Classifier.sameClass_trans' does not depend on any axioms
'Classifier.sameClass_equivalence' does not depend on any axioms
'MarginStability.mark_stable_of_margin' does not depend on any axioms
'Ledger.mem_required_decidable' depends on axioms: [propext]
'FiniteLedgerCoverage.coverage_of_recorded_witnesses' depends on axioms: [propext]
'FiniteLedgerCoverage.missingRow_not_covered' depends on axioms: [propext]
```

## Not formalized

- No real-analysis transcription of score functions, thresholds, absolute
  perturbation bounds, or epsilon margins is formalized here.
- No theorem in this kernel connects the finite threshold-side certificate to
  the BEDC paper theory or to Python evidence producers.
- No completeness theorem for all explanation evidence is formalized here.

## Trust boundary

The formal claim is limited to finite lab kernels in this directory. Python
schemas, discovery code, paper text, and the repository root Lean development
are opaque consumers or separate substrates.

## Forbidden claims

This ledger explicitly forbids the claim `fully verified explanation`.

The formalized claim is only minimal hardening for finite lab kernels. It does
not claim BEDC theory closure, complete explanation verification, or full
coverage of all evidence semantics.
