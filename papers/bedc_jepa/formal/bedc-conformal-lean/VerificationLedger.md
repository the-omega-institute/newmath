# Verification Ledger

This package is mathlib-free. The Lake configuration contains no `require mathlib`;
the development uses Lean 4 core, natural numbers, booleans, and lists.

## Checked Claims

The Lean statements are:

```lean
theorem fail_closed_selects_empty
    (cal : List Bool) (alphaNum alphaDen : Nat) :
    selectIdx cal alphaNum alphaDen = none ->
      okCount cal (selectIdx cal alphaNum alphaDen) = 0
```

```lean
theorem selected_satisfies_conservative_bound
    (cal : List Bool) (alphaNum alphaDen i : Nat) :
    selectIdx cal alphaNum alphaDen = some i ->
      (1 + cumFail cal i) * alphaDen <= alphaNum * (1 + (i + 1))
```

```lean
theorem coverage_counting_correct
    (cal : List Bool) (alphaNum alphaDen i : Nat) :
    selectIdx cal alphaNum alphaDen = some i ->
      i < cal.length ->
        (cal.take (i + 1)).length = i + 1
```

```lean
theorem cumFail_monotone
    (cal : List Bool) (i j : Nat) :
    i <= j -> cumFail cal i <= cumFail cal j
```

## Kernel Dependency Audit

The final `lake build` emitted:

```text
info: ConformalCounting.lean:176:0: 'ConformalCounting.fail_closed_selects_empty' does not depend on any axioms
info: ConformalCounting.lean:177:0: 'ConformalCounting.selected_satisfies_conservative_bound' does not depend on any axioms
info: ConformalCounting.lean:178:0: 'ConformalCounting.coverage_counting_correct' does not depend on any axioms
info: ConformalCounting.lean:179:0: 'ConformalCounting.cumFail_monotone' does not depend on any axioms
Build completed successfully (3 jobs).
```

The checked Lean source contains no primitive assumption keyword and no
placeholder proof keywords. The dependency output contains no `Classical.choice`,
`Quot.sound`, or `propext` dependency for the four main theorems.

## Open Statistical Step

The exchangeability-to-distribution-free-miscoverage step of split conformal
prediction is not formalized here. The package verifies only the deterministic
finite counting kernel for the sorted calibration list, the fail-closed branch,
the conservative Laplace counting bound attached to the selected prefix, the
prefix coverage count, and monotonicity of cumulative failures.
