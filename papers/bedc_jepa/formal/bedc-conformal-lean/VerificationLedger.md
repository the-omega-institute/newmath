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
-- selectIdx only returns in-range indices, so the admitted count of the
-- selected index equals the selected prefix length (no extra hypothesis).
theorem selectIdx_lt
    (cal : List Bool) (alphaNum alphaDen i : Nat) :
    selectIdx cal alphaNum alphaDen = some i -> i < cal.length

theorem coverage_counting_correct
    (cal : List Bool) (alphaNum alphaDen i : Nat) :
    selectIdx cal alphaNum alphaDen = some i ->
      okCount cal (selectIdx cal alphaNum alphaDen) = (cal.take (i + 1)).length
```

```lean
theorem cumFail_monotone
    (cal : List Bool) (i j : Nat) :
    i <= j -> cumFail cal i <= cumFail cal j
```

## Kernel Dependency Audit

The final `lake build` emitted:

```text
info: 'ConformalCounting.fail_closed_selects_empty' does not depend on any axioms
info: 'ConformalCounting.selected_satisfies_conservative_bound' does not depend on any axioms
info: 'ConformalCounting.coverage_counting_correct' does not depend on any axioms
info: 'ConformalCounting.cumFail_monotone' does not depend on any axioms
Build completed successfully (3 jobs).
```

The checked Lean source contains no primitive assumption keyword and no
placeholder proof keywords. The dependency output contains no `Classical.choice`,
`Quot.sound`, or `propext` dependency for the four main theorems.

## Scope and Open Step

The formalized object is the deterministic finite counting kernel over a
failure-indicator list **already ordered by score**. The score sort itself, the
numeric threshold readout `tau = s_sorted[i]`, and the evaluation-side
`score <= tau` comparison in `_conformal_calibration.py` are the trusted
numerical harness around this kernel and are not themselves formalized.

The exchangeability-to-distribution-free-miscoverage step of split conformal
prediction is likewise not formalized. The package verifies only the fail-closed
branch, the conservative Laplace counting bound attached to the selected prefix,
the admitted-count/prefix-length identity for the selected index, and
monotonicity of cumulative failures.
