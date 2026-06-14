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

The package also proves the finite-sample order-statistic coverage bound itself
over a sorted score list, where `kthSmallest scores k` is the `k`-th order
statistic and `countLE t scores` counts the scores at most `t`:

```lean
theorem coverage_count_ge_k
    (scores : List Nat) (k : Nat) :
    Sorted scores -> k <= scores.length ->
      k <= countLE (kthSmallest scores k) scores

theorem finite_coverage_count
    (scores : List Nat) (k : Nat) :
    Sorted scores -> k <= scores.length ->
      scores.length - countLE (kthSmallest scores k) scores <=
        scores.length - k

theorem finite_miscoverage_bound
    (scores : List Nat) (k alphaNum alphaDen : Nat) :
    Sorted scores ->
    k <= scores.length ->
    alphaNum <= alphaDen ->
    (alphaDen - alphaNum) * scores.length <= k * alphaDen ->
      (scores.length - countLE (kthSmallest scores k) scores) * alphaDen <=
        alphaNum * scores.length
```

`coverage_count_ge_k` is the order-statistic core: at least `k` of the sorted
scores are at most the `k`-th order statistic, so the threshold covers at least
`k` of the `m` calibration positions. `finite_miscoverage_bound` couples this to
`alpha`: once `k` meets the quantile budget `(alphaDen - alphaNum) * m <=
k * alphaDen` (that is, `k / m >= 1 - alpha`), the miscoverage fraction is at
most `alpha`. This is the deterministic rank-quantile core established by
counting, not the trivial `m - k <= m`.

On a strictly sorted (distinct) list the bound is two-sided. With
`StrictSorted scores` the count at most the `k`-th order statistic is also at
most `k`, so it equals `k` exactly and the miscoverage count equals `m - k`:

```lean
theorem coverage_count_le_k
    (scores : List Nat) (k : Nat) :
    StrictSorted scores -> 1 <= k -> k <= scores.length ->
      countLE (kthSmallest scores k) scores <= k

theorem coverage_count_eq_k
    (scores : List Nat) (k : Nat) :
    StrictSorted scores -> 1 <= k -> k <= scores.length ->
      countLE (kthSmallest scores k) scores = k

theorem two_sided_coverage_interval
    (scores : List Nat) (k : Nat) :
    StrictSorted scores -> 1 <= k -> k <= scores.length ->
      scores.length - countLE (kthSmallest scores k) scores =
        scores.length - k
```

`coverage_count_le_k` is where distinctness is used: positions past the `k`-th
order statistic are strictly larger, so none of them is at most the threshold.
With ties the upper bound can fail, which is why `StrictSorted` (not `Sorted`)
is the hypothesis. Together with `coverage_count_ge_k` this gives the exact
finite-sample coverage characterization rather than only its lower side.

## Kernel Dependency Audit

The final `lake build` emitted:

```text
info: 'ConformalCounting.fail_closed_selects_empty' does not depend on any axioms
info: 'ConformalCounting.selected_satisfies_conservative_bound' does not depend on any axioms
info: 'ConformalCounting.coverage_counting_correct' does not depend on any axioms
info: 'ConformalCounting.cumFail_monotone' does not depend on any axioms
info: 'ConformalCounting.strictSorted_sorted' does not depend on any axioms
info: 'ConformalCounting.coverage_count_ge_k' does not depend on any axioms
info: 'ConformalCounting.coverage_count_le_k' does not depend on any axioms
info: 'ConformalCounting.coverage_count_eq_k' does not depend on any axioms
info: 'ConformalCounting.two_sided_coverage_interval' does not depend on any axioms
info: 'ConformalCounting.finite_coverage_count' does not depend on any axioms
info: 'ConformalCounting.finite_miscoverage_bound' does not depend on any axioms
Build completed successfully (3 jobs).
```

The checked Lean source contains no primitive assumption keyword and no
placeholder proof keywords. The dependency output contains no `Classical.choice`,
`Quot.sound`, or `propext` dependency for the eleven theorems.

## Scope and Open Step

The formalized object is the deterministic finite counting kernel over a
failure-indicator list **already ordered by score**. The score sort itself, the
numeric threshold readout `tau = s_sorted[i]`, and the evaluation-side
`score <= tau` comparison in `_conformal_calibration.py` are the trusted
numerical harness around this kernel and are not themselves formalized.

The package verifies the fail-closed branch, the conservative Laplace counting
bound attached to the selected prefix, the admitted-count/prefix-length identity
for the selected index, monotonicity of cumulative failures, and the
finite-sample order-statistic coverage bound (the rank-quantile counting core:
the `k`-th order statistic threshold covers at least `k` of `m` positions, so the
miscoverage fraction is at most `alpha` once `k / m >= 1 - alpha`). What remains
outside the formalization is the exchangeability step --- that a fresh test
point's rank among the calibration scores is uniform --- which is what converts
this deterministic order-statistic bound into a distribution-free probabilistic
coverage guarantee; that step is recorded as open rather than claimed.
