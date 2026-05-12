# ProbeBundle Design

Primary sources:

- `lean4/BEDC/FKernel/Bundle.lean`
- `lean4/BEDC/FKernel/Bundle/Length.lean`
- `lean4/BEDC/FKernel/Bundle/MembershipAppend.lean`
- `lean4/BEDC/FKernel/Bundle/Cancellation.lean`
- `lean4/BEDC/FKernel/Bundle/ResultInversion.lean`

`ProbeBundle PName` is a generated list:

```text
Bnil | Bcons p tail
```

The Lean carrier `PName` is abstract. The rule110 manifests use the concrete
fixture already recorded in `sigrel_design.md`:

```text
ProbeName := Nat
ProbeName(n) payload = [0 repeated n, 1]
ProbeNameEncoding(n) = EventEncoding(ProbeName(n) payload)
```

The bundle terminator is a reserved event payload:

```text
Bnil = EventEncoding([1,1])
Bcons p tail = ProbeNameEncoding(p) ++ tail
```

This makes a bundle an event list. Each non-terminal event must be a unary
probe-name event: zero or more `0` bytes followed by a single `1`. The terminal
event is exactly `[1,1]`. The reserved marker is not a valid probe event under
the unary parser, so stream boundaries are unambiguous.

## Theorem Coverage

`bundle_length.*.ct` covers the length and append spine:

- `bundleLength_append`, `bundleLength_bundleAppend`,
  `bundleAppend_length`
- `bundleAppend_nil_right`, `bundleAppend_right_nil`
- `bundleAppend_assoc`
- `bundleAppend_eq_right_iff_left_nil`,
  `bundleAppend_eq_left_iff_right_nil`
- fixed-length split uniqueness for two and three adjacent bundle segments

`bundle_membership.*.ct` covers membership, split, cancellation, and result
inversion:

- nil, cons, singleton, and append membership theorems
- three-way and four-way append membership flattening
- member split witnesses and uniqueness at a fixed prefix length
- prefix, suffix, common-context, and middle cancellation
- cons-result and empty-result append inversion

The `.enum.ct` files provide audit-readable representative assertions. The
`.algo.ct` files keep the same semantic fixtures with a vacuous CT production
under the current manifest-runner contract. Runtime checking is implemented in
`tests/test_bundle.c`, which decodes the event streams and verifies the list
semantics directly.

## Decoder Semantics

The test harness treats a decoded bundle as a finite array of natural probe
names. Append is array concatenation, length is array length, and `InBundle p`
is membership in the array. Equality is byte equality of the probe-name array.

The checks intentionally include implication-vacuous cases. For example,
`bundleAppend_eq_right_iff_left_nil` is checked both when `left = Bnil` and when
`left` is non-empty; in the non-empty case the equality premise is false and
the equivalence still holds.
