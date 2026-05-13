# TopologyUp Design

Primary sources:

- `lean4/BEDC/Derived/TopologyUp.lean`
- `lean4/BEDC/Derived/TopologyUp/Core.lean`
- `lean4/BEDC/Derived/TopologyUp/FiniteBaseNeighborhood.lean`

`TopologyUp` is a thin derived layer over `BHist`, `ProbeBundle`, `UnaryHistory`,
`hsame`, and `Cont`.  Its abstract carrier fields are not finite data by
themselves, so the rule110 mirror uses the finite-base carrier where

```text
OpenIx := ProbeBundle BHist
meet   := bundleAppend
OpenAt indices x := forall i, InBundle i indices -> ball i x
```

The manifest layer records representative finite instances of the closed-form
theorems whose inputs decode directly from GroundCompiler event streams.

## Event Encoding

The manifests reuse the existing `BHist` event encoding:

```text
Empty        = 11
e0 Empty     = 011
e1 Empty     = 1011
e0(e1 Empty) = 01011
```

A `ProbeBundle BHist` is encoded as a list of BHist events followed by the
same bundle terminator used by the FKernel bundle fixtures:

```text
Bnil = EventEncoding([1,1]) = 101011
Bcons h tail = BHistEncoding(h) ++ tail
```

The terminator event payload `[1,1]` is not used as a BHist item in these
fixtures.  A strict cross-checker should keep the family-specific type
separate from `ProbeBundle Nat`; both use event-list streams, but their item
decoders differ.

## Mirrored Theorems

`topology_finite_base_neighborhood.enum.ct` mirrors:

- `BHistFiniteBaseNeighborhood_append_decomposition`
- `BHistFiniteBaseNeighborhoodCarrier_meet_scope_rows`

Each assertion input is:

```text
Bundle(BHist) left ++ Bundle(BHist) right ++ BHist point
```

The C harness checks that decoding is exact, that bundle append is list
concatenation, and that neighborhood membership over the appended index set is
the conjunction of membership over the two parts.  The actual `ball` predicate
is represented by a deterministic finite fixture function in the harness,
because the Lean theorem is parametric in `ball`.

`topology_carrier_rows.enum.ct` mirrors:

- `BHistFiniteBaseNeighborhoodCarrier_scope_rows`
- `BHistFiniteBaseNeighborhoodCarrier_indexed_open_laws`

The main decoded shape is:

```text
Bundle(BHist) left ++ Bundle(BHist) right ++ BHist ledger
```

The harness checks that the carrier meet index is `bundleAppend left right`,
that the ledger decodes as a unary history fixture (`Empty`, `e1 Empty`, or
`e1(e1 Empty)` in these cases), and that the left row and append carries
clauses have the intended finite-base surface.

`topology_ledger_tags.enum.ct` mirrors:

- `BHistUnaryTopologyLedgerRow_constructor_coverage`
- `BHistUnaryTopologyLedgerRow_constructor_tag_no_confusion`

Each assertion input is:

```text
BHist rowTag ++ BHist expectedTag ++ BHist ledger
```

The six row constructors use the finite tag set from Lean:

```text
singletonMetricBall     -> Empty
finiteListIntersection  -> e0 Empty
binaryGeneratedMeet     -> e1 Empty
arbitraryUnion          -> e0(e0 Empty)
bottom                  -> e0(e1 Empty)
top                     -> e1(e0 Empty)
```

The harness checks exact tag equality for positive rows and pairwise
non-equality for representative no-confusion rows.

## Cross-Check Extension

`rule110/lean-side/Rule110CrossCheck/**` should register a new
`topology_up` manifest family with these decoders:

```text
parseBHistBundle : Cursor -> Option (ProbeBundle BHist x Cursor)
parseFiniteBaseAppendCase : bits -> Option (left, right, x)
parseCarrierRowCase : bits -> Option (left, right, ledger)
parseLedgerTagCase : bits -> Option (rowTag, expectedTag, ledger)
```

The target keys should be finite strings, not theorem-name reflection:

```text
finite_base_append_decomposition
finite_base_carrier_meet_scope
finite_base_indexed_open_laws
ledger_constructor_coverage
ledger_constructor_tag_no_confusion
```

Positive checks are ground instances of universal Lean theorems under the
finite-base carrier.  The manifests do not claim an unbounded cyclic-tag
recognizer for arbitrary topology syntax; strict recognizers belong to Level 2.

## Assertion Keys

The assertion key set is:

```text
theorem=<target-key>
left_len=<nat>
right_len=<nat>
append_len=<nat>
point=<hist-name>
ledger=<hist-name>
row_constructor=<constructor-name>
tag=<hist-name>
expected_tag=<hist-name>
conclusion_holds=yes
tags_distinct=yes
```

Unknown keys should be rejected by the Lean cross-checker once the family is
registered.
