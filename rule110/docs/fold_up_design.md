# FoldMomentKernelUp Design

Primary source:

- `lean4/BEDC/Derived/FoldMomentKernelUp/TasteGate.lean`

`ROADMAP.md` names this row as `Derived/FoldUp`, but the existing Lean module is
`Derived/FoldMomentKernelUp`.  The mirror therefore follows the actual
`FoldMomentKernelUp` taste-gate carrier rather than a separate fold algebra.

The Lean carrier is a nine-field constructor:

```text
FoldMomentKernelUp.mk
  window foldSource fiberLedger momentIndex collisionCount
  transport continuation provenance nameCert
```

Every field is a `BHist`.  The taste-gate event flow interleaves a fixed tag
event before each field event:

```text
tag(0), window,
tag(1), foldSource,
tag(2), fiberLedger,
tag(3), momentIndex,
tag(4), collisionCount,
tag(5), transport,
tag(6), continuation,
tag(7), provenance,
tag(8), nameCert
```

where `tag(n)` is the raw event `n` copies of `b1` followed by `b0`.  The Lean
decoder currently checks the 18-event shape and field positions, but treats tag
payloads as structural separators instead of validating their exact contents.

## Event Encoding

The manifests reuse the GroundCompiler event convention:

```text
b0 -> 0
b1 -> 10
event terminator -> 11
```

Thus the first three tags and common field values are:

```text
tag(0) = EventEncoding([0])       = 011
tag(1) = EventEncoding([1,0])     = 10011
tag(2) = EventEncoding([1,1,0])   = 1010011

Empty        = 11
e0 Empty     = 011
e1 Empty     = 1011
e0(e1 Empty) = 01011
e1(e0 Empty) = 10011
```

## Mirrored Theorems

`fold_round_trip.enum.ct` mirrors the finite surface of:

- `foldMomentKernelDecodeEncodeBHist`
- `foldMomentKernel_round_trip`
- `FoldMomentKernelTasteGate_visible_rows`

Each assertion input is the full 18-event flow for one nine-field kernel.  The C
harness decodes all fields, re-encodes the flow with the canonical tag schedule,
and checks exact equality with the manifest input.  It also checks that every
decoded mark is `0` or `1`, matching the conservativity clause in
`FoldMomentKernelTasteGate_visible_rows`.

`fold_tag_layout.enum.ct` mirrors the closed tag schedule used by
`foldMomentKernelToEventFlow`.  Each assertion is a single full kernel flow; the
harness checks that event positions `0,2,4,...,16` are exactly `tag(0)` through
`tag(8)` and that all odd positions are decodable `BHist` field events.

`fold_injectivity.enum.ct` mirrors the injective half of:

- `foldMomentKernelToEventFlow_injective`
- `foldMomentKernelChapterTasteGate.layer_separation`
- `FoldMomentKernelTasteGate_visible_rows`

Each assertion input is a pair of full kernel flows.  The harness decodes both,
checks whether the nine fields are pointwise equal, and verifies that canonical
event-flow equality agrees with field equality.  This gives finite ground
instances of the Lean statement that equal event flows determine equal
`FoldMomentKernelUp` values.

## Assertion Keys

The assertion key set is:

```text
theorem=<target-key>
fields=9
events=18
round_trip=yes
tag_layout=canonical
conservative_marks=yes
left_fields=<nat>
right_fields=<nat>
flows_equal=yes|no
fields_equal=yes|no
layer_separation=yes
conclusion_holds=yes
```

Target keys are finite strings:

```text
fold_bhist_decode_encode
fold_round_trip
fold_visible_rows
fold_tag_layout
fold_event_flow_injective
fold_layer_separation
```

## Boundary

This row is a representative cyclic-tag manifest mirror of the existing
`FoldMomentKernelUp` taste-gate carrier.  It does not claim an unbounded
cyclic-tag recognizer for all possible fold-moment kernels, and it does not
mirror a separate `Derived/FoldUp` fold algebra because no such Lean module is
present in this worktree.
