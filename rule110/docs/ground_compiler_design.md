# GroundCompiler Rule110-Substrate Mirror

## Purpose

`GroundCompiler` is the channel encoding used by the rule110 manifest layer
itself:

```text
b0 -> 0
b1 -> 10
event terminator -> 11
flow -> concatenated event encodings
```

This makes the Level 5.7 mirror meta-circular.  The manifest input language is
already a GroundCompiler display stream, so the mirror does not introduce a
second encoding for the compiler.  It records finite theorem instances about
the same channel that carries the instances.

## Lean Surface Mirrored

The closed-form Lean targets are in
`BEDC.GroundCompiler.ChannelEncoding`:

```text
event_level_round_trip
flow_level_round_trip
legal_stream_completeness
channel_encoding_bijection
prototype_roundtrip_correctness
channel_conservativity
channel_encoding_0111_illegal
```

The C mirror also exercises the implementation-level reject taxonomy exposed by
`encoder/groundcompiler_encoding.h`:

```text
GC_REJECT_DANGLING_ONE
GC_REJECT_UNFINISHED_EVENT
GC_REJECT_NONBINARY_CHARACTER
GC_REJECT_EMPTY_INPUT_POLICY
GC_REJECT_RESOURCE_BOUND_EXCESS
GC_REJECT_NONCANONICAL_DISPLAY
```

The six reject names are C-level classifications for malformed concrete
channels.  The Lean file proves the pure binary channel theorem; the rule110
mirror keeps the concrete error taxonomy as a bounded implementation contract.

## Manifest Format

All files in `manifests/ground_compiler/` use the existing line format:

```text
PRODUCTIONS 0
ASSERTIONS <n>
case <name>: input=<bits-or-display> ; theorem=<target> ; key=value
```

The cyclic-tag program is intentionally empty-production enumeration.  The
semantic work is in the assertion table and the C test harness:

```text
manifest assertion
  -> existing manifest runner smoke
  -> GroundCompiler byte/display parser
  -> theorem-family checker
```

The canonical `input=` field is a string over `0` and `1`.  The reject-reason
manifest uses `input=<empty>` for the empty-channel policy and `input=01x11`
for the display-level nonbinary case.  `display=01011_` denotes a
noncanonical display spelling: the binary payload is readable after removing
layout characters, but the manifest display is rejected because canonical
display has no separators or whitespace.

## Encoded Theorem Families

### `flow_round_trip.enum.ct`

Input shape:

```text
FlowEncoding(S)
```

Fields:

```text
theorem=flow_level_round_trip
events=<count>
round_trip=yes
conservative_marks=yes
canonical=yes
```

The checker decodes the entire flow event by event, re-encodes it with
`gc_flow_encode`, and requires byte-for-byte equality with the original input.
This is a bounded ground instance of `flow_level_round_trip` and
`channel_conservativity`.

### `bhist_injectivity.enum.ct`

Input shape:

```text
EventEncoding(h1) ++ EventEncoding(h2)
```

Fields:

```text
theorem=channel_encoding_bijection
left=<BHist name>
right=<BHist name>
same_source=yes|no
same_encoding=yes|no
```

The checker decodes exactly two BHist events, re-encodes both events, and checks
that equal canonical encodings imply equal decoded histories.  This is finite
coverage of the injective direction supplied by the channel bijection.

### `reject_reasons.enum.ct`

Input shape:

```text
malformed display channel
```

Fields:

```text
theorem=groundcompiler_reject_taxonomy
expected_reject=<reason>
```

Rows cover the six implementation statuses:

```text
DANGLING_ONE
UNFINISHED_EVENT
NONBINARY_CHARACTER
EMPTY_INPUT_POLICY
RESOURCE_BOUND_EXCESS
NONCANONICAL_DISPLAY
```

`NONCANONICAL_DISPLAY` is checked before byte decoding.  It is a manifest-level
display policy, not a Lean channel theorem and not a status reachable from a
strict binary byte array.

## Boundary

This is a bounded enum mirror.  It does not claim a universal cyclic-tag
recognizer for all legal streams, does not alter the GroundCompiler C
implementation, and does not replace the Lean proofs.  It records executable
representative instances of the theorem surface while using GroundCompiler
itself as the underlying channel.
