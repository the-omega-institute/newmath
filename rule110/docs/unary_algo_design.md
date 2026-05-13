# Unary CT Algorithm Design

## Encoding

Unary inputs use the existing BHist event encoding:

```text
BHistEncoding(h) = EventEncoding(choices(h))
```

The all-one histories therefore have the regular bit shape:

```text
(10)^n 11
```

A payload zero is a literal `0` in the event body. The empty history is the
two-bit event terminator `11`.

## CT Program

The algorithm manifest uses an eight-production positional certificate:

```text
P_i = 1 ++ binary3(i)        for 0 <= i < 8
```

The test harness runs the cyclic-tag system for exactly the input length. During
that pass, every consumed source bit equal to `1` appends the active production,
and every consumed source bit equal to `0` appends nothing. The remaining tape
is:

```text
concat(P_i for each input position i whose bit is 1)
```

This certificate is produced by the cyclic-tag evaluator itself. It records the
one-bit positions in the scanned BHist encoding.

For example, input `1011` has one bits at positions `0`, `2`, and `3`. Running
for four steps leaves:

```text
100010101011
```

## Recognition Boundary

The full Unary predicate is the local condition "the decoded payload contains no
zero". In the binary cyclic-tag evaluator, a `1` head appends the active
production and a `0` head only deletes itself. The manifest runner exposes a
production list, an initial tape, an expected final tape, and a fuel bound; it
does not expose separate accept and reject states.

Under that interface, the CT program is a real scan certificate, while the
universal accept/reject decision remains at the decoded semantic layer in
`tests/test_unary.c`. A complete universal classifier needs one of these
additional pieces:

- a runner-level convention for observing a non-empty reject marker before
  natural halt;
- a compiled state encoding that lets a literal payload `0` force a permanent
  non-empty tape while `(10)^n11` reaches empty halt;
- or an audited macro compilation from a two-state streaming recognizer into the
  binary CTS model.

The eight-production manifest covers every existing Unary fixture and keeps the
open boundary explicit.
