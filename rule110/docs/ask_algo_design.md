# Ask Algo Design

Target relation:

```text
Ask(probe, history, mark, evidence)
```

under the concrete fixture from `docs/ask_design.md`:

```text
mark = evidence = (probe + depth(history)) mod 2
```

## Input Contract

The input tape is exactly four GroundCompiler events:

```text
ProbeNameEncoding(probe)
+ BHistEncoding(history)
+ EventEncoding(mark)
+ EventEncoding(evidence)
```

The probe event is a unary natural `[0 repeated n, 1]`. The history is a
GroundCompiler event whose payload is the constructor-choice sequence, so its
depth is the decoded event payload length. The mark and evidence events must
each contain exactly one bit.

## Required Unbounded Machine

A full cyclic-tag recognizer must do all of the following without a fixed input
bound:

1. split exactly four GroundCompiler events at their `11` terminators;
2. reject malformed event bodies, unfinished events, and trailing input;
3. check that the probe payload is unary: zero or more `0` bytes followed by
   exactly one final `1`;
4. compute `(probe + depth(history)) mod 2` while reading the first two events;
5. check that the third and fourth decoded events are one-bit payloads equal to
   the computed parity;
6. halt in the accept convention used by the manifest runner.

The parity part is finite-state: each decoded probe zero and each decoded
history choice toggles a one-bit state; the final probe `1` toggles once more.
The harder part is compiling the GroundCompiler event lexer into a cyclic-tag
program with a reliable reject discipline. A malformed input can fail in several
ways: dangling `1`, missing terminator, non-unary probe payload, short event
count, extra trailing event data, and non-one-bit mark or evidence. The current
manifest runner observes only an exact final tape after a caller-supplied step
bound, with empty tape as natural halt. It has no native "reject state" or
"halt with non-empty accept marker" convention for an unbounded lexer.

## Bounded Program

`manifests/ask/ask_basic.algo.ct` therefore uses the same bounded positional
certificate pattern as the Cont and Bundle algorithm manifests.

For each position `i`, production `P_i` is:

```text
P_i = 1 ++ binary6(i)
```

The test harness runs the CT program for exactly the input length. At that
point the input prefix has been consumed and the remaining tape is:

```text
concat(P_i for every input position i containing bit 1)
```

The manifest provides 64 productions, so the certificate is injective for input
positions below 64. The Ask representative inputs are at most 20 bits long, and
the bounded sweep in `tests/test_ask.c` stays below that limit.

The CT run and semantic decoder are checked together:

```text
CT tape = positional certificate
decoder says Ask = expected yes/no
```

This is a real CT trace witness whose output depends on the whole input bit
pattern, but it is not an unbounded Ask decider.

## Representative Trace

For the positive case `probe = 0`, `history = Empty`, `mark = 0`, and
`evidence = 0`, the input is:

```text
101111011011
```

The one bits occur at positions `0, 2, 3, 4, 5, 7, 8, 10, 11`, so after twelve
steps the remaining tape is:

```text
100000010000101000011100010010001011000111100100010010101001011
```

For the negative case with the same probe and history but the wrong evidence,
the input is:

```text
1011110111011
```

The CT run still produces the expected positional certificate, while the
decoder-side Ask predicate rejects the quadruple because the evidence bit does
not equal the computed parity.

## Full Recognizer Shape

The unbounded recognizer should be implemented as a compiled finite-control
cyclic-tag lexer for the four-event language. Since Ask only needs parity and
one-bit payload checks, it does not need to store the history or probe payloads;
it only needs to retain:

```text
event_index, lexer_substate, probe_seen_final_one, parity, mark_bit, evidence_bit
```

A complete recognizer is best expressed by a small generator that emits CT
productions from a finite state machine and records a proof table for every
transition.
