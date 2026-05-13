# Ext CT Algorithm Design

## Target

The target relation is:

```text
Ext h b r
```

with exactly two valid constructor cases:

```text
Ext h b0 (e0 h)
Ext h b1 (e1 h)
```

The input stream is:

```text
EventEncoding(h) ++ EventEncoding([b]) ++ EventEncoding(r)
```

where `h` and `r` are BHist choice payloads, and the mark event has exactly one
decoded byte.

## Required Unbounded Recognizer

A universal cyclic-tag recognizer must do all of the following on arbitrary
input length:

1. Split exactly three event encodings at their `11` terminators.
2. Decode event bodies, treating `0` as constructor choice `0` and `10` as
   constructor choice `1`.
3. Require the middle event to decode to exactly one bit.
4. Strip one constructor from `r`, require it to match the mark, and compare the
   remaining decoded tail with `h`.
5. Reject malformed encodings, missing events, trailing input, `Empty` result,
   wrong result head, short or long tails, and any tail mismatch.

The small semantic predicate hides the hard CT operation: the machine must keep
an unbounded copy of decoded `h` until the result tail is available, then
compare the two streams exactly. That is the same queue-copy/compare obstacle
described for Cont. It is implementable with a compiled tag-system layer, but
there is not enough local infrastructure to install and audit such a compiler
inside this task.

The current manifest runner also accepts by exact final tape after a caller
supplied fuel bound. It has no native typed accept/reject channel beyond empty
tape versus observed tape, so a universal semantic recognizer would need an
extra convention for positive and negative halts before it could replace the C
decoder checks cleanly.

## Bounded Program

`manifests/ext/ext_step.algo.ct` therefore uses a bounded positional-certificate
cyclic-tag program for inputs up to 64 bits.

For each position `i`, production `P_i` is:

```text
P_i = 1 ++ binary6(i)
```

The test harness executes the CT system for exactly `input_length` steps. During
those steps the original input prefix is consumed once. Whenever the consumed
bit is `1`, the production selected by the cyclic program counter is appended.
The final tape is:

```text
concat(P_i for every input position i containing bit 1)
```

This certificate is produced by the CT evaluator and is independent of the
decoder-side Ext predicate. The C harness checks both:

```text
CT tape = positional certificate
decoder says Ext h b r = expected yes/no
```

## Coverage

The manifest assertions cover:

- both valid constructors at depths 0, 1, and 2;
- `Empty` result rejection;
- wrong result head for both marks.

`tests/test_ext.c` also sweeps all well-formed Ext triples with source depth
`<= 3` and candidate result depth `<= 4`, plus representative malformed and
trailing-input streams. All swept inputs are below the 64-bit certificate
bound.

This is a bounded CT witness, not a universal Ext decider.
