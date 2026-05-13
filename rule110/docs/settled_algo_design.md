# Settled Algo Design

Target relation:

```text
Settled(tag(family) ++ tag(case) ++ payload)
```

The Settled manifest is an aggregator over the already exposed FKernel
projection families. It has no primitive local predicate of its own; after the
two unary tags are decoded, the remaining payload is delegated to one of:

- history kernel representatives;
- Ext and Cont determinacy/unit/associativity representatives;
- signature determinacy and SameSig representatives;
- package/gap representatives;
- globalize exactness representatives;
- composite gap witnesses;
- unary name-certificate representatives;
- function-like descent representatives;
- bundle-generation representatives.

## Required Unbounded Machine

A universal cyclic-tag recognizer would need to compose all lower-family
recognizers and make a top-level choice from the two tags:

1. Decode exactly two unary natural-number tags.
2. Dispatch on the family tag without losing the remaining unbounded payload.
3. Run the matching lower-family recognizer over that payload.
4. Reject malformed tags, unknown families, unknown subcases, trailing input,
   and every malformed lower-family payload.
5. For aggregate cases such as globalize exactness, compose package, gap,
   signature, and history equality checks with shared decoded witnesses.

This is harder than a leaf recognizer. Several leaf families in the current
repository are themselves bounded certificate programs or still have inert
algorithm manifests. A universal Settled recognizer would therefore require
universal NameCert, Package, Gap, Cont, SigRel, and BHist equality recognizers
first, plus a CT-level dispatch convention for accept and reject. The present
manifest runner observes success by comparing an exact tape after a supplied
fuel bound, so it does not yet provide a native top-level boolean halt protocol
for negative cases.

## Bounded Program

`manifests/settled/settled_basic.algo.ct` uses a bounded positional-certificate
program over inputs up to 63 bits. This covers all 38 Settled manifest fixtures
and the short malformed sweep in `tests/test_settled.c`; the longest listed
fixture is 41 bits.

For each position `i`, production `P_i` is:

```text
P_i = 1 ++ binary6(i)
```

The test harness runs the CT program for exactly the input length. Once that
prefix has been consumed, the remaining tape is:

```text
concat(P_i for every input position i containing bit 1)
```

For fixed input length below 64, this certificate records every one-bit
position. The C test separately decodes the same input and checks the Settled
projection semantics, so the bounded run has two independent observations:

```text
CT tape = positional certificate
decoder says Settled = expected yes/no
```

The short-input sweep also runs the CT certificate on every bitstream of length
at most eight and confirms those streams do not decode as complete Settled
payloads.

## Representative Trace

For `history_mark_refl_b0`, the input is:

```text
10111011011
```

The one bits are at positions `0,2,3,4,6,7,9,10`, so after eleven CT steps the
tape is:

```text
10000001000010100001110001001000110100011110010011001010
```

For the negative `bundle_bad` fixture, the input is:

```text
0000000010111011011
```

The CT tape is still a positional certificate:

```text
10010001001010100101110011001001110100111110100011010010
```

The decoder-side Settled check rejects that payload because the bundle
generation projection does not decode a nil or cons bundle.

## Boundary

This is a real cyclic-tag program, but it is not a universal Settled decider.
It is a bounded certificate for the current aggregate fixture corpus and a
small malformed sweep. Universal Settled remains blocked on the lower-family
universal recognizers and a shared CT accept/reject protocol.
