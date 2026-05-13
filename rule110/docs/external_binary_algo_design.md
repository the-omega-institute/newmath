# ExternalBinary Algo Design

Target relation:

```text
ExternalBinary.append a b = r
```

Because `BEDC.FKernel.ExternalBinary` defines:

```text
BWord := BHist
Mbin  := BWord
append := BEDC.FKernel.Cont.append
```

the executable relation is the Cont append relation over three history
encodings:

```text
choices(r) = choices(b) ++ choices(a)
```

The input tape is:

```text
BHistEncoding(a) ++ BHistEncoding(b) ++ BHistEncoding(r)
```

## Required Unbounded Machine

A full cyclic-tag recognizer has to implement the same unbounded queue
operation needed by Cont:

1. Split exactly three BHist encodings at their `11` terminators.
2. Decode each history body, where `0` is constructor `e0` and `10` is
   constructor `e1`.
3. Store the decoded choices of `b`, then the decoded choices of `a`.
4. Compare that stored sequence against the decoded choices of `r`.
5. Reject malformed encodings, trailing input, short result streams, long
   result streams, and any bit mismatch.

This is not a new ExternalBinary-specific algorithmic problem. The Lean module
is a definitional reuse of Cont, so the missing unbounded recognizer is exactly
the unbounded Cont queue-copy/compare recognizer described in
`docs/cont_algo_design.md`.

## Bounded Program

`manifests/external_binary/external_binary_basic.algo.ct` uses the same bounded
positional-certificate program as the Cont manifest. It covers all listed
ExternalBinary fixtures and the depth `<= 2` sweep in
`tests/test_external_binary.c`.

For each input position `i`, production `P_i` is:

```text
P_i = 1 ++ binary5(i)
```

The harness runs the program for exactly the input length. At that boundary,
the consumed input prefix has appended one certificate block for every one-bit
position, so the remaining tape is:

```text
concat(P_i for every input position i containing bit 1)
```

For fixed input length below 32, this certificate records every one-bit
position. The C harness then independently decodes the same tape as an
ExternalBinary append triple and checks:

```text
choices(r) = choices(b) ++ choices(a)
```

The result is a real bounded CT computation plus a semantic decoder
cross-check. It is not an unbounded ExternalBinary decider.

## Representative Traces

For `append Empty Empty = Empty`, the input is:

```text
111111
```

The one bits are at positions `0,1,2,3,4,5`, so the bounded CT tape after six
steps is:

```text
100000100001100010100011100100100101
```

For `append (e0 Empty) (e1 Empty) = e1 (e0 Empty)`, the input is:

```text
011101110011
```

The one bits are at positions `1,2,3,5,6,7,10,11`, so the bounded CT tape after
twelve steps is:

```text
100001100010100011100101100110100111101010101011
```

For the rejected claim `append Empty Empty = e0 Empty`, the input is:

```text
1111011
```

The CT tape still has a deterministic certificate:

```text
100000100001100010100011100101100110
```

The decoder-side ExternalBinary check rejects the triple because the decoded
result has one constructor choice while both inputs are empty.
