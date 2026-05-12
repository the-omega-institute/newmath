# Cont Algo Design

Target relation:

```text
Cont h k r := choices(r) = choices(k) ++ choices(h)
```

Input tape:

```text
EventEncoding(h) ++ EventEncoding(k) ++ EventEncoding(r)
```

## Required Unbounded Machine

A full cyclic-tag recognizer has to perform these operations over an unbounded
stream:

1. Split exactly three event encodings at their `11` terminators.
2. Decode event bodies, where `0` represents constructor choice `0` and `10`
   represents constructor choice `1`.
3. Store the decoded choices of `k`, then the decoded choices of `h`.
4. Compare the decoded choices of `r` against that stored sequence.
5. Reject malformed encodings, extra trailing input, short `r`, long `r`, and
   any mismatched choice.

The hard part is the middle queue: the cyclic-tag tape must retain an
unbounded payload while also tracking which of the three events is active and
which half of the append comparison is being consumed. That is implementable by
a compiled tag-system program, but a hand-written manifest would need a
verified compiler or a much richer trace audit than this repository presently
has. The manifest runner also observes acceptance by comparing an exact tape
after a supplied fuel bound; natural cyclic-tag halt is the empty tape, so a
non-empty accept marker is not a native halt mode in the runner API.

## Bounded Program

`manifests/cont/cont_basic.algo.ct` therefore uses a bounded positional
certificate program over inputs up to 31 bits, which covers the listed Cont
cases and the depth `<= 2` sweep in `tests/test_cont.c`.

For each position `i`, production `P_i` is:

```text
P_i = 1 ++ binary5(i)
```

The test harness runs the CT program for exactly the input length. At that
point the input prefix has been consumed and the remaining tape is:

```text
concat(P_i for every input position i containing bit 1)
```

For fixed input length below 32, this certificate records every one-bit
position. The C test separately decodes the same input and checks the Cont
semantic predicate, so the bounded run has two independent observations:

```text
CT tape = positional certificate
decoder says Cont = expected yes/no
```

This is a bounded witness, not an unbounded Cont decider.

## Representative Traces

For `Cont Empty Empty Empty`, the input is:

```text
111111
```

The one bits are at positions `0,1,2,3,4,5`, so after six CT steps the tape is:

```text
100000100001100010100011100100100101
```

For `Cont (e0 Empty) (e1 Empty) (e1 (e0 Empty))`, the input is:

```text
011101110011
```

The one bits are at positions `1,2,3,5,6,7,10,11`, so after twelve CT steps the
tape is:

```text
100001100010100011100101100110100111101010101011
```

For the malformed Cont claim `Empty, Empty, e0 Empty`, the input is:

```text
1111011
```

The CT tape is still a well-defined positional certificate:

```text
100000100001100010100011100101100110
```

The decoder-side Cont check rejects that triple because `r` has one constructor
choice while `h` and `k` are empty.
