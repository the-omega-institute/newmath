# P_eq_bhist Design

`P_eq_bhist` is the algorithm-form witness used by
`manifests/hist/hsame_refl.algo.ct`.

## Contract

Input is the concatenation of two BHist event encodings:

```text
EventEncoding(h1) ++ EventEncoding(h2)
```

The intended full contract is to accept exactly when the two decoded payloads
are bit-for-bit equal. The current file implements a bounded positive certifier
for the five representative reflexive inputs already used by
`hsame_refl.enum.ct`:

```text
1111
011011
10111011
0101101011
10010111001011
```

This is partial scope. It is not a decider for arbitrary BHist pairs, and it
does not provide a negative rejection path for unequal histories.

## Program

The cyclic tag program has 16 productions:

```text
P0  = 10000
P1  = 10001
P2  = 10010
P3  = 10011
P4  = 10100
P5  = 10101
P6  = 10110
P7  = 10111
P8  = 11000
P9  = 11001
P10 = 11010
P11 = 11011
P12 = 11100
P13 = 11101
P14 = 11110
P15 = 11111
```

At step `i`, the program consumes the current head bit and uses production
`P_i mod 16`. If the head bit is `1`, the production is appended to the tail.
If the head bit is `0`, no production is appended. For the representative
inputs, the test harness runs exactly `input_length` steps, so the initial
input has been consumed and the remaining tape is the certificate stream:

```text
concat(P_i for each input position i whose bit is 1)
```

Each production starts with `1`, so every accepted representative case leaves a
non-empty marker tape. The following four bits record the source position modulo
16. The largest representative input has length 14, so no modulo wrap occurs in
the tested scope.

## Trace Example

For `e0 Empty / e0 Empty`, the input is:

```text
011011
```

The one bits occur at positions 1, 2, 4, and 5. The program runs for six steps:

```text
step 0: head 0, P0 skipped
step 1: head 1, append P1  = 10001
step 2: head 1, append P2  = 10010
step 3: head 0, P3 skipped
step 4: head 1, append P4  = 10100
step 5: head 1, append P5  = 10101
```

The final marker tape is:

```text
10001100101010010101
```

The corresponding test calls:

```text
mr_run_ct_manifest("manifests/hist/hsame_refl.algo.ct",
                   "011011",
                   "10001100101010010101",
                   6)
```

## Boundary

The program proves that the manifest pipeline can run non-empty cyclic-tag
productions whose output depends on the BHist input. It does not yet implement
the unbounded comparison machinery needed for all BHist pairs:

- split the first and second events at the first `11` terminator;
- retain each first-payload choice until the corresponding second-payload
  choice is active;
- reject mismatched choices and unequal lengths;
- accept only when both event terminators arrive in the same comparison cycle.

The current runner can compare an exact final tape after a chosen fuel bound,
but it cannot directly express "halt with non-empty accept marker"; natural CTS
halt means the tape is empty. A full equality decider should therefore either
use a runner-level accept convention for bounded marker observation or encode
acceptance as empty halt after a separately audited positive trace.
