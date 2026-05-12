# Bundle CT Algorithm Design

## Encoding

Bundle inputs use the event-list encoding from `bundle_design.md`:

```text
ProbeName(n) payload = [0 repeated n, 1]
ProbeNameEncoding(n) = EventEncoding(ProbeName(n))
BundleEncoding(Bnil) = EventEncoding([1,1])
BundleEncoding(Bcons p tail) = ProbeNameEncoding(p) ++ BundleEncoding(tail)
```

The length manifest receives two encoded bundles. The membership manifest
receives one encoded probe followed by the encoded bundles named by each
assertion.

## CT Program

Both Bundle algorithm manifests use the same bounded positional-certificate
cyclic-tag system.

```text
P_i = 1 ++ binary7(i)        for 0 <= i < 128
```

The runner executes the system for exactly `input_length` steps. During those
steps the original input prefix is consumed once. Whenever the consumed bit is
`1`, the production selected by the cyclic program counter is appended to the
tape. Since the program counter advances once per consumed bit, the remaining
tape is:

```text
concat(P_i for each input position i whose bit is 1)
```

This certificate depends on the cyclic-tag execution, not on the decoder. The
C tests compare the exact certificate through `mr_run_ct_manifest`, and then
check the decoded ProbeBundle semantics directly.

## Step Trace

For input `101011`, the first six productions are:

```text
P_0 = 10000000
P_1 = 10000001
P_2 = 10000010
P_3 = 10000011
P_4 = 10000100
P_5 = 10000101
```

Running for six steps gives:

```text
step 0: read 1, append P_0
step 1: read 0, append nothing
step 2: read 1, append P_2
step 3: read 0, append nothing
step 4: read 1, append P_4
step 5: read 1, append P_5
```

The final tape is:

```text
10000000100000101000010010000101
```

For length assertions, this certificate covers the concrete bitstream whose
decoded shape witnesses append-length arithmetic. For membership assertions,
it covers the concrete bitstream whose decoded shape witnesses membership
distribution over append.

## Scope

The manifest runner exposes only a production list, an initial tape, and a step
limit. It does not expose a macro layer, extra work tapes, or a parser state.
Within the file whitelist, a complete universal recognizer for arbitrary
ProbeBundle streams is therefore not installed here.

The shipped scope is bounded to inputs of length at most 128 bits. This bound
covers all Bundle fixtures in `tests/test_bundle.c`; the largest current input
is 66 bits. A universal recognizer needs an unbounded parser and a reusable
equality routine for unary probe names before it can decide membership for all
input lengths.
