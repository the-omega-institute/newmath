# Package CT Algorithm Design

## Target

The Package fixture uses the concrete instance described in `package_design.md`:

```text
Pkg := BHist
TokIntro bundle s p := hsame s p
```

The tagged input families are:

```text
tag(0): token introduction
tag(1): psame over two introduced tokens
tag(2): TokenPolicy classification over introduced tokens
tag(3): two-step psame chain
```

For this fixture, `psame bundle p q` holds exactly when there are source
histories `s` and `t` such that `s = p`, `t = q`, and `hsame s t`. The bundle is
parsed to keep the public encoding contract, but this minimal package instance
does not inspect bundle contents.

## Required Unbounded Machine

A universal cyclic-tag recognizer would need to:

1. Decode the leading unary tag and reject unknown tags.
2. Decode an unbounded terminated bundle stream.
3. Decode two to six `BHist` event streams depending on the tag.
4. Compare arbitrary decoded histories for `TokIntro := hsame`.
5. Reuse that equality result to decide `psame`, TokenPolicy claim agreement,
   or two-step transitivity.
6. Reject malformed encodings and any trailing input.

The obstruction is the same unbounded equality problem as the BHist `hsame`
recognizer: the CT program must retain and compare arbitrary event payloads
while still tracking parser state and tag-specific arity. The current manifest
runner exposes only a production list, an initial tape, and a step bound. It has
no macro layer, parser work tape, or native accept marker beyond exact final
tape comparison supplied by the C harness.

## Bounded Program

`manifests/package/package_basic.algo.ct` uses a bounded positional-certificate
program for inputs of length at most 128 bits:

```text
P_i = 1 ++ binary7(i)        for 0 <= i < 128
```

The harness runs the CT program for exactly `input_length` steps. The consumed
prefix is the original input. Whenever a consumed bit is `1`, production `P_i`
for that input position is appended. The final tape is therefore:

```text
concat(P_i for each input position i whose bit is 1)
```

This tape is a real cyclic-tag artifact that identifies the checked bitstream
within the 128-bit bound. The C harness independently decodes the same stream
and checks the concrete Package predicate. The two observations are kept
separate:

```text
CT tape = positional certificate
decoder says Package predicate = expected yes/no
```

## Coverage

The manifest lists the 19 representative Package fixtures from
`package_basic.enum.ct`, each with its expected certificate. The test harness
also generates a bounded sweep over all histories of depth at most 2 for token
introduction, a representative psame grid, TokenPolicy classifications with
correct claim bits, and transitive and broken two-step chains.

This is not a universal Package recognizer. It is a bounded CT witness for the
current fixture set and small generated Package corpus. A universal recognizer
requires first solving or importing an unbounded `hsame` equality machine and
then composing it with the Package tag parser.
