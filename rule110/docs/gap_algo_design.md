# Gap Algo Design

Target predicates:

```text
InGapSig bundle D p h :=
  InDom D h /\ exists s, SigRel bundle h s /\ TokIntro bundle s p

CompGap firstGap secondGap z x :=
  exists y, firstGap y x /\ secondGap z y
```

The fixture used by `gap_basic.algo.ct` is the same fixture described in
`gap_design.md`:

```text
Domain := Nat
InDom D h := depth(h) <= D
Pkg := BHist
TokIntro bundle s p := hsame s p
Ask(n, h) := parity(n + depth(h))
```

`InGapSig` inputs have this stream shape:

```text
tag(0) ++ DomainEncoding(D) ++ BundleEncoding(bundle) ++
BHistEncoding(h) ++ BHistEncoding(s) ++ PkgEncoding(p)
```

`CompGap` inputs carry the middle witness and two relation truth bits:

```text
tag(1) ++ BHistEncoding(source) ++ BHistEncoding(inter) ++
BHistEncoding(final) ++ event([first_holds, second_holds])
```

## Required Unbounded Machine

A complete cyclic-tag recognizer for `InGapSig` has to:

1. Split the tagged event stream exactly.
2. Decode a unary domain bound.
3. Decode an unbounded `ProbeBundle` until its terminator.
4. Decode three history-shaped events.
5. Compute the fixture signature from every probe name and the history depth.
6. Compare the computed signature with the witness signature.
7. Compare the witness signature with the package history.
8. Reject malformed tags, malformed events, trailing input, domain failures,
   signature mismatches, and package mismatches.

The central obstruction is the bundle/signature pass. The cyclic-tag tape must
retain an unbounded list of probe names, compute the parity response for each
name against the decoded history depth, and then compare that generated history
against two independent history encodings. That needs an unbounded parser plus
queue-copy/compare machinery of the same class described for Cont and Bundle.

`CompGap` is simpler once the witness is explicit: after the tag and three
history decodes, it only checks a two-bit relation event. A universal Gap
recognizer still has to share the same front-end parser and reject all malformed
or trailing streams.

## Bounded Program

`manifests/gap/gap_basic.algo.ct` uses a bounded positional-certificate
cyclic-tag program for inputs up to 128 bits.

For each position `i`, production `P_i` is:

```text
P_i = 1 ++ binary7(i)
```

The harness runs the program for exactly the input length. The original input
prefix is consumed once. Whenever the consumed bit is `1`, the production for
that input position is appended. The remaining tape is:

```text
concat(P_i for every input position i whose bit is 1)
```

The C harness independently decodes the same input and checks the executable
Gap fixture semantics. Each bounded case therefore has two observations:

```text
CT tape = positional certificate
decoder says Gap predicate = expected result
```

This is a real cyclic-tag computation over each covered bitstream. It is not an
unbounded Gap decision procedure.

## Covered Scope

The bounded certificate covers all assertions in `gap_basic.algo.ct` and the
depth `<= 2` sweep in `tests/test_gap.c`:

- Four small bundles: empty, singleton probe `0`, singleton probe `1`, and
  two-probe bundle `[1, 2]`.
- Domain bounds `0..2`.
- Histories, witness signatures, and package histories of depth `<= 2`.
- Explicit `CompGap` witnesses of depth `<= 2` with all four relation-bit
  combinations.

The largest generated input is below the 128-bit production bound.
