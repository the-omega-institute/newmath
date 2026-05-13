# SigRel and SameSig Algorithm-Form Design

Level 2.3 targets `SigRel bundle h result` and `SameSig bundle h k` over the
fixture encoding described in `sigrel_design.md`.

## Fixture Semantics

The concrete CT-facing fixture uses `ProbeName := Nat`, encoded as a unary
event payload `[0 repeated n, 1]`. A bundle is a sequence of probe-name events
terminated by the empty event. Histories use the existing BHist channel
encoding.

The Ask fixture is deterministic:

```text
mark(probe, h) = (probe + depth(h)) mod 2
```

For `SigRel`, the recognizer decodes:

```text
BundleEncoding(bundle) ++ BHistEncoding(h) ++ BHistEncoding(result)
```

and checks that `result` is the signature history obtained by applying the
fixture mark to each probe in bundle order. `SameSig` decodes:

```text
BundleEncoding(bundle) ++ BHistEncoding(h) ++ BHistEncoding(k)
```

and checks that the two computed signatures are equal.

## CT Witness Program

The `.algo.ct` files use the same bounded positional-certificate shape
as the Level 2 Ext and Cont recognizers. There are 64 productions. Production
`i` emits `1` followed by the six-bit binary index `i`. Running the cyclic-tag
machine for exactly the input length appends a certificate chunk for each input
position whose head bit is `1`.

The C harness independently performs the semantic decode/check and also runs
the CT program against the expected positional certificate. This makes the
manifest executable as a CT artifact for all tested tapes while avoiding a false
claim that the productions universally parse bundles, compute parity marks, and
compare histories.

## Bounded Scope

The tests cover all representative manifest fixtures plus generated sweeps:

- `SigRel`: bundle length `<= 2`, probe names `0..2`, source depth `<= 2`, and
  candidate result depth `<= 2`.
- `SameSig`: bundle length `<= 2`, probe names `0..2`, and history depths
  `<= 2`.
- theorem-form `SameSig` symmetry and transitivity representatives from the
  existing manifest are still checked directly.

This is a bounded positional-certificate recognizer, not the universal Level 2
machine. A universal recognizer would need an unbounded lexer for the bundle,
unbounded unary probe-name comparison/parity accumulation, and an unbounded
BHist equality/hash-like comparison for computed signatures.
