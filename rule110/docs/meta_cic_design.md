# MetaCIC rule110 mirror

## Scope

This mirror covers the closed, finite surfaces that can be checked by the
current cyclic-tag manifest harness:

- `BHistSubstrate.bhistLen_natToBHist`
- `BHistSubstrate.bhistToTerm_closed`
- `BHistSubstrate.bhistPayloadToTerm_injective`
- `BHistSubstrate.bhistToTerm_injective`
- `AtomInfer.inferAtom_sort_sound`
- `AtomInfer.inferAtom_var_sound`

The manifests are representative enum manifests.  They do not implement a
general Calculus of Inductive Constructions typechecker, beta reducer,
normalizer, or universe hierarchy on cyclic-tag productions.  The executable
checks decode the assertion inputs and verify the same finite closed cases
against a C mirror of the Lean definitions.

## BHistSubstrate encoding

`BHistSubstrate` already uses `BHist` as the substrate carrier:

```text
Empty | e0 BHist | e1 BHist
```

The rule110 side reuses the existing `BHistEncoding`:

```text
BHistEncoding(h) = EventEncoding(choices(h))
```

where `choices` records the outer constructors as bytes:

```text
Empty        -> []
e0 h         -> 0 :: choices(h)
e1 h         -> 1 :: choices(h)
```

The `natToBHist` surface is represented by histories whose choice payload is
all zero bytes.  The length theorem is checked by decoding a single BHist,
requiring every choice to be `0`, and comparing the depth to the expected
natural number carried by the manifest case.

The MetaCIC term embedding is not serialized as a separate term stream.  The
test reconstructs the Lean-side shape directly from the decoded BHist:

```text
payload(Empty) = var 2
payload(e0 h)  = app (var 1) (lam sort (lam sort (lam sort (payload h))))
payload(e1 h)  = app (var 0) (lam sort (lam sort (lam sort (payload h))))
term(h)        = lam sort (lam sort (lam sort (payload h)))
```

For closure, the checker evaluates `ClosedAt` structurally on that generated
shape.  For injectivity, the checker compares the generated payload or full
term shapes for two decoded histories and verifies that term equality implies
history equality on the enumerated cases.

## AtomInfer encoding

Atom-level inference uses a compact two-event flow:

```text
input = CtxEncoding ++ AtomEncoding
```

Contexts are restricted to sort-only entries:

```text
CtxEncoding([sort, ..., sort]) = EventEncoding([0, ..., 0])
```

Atoms use these payloads:

```text
sort      = EventEncoding([0])
var i     = EventEncoding([1, 0 repeated i])
non-atom  = any other payload used as a negative fixture
```

The checker mirrors:

```text
inferAtom Gamma sort    = some sort
inferAtom Gamma (var i) = Gamma.lookup i
inferAtom Gamma _       = none
```

Because the context fixtures contain only `sort`, lookup shifting is inert in
these cases.  The var cases are therefore concrete instances of
`inferAtom_var_sound` with `A = sort`.

## Manifest files

`manifests/meta_cic/bhist_nat_len.enum.ct`

: Finite cases for `natToBHist` and `bhistLen`.

`manifests/meta_cic/bhist_term_embedding.enum.ct`

: Finite closure and injectivity cases for the BHist-to-Term embedding.

`manifests/meta_cic/atom_infer.enum.ct`

: Finite sort and variable inference cases, plus out-of-scope and non-atom
negative fixtures.

All three are `PRODUCTIONS 0` enum manifests.  Their semantic content is in the
assertion table and in `tests/test_meta_cic.c`; the cyclic-tag runner smoke
test verifies that they still pass through the manifest parser and evaluator
pipeline.

## Boundary

The current mirror is a bounded substrate check over closed encodings and
atom-level inference.  A full MetaCIC mirror would need cyclic-tag encodings
for recursive term parsing, binder-aware substitution, beta reduction,
contextual typing, normalization bounds, and proof-relevant derivations.  Those
surfaces are not present in these enum manifests.
