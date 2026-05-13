# ExternalBinary Design

Target: encode `BEDC.FKernel.ExternalBinary`.
Primary sources:

- `lean4/BEDC/FKernel/ExternalBinary.lean`
- `lean4/BEDC/FKernel/ExternalBinary/BitInversion.lean`
- `lean4/BEDC/FKernel/ExternalBinary/Cancellation.lean`
- `lean4/BEDC/FKernel/ExternalBinary/Congruence.lean`
- `lean4/BEDC/FKernel/ExternalBinary/Inversion.lean`
- `lean4/BEDC/FKernel/ExternalBinary/Model.lean`

## Lean Shape

The ExternalBinary module is a metamodel witness. It does not introduce a new
word carrier:

```text
abbrev BWord : Type := BHist
abbrev Mbin : Type := BWord
abbrev append : BWord -> BWord -> BWord := BEDC.FKernel.Cont.append
```

The executable content is therefore the same closed history datatype used by
`Hist` and `Cont`:

```text
Empty | e0 BWord | e1 BWord
```

The append recursion is inherited from `Cont`: recursion is on the second
argument, so with outermost-first constructor choices,

```text
choices(append a b) = choices(b) ++ choices(a)
```

## Encoding Strategy

ExternalBinary reuses the BHist event encoding directly:

```text
BWordEncoding(w) = BHistEncoding(w) = EventEncoding(choices(w))
MbinEncoding(w)  = BWordEncoding(w)
```

There is no wrapper tag for `BWord` or `Mbin`. The Lean aliases are definitional
reuse, and adding a separate runtime tag would encode structure that the Lean
module intentionally does not add.

The basic append manifest uses a concatenated triple:

```text
BWordEncoding(a) ++ BWordEncoding(b) ++ BWordEncoding(r)
```

The checker:

1. Decodes exactly three BHist events.
2. Rejects trailing input after the third event.
3. Computes `choices(b) ++ choices(a)`.
4. Accepts exactly when the computed choices equal `choices(r)`.

## Covered Theorem Families

`tests/test_external_binary.c` checks representative executable cases for:

- Model reuse: `BWord = BHist`, `Mbin = BHist`, and append reuse.
- Append unit laws and constructor rules.
- Length behavior through decoded choice-buffer lengths.
- Empty-result inversion.
- Bit-result inversion and cross-constructor impossibility.
- Right and left cancellation by comparing computed append results.
- Congruence under decoded word equality.

The `external_binary_basic.algo.ct` file uses a vacuous production, matching
the existing Ext and Cont pattern. Semantic checking lives in the C harness and
uses the shared GroundCompiler/BHist decoder.

## Representative Streams

Examples under the shared BHist encoding:

```text
Empty                         -> 11
e0 Empty                      -> 011
e1 Empty                      -> 1011
e0 (e1 Empty)                 -> 01011
e1 (e0 Empty)                 -> 10011
```

An append triple such as
`append (e0 Empty) (e1 Empty) = e1 (e0 Empty)` is encoded as:

```text
011 ++ 1011 ++ 10011 = 011101110011
```

This directly mirrors the Lean theorem surface: ExternalBinary is not a new
binary syntax beside the kernel history syntax; it is the same kernel history
syntax viewed as binary words.
