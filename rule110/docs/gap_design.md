# Gap Design

Target: encode the executable shape of `BEDC.FKernel.Gap`.
Primary sources: `lean4/BEDC/FKernel/Gap/Core.lean`,
`Gap/InGapSig.lean`, `Gap/Comp.lean`, and `Gap/Policy.lean`.

## Lean Shape

`Core.lean` defines the local domain interface and the signature gap relation:

```text
class DomainSetup where
  Domain : Type
  InDom : Domain -> BHist -> Prop

def InGapSig bundle D p h : Prop :=
  InDom D h /\ exists s, SigRel bundle h s /\ TokIntro bundle s p
```

`Comp.lean` gives the composition gap as an explicit middle witness:

```text
def CompGap firstGap secondGap z x : Prop :=
  exists y, firstGap y x /\ secondGap z y
```

`Policy.lean` packages coverage, generation, and separation fields over the
same `InGapSig` predicate. The CT encoding here focuses on the two executable
membership shapes: domain-plus-signature membership and composition by witness.

## Ground Fixtures

The Lean interfaces are abstract, so the manifest uses concrete fixtures for
representative execution:

```text
Domain := Nat
InDom D h := depth(h) <= D
Pkg := BHist
TokIntro bundle s p := hsame s p
```

`Pkg := BHist` mirrors `SignaturePackageSetup` in
`Package/Minimal.lean`, where a package token is introduced exactly when it is
the same history as the generated signature.

The `SigRel` part reuses the `sig` fixture:

```text
ProbeName(n) payload = [0 repeated n, 1]
BundleEncoding(Bnil) = empty event "11"
BundleEncoding(Bcons p tail) = ProbeNameEncoding(p) ++ BundleEncoding(tail)
Ask(n, h) = parity(n + depth(h))
```

With this fixture, `SigRel bundle h s` is decidable by computing the bundle
signature from `h` and comparing it with `s`.

## Encodings

A leading tag selects the predicate:

```text
tag(0) = event([0])
tag(1) = event([1])
```

`InGapSig` input:

```text
tag(0) ++ DomainEncoding(D) ++ BundleEncoding(bundle) ++
BHistEncoding(h) ++ BHistEncoding(s) ++ PkgEncoding(p)
```

`DomainEncoding(D)` uses the same unary event shape as probe names:
payload `[0 repeated D, 1]`. `PkgEncoding(p)` is a BHist event because the
fixture package carrier is `BHist`.

The checker accepts exactly when:

1. The tag is `0`.
2. The domain, bundle, history, witness signature, and package decode.
3. No trailing input remains.
4. `depth(h) <= D`.
5. The computed fixture signature equals witness `s`.
6. The package history `p` equals `s`.

`CompGap` input:

```text
tag(1) ++ BHistEncoding(source) ++ BHistEncoding(inter) ++
BHistEncoding(final) ++ event([first_holds, second_holds])
```

The three histories are decoded to keep the witness ledger explicit. The last
event carries the truth values for the two supplied relations at that witness.
The checker accepts exactly when both bits are present and equal to `1`.

## Covered Cases

`manifests/gap/gap_basic.enum.ct` and `gap_basic.algo.ct` cover:

- Empty-domain empty-history membership.
- Singleton and two-probe signature memberships.
- Domain failure, wrong signature, wrong package, and trailing input.
- Composition witnesses with both relation bits true.
- Composition failures where either relation bit is false or malformed.

The `.algo.ct` file uses a vacuous cyclic-tag production under the current
manifest-runner boundary. The executable semantics live in `tests/test_gap.c`,
matching the established Ext, Cont, and SigRel test pattern.

## Lean Theorem Alignment

The test harness exercises the computational content behind these theorem
families:

- `InGapSig` definition and witness iff wrappers.
- `inGapSig_intro`, domain projection, and signature/token witness extraction.
- `PolicySupportedSignatureGap` and `GapMembership` definitional wrappers.
- `CompGap` iff, intro, inversion, left/right witness projections, and ledger
  composition principle at the explicit-witness level.
- `GapPolicy` generation and coverage fields when read as executable witness
  obligations over the concrete fixtures above.
