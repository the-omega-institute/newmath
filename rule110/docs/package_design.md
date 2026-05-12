# Package Design

Primary sources:

- `lean4/BEDC/FKernel/Package/Core.lean`
- `lean4/BEDC/FKernel/Package/Policy.lean`
- `lean4/BEDC/FKernel/Package/TokenPolicy.lean`
- `lean4/BEDC/FKernel/Package/TokenPolicy/Classify.lean`
- `lean4/BEDC/FKernel/Package/Minimal.lean`

## Lean Shape

`PackageSetup` is parameterized by `AskSetup`:

```text
class PackageSetup [AskSetup] where
  Pkg : Type
  TokIntro : ProbeBundle ProbeName -> BHist -> Pkg -> Prop
```

`psame bundle p q` is generated from two token introductions and an `hsame`
witness between their source histories:

```text
TokIntro bundle s p -> TokIntro bundle t q -> hsame s t -> psame bundle p q
```

`PackageTokenPolicy` packages two directions over introduced tokens:

```text
hsame s t -> psame bundle p q
psame bundle p q -> hsame s t
```

The token-policy files derive reflexive, symmetric, and transitive package
sameness on introduced tokens from those two directions.

## Ground Fixture

The rule110 fixture uses the concrete package instance from
`Package/Minimal.lean`:

```text
Pkg := BHist
TokIntro bundle s p := hsame s p
```

At the C harness level, `hsame` is byte equality of decoded BHist payloads. The
bundle parameter is still decoded and checked using the established
`ProbeBundle` event-list format, but this particular fixture does not inspect
the bundle contents when deciding token introduction.

Probe names use the existing unary natural event payload:

```text
ProbeName(n) payload = [0 repeated n, 1]
```

Bundles are terminated by the reserved event payload `[1,1]`.

## Encodings

A leading unary tag selects the Package predicate family:

```text
tag(0) = event([1])
tag(1) = event([0,1])
tag(2) = event([0,0,1])
tag(3) = event([0,0,0,1])
```

Token input:

```text
tag(0) ++ BundleEncoding(bundle) ++ BHistEncoding(s) ++ PkgEncoding(p)
```

`psame` input:

```text
tag(1) ++ BundleEncoding(bundle) ++ BHistEncoding(s) ++ BHistEncoding(t) ++
PkgEncoding(p) ++ PkgEncoding(q)
```

The checker accepts exactly when both tokens are introduced and the two source
histories are equal.

Token-policy classification input:

```text
tag(2) ++ BundleEncoding(bundle) ++ BHistEncoding(s) ++ BHistEncoding(t) ++
PkgEncoding(p) ++ PkgEncoding(q) ++ event([claimed_psame, claimed_hsame])
```

The checker recomputes the two fixture truth values and accepts exactly when
both claim bits match. If either token is not introduced, both policy
directions are outside their Lean premise, so the tagged classification input
is rejected as a malformed introduced-token case.

Two-step chain input:

```text
tag(3) ++ BundleEncoding(bundle) ++ BHistEncoding(a) ++ BHistEncoding(b) ++
BHistEncoding(c) ++ PkgEncoding(p) ++ PkgEncoding(q) ++ PkgEncoding(r)
```

The checker accepts when all three tokens are introduced, `psame p q` holds,
`psame q r` holds, and therefore `psame p r` holds by equality of the three
source histories.

## Covered Cases

`package_basic.enum.ct` and `package_basic.algo.ct` cover:

- token introduction for empty and non-empty bundle representatives;
- token rejection for wrong package payloads, malformed bundles, and trailing
  input;
- `psame` reflexivity, symmetry representatives, and negative cases for
  distinct histories or non-introduced packages;
- token-policy classification where both directions are true and where both
  are false;
- classification rejection for incorrect claim bits and non-introduced tokens;
- two-step transitivity and a broken chain.

The `.algo.ct` file uses a vacuous cyclic-tag production under the current
manifest-runner boundary. Executable semantics live in `tests/test_package.c`,
matching the established Ask, SigRel, Bundle, and Gap pattern.
