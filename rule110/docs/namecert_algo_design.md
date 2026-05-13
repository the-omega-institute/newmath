# NameCert Algo Design

Target family:

```text
NameCert Carrier Equiv
SemanticNameCert SourceSpec PatternSpec LedgerPolicy ClassifierSpec
SealInterface Thread Carrier Equiv
DescentCertificate Source Target sourceSame targetSame
StableTransformation Source Target Ledger sourceSame targetSame
StabilityMode
```

## Fixture Contract

The algorithm manifest uses the concrete fixture described in
`docs/name_cert_design.md`:

```text
Carrier_bound(h) := depth(h) <= bound
Equiv(h,k) := depth(h) = depth(k)
PatternSpec := Carrier_bound
LedgerPolicy := Carrier_bound
ClassifierSpec := Equiv
StableTransformation.map := identity on BHist
sourceSame and targetSame := Equiv
```

Inputs are tagged GroundCompiler event streams. Tags `0..5` select core
certificate fields, semantic transport, seal witnesses, stable transformation
descent, stable transformation composition, and stability-mode distinction.

## Universal Obstruction

A universal cyclic-tag recognizer for the Lean `NameCert` interface is not a
single closed first-order language recognizer. The Lean structure is
parameterized by arbitrary Prop-valued predicates:

```text
Carrier : BHist -> Prop
Equiv : BHist -> BHist -> Prop
SourceSpec PatternSpec LedgerPolicy : BHist -> Prop
ClassifierSpec : BHist -> BHist -> Prop
sourceSame targetSame : Source/Target relations
```

Without an encoded decision procedure for those predicates, the CT substrate has
no executable data to inspect. Even after choosing the bounded-depth fixture,
the full unbounded recognizer would still need a GroundCompiler lexer, unary
natural decoder, BHist decoder, exact trailing-input rejection, depth equality,
carrier-bound comparison, relation-bit consistency checks, ledger-bit checks,
and a stable accept/reject convention in the manifest runner.

The present manifest runner observes a final tape after caller-supplied fuel.
It has no native rejected halt state distinct from nontermination and no
standard non-empty accept marker convention for arbitrary unbounded lexers.

## Bounded Program

`manifests/name_cert/name_cert_basic.algo.ct` therefore uses a bounded
positional-certificate program for the concrete fixture and small sweep in
`tests/test_name_cert.c`.

For each position `i`, production `P_i` is:

```text
P_i = 1 ++ binary6(i)
```

The test harness runs the CT program for exactly the input length. At that
point the consumed prefix has produced:

```text
concat(P_i for every input position i containing bit 1)
```

The 64 productions are injective for positions `0..63`. The representative
manifest inputs and the generated sweep all stay below that limit. The C test
checks two observations together:

```text
CT tape = positional certificate
decoder says NameCert fixture predicate = expected yes/no
```

This is an executable CT trace witness over the full input bit pattern, not a
universal NameCert decider.

## Sweep Scope

The bounded test sweep covers:

- core and semantic tagged inputs with bounds `0..3` and BHist depths `0..2`;
- seal witness inputs with threads `0..5` and bounds `0..3`;
- stable transformation descent inputs over depths `0..3`, both relation-bit
  values, and both ledger-bit values;
- composition inputs over depths `0..3`, both relation-bit values, and both
  ledger-bit values;
- stability-mode pairs in the range `0..6`, covering valid distinct modes,
  equal modes, and out-of-range modes.

The sweep is finite by design. Extending beyond 64 input positions requires
more productions or a different compiled recognizer strategy.
