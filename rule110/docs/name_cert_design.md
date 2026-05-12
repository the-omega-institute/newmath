# NameCert Design

Target: encode the executable boundary of `BEDC.FKernel.NameCert`.
Primary sources: `lean4/BEDC/FKernel/NameCert.lean`,
`NameCert/Descent.lean`, and `NameCert/StabilityMode.lean`.

## Lean Shape

`NameCert` packages an inhabited carrier, equivalence fields, and transport of
carrier membership across the equivalence:

```text
NameCert Carrier Equiv :=
  exists h, Carrier h
  refl/symm/trans for Equiv
  Equiv h k -> Carrier h -> Carrier k
```

`SemanticNameCert` extends that core with pattern and ledger soundness from the
source carrier. The theorem family transports those two facts along classifier
chains, confluence shapes, and reverse chains.

The descent side packages a function-like map with a respectfulness proof:

```text
DescentCertificate Source Target sourceSame targetSame
StableTransformation Source Target Ledger sourceSame targetSame
```

`StableTransformation` also carries `Nonempty Ledger`, and its composition
theorem combines two ledgers as a product.

`StabilityMode` is a closed five-constructor type:

```text
closure | reuse | descent | composition | seal
```

## Ground Fixture

The Lean module is abstract over Prop-valued predicates. The rule110 fixture
uses a small decidable instance:

```text
Carrier_bound(h) := depth(h) <= bound
Equiv(h,k) := depth(h) = depth(k)
PatternSpec := Carrier_bound
LedgerPolicy := Carrier_bound
ClassifierSpec := Equiv
StableTransformation.map := identity on BHist
sourceSame and targetSame := Equiv
```

This instance gives an inhabited carrier because `Empty` has depth `0`. Depth
equality is reflexive, symmetric, and transitive, and carrier membership
transports across it. Pattern and ledger soundness are identity projections
from the same carrier predicate.

## Encodings

Every input starts with a unary tag event:

```text
tag(n) = EventEncoding([0 repeated n, 1])
```

`tag(0)` checks the core certificate fields:

```text
tag(0) ++ BoundEncoding(bound) ++ BHistEncoding(h) ++
BHistEncoding(k) ++ BHistEncoding(r) ++ event([hk, kr, sourceH])
```

The relation bits must match the decoded fixture facts. The checker then
evaluates the representative refl, symm, trans, and carrier-transport
obligations.

`tag(1)` checks semantic transport:

```text
tag(1) ++ BoundEncoding(bound) ++ BHistEncoding(h) ++
BHistEncoding(k) ++ BHistEncoding(r) ++ event([hk, kr, sourceH])
```

The same decoded facts are interpreted as classifier edges and a source fact.
The checker evaluates direct pattern/ledger soundness, one-step transport, and
two-step chain transport.

`tag(2)` checks seal-interface witnesses:

```text
tag(2) ++ ThreadEncoding(thread) ++ BoundEncoding(bound)
```

The thread is a unary natural event. The certificate witness is the bound-based
NameCert instance.

`tag(3)` checks stable transformation descent:

```text
tag(3) ++ BHistEncoding(source) ++ BHistEncoding(target) ++ event([same, ledger])
```

The identity map respects depth equality whenever the `same` bit is true, and
the ledger bit must be present.

`tag(4)` checks composition:

```text
tag(4) ++ BHistEncoding(source) ++ BHistEncoding(target) ++
event([sourceSame, leftLedger, rightLedger])
```

The composed identity map respects the same relation and requires both ledger
witness bits.

`tag(5)` checks stability-mode distinction:

```text
tag(5) ++ ModeEncoding(left) ++ ModeEncoding(right)
```

Modes `0..4` correspond to `closure`, `reuse`, `descent`, `composition`, and
`seal`. The representative no-confusion predicate accepts valid distinct
modes and rejects equal or out-of-range modes.

## Covered Cases

`name_cert_basic.enum.ct` and `name_cert_basic.algo.ct` cover:

- Core certificate witnesses, depth-one equivalence chains, vacuous transport,
  wrong equivalence bits, and wrong source bits.
- Semantic direct transport, two-step classifier transport, vacuous source
  cases, wrong classifier bits, and wrong source bits.
- Seal interface thread and certificate witnesses, plus malformed or trailing
  streams.
- Stable transformation descent for equal depths, vacuous non-equal histories,
  wrong relation bits, and missing ledger witnesses.
- Stable transformation composition with both ledgers, vacuous non-equal
  histories, wrong relation bits, and missing right ledger witnesses.
- Stability-mode no-confusion representatives and invalid mode rejection.

The `.algo.ct` production is inert under the manifest-runner boundary. The
semantic checks live in `tests/test_name_cert.c`, matching the existing Gap and
SigRel fixture pattern.

## Lean Theorem Alignment

The harness exercises the computational content behind these theorem families:

- `NameCert_iff_semantic_fields`, `nameCert_carrier_witness`,
  `nameCert_equiv_refl`, `nameCert_equiv_trans`,
  `nameCert_carrier_transport`, and
  `derived_interfaces_require_certificates`.
- `NameCert_carrier_self_semantic_lifting`,
  `semanticNameCert_ledger_policy_witness`,
  `semanticNameCert_pattern_ledger_transport`, and
  `semanticNameCert_classifier_chain_transport`.
- `SealInterface` thread and certificate witness projections.
- `descentCertificate_respects`,
  `StableTransformation_descentCertificate_exists`,
  `stableTransformation_descends_to_packages`,
  `function_like_interfaces_are_derived`, and the composition theorem in
  `NameCert/Descent.lean`.
- `stabilityMode_no_confusion`,
  `stabilityMode_pairwise_no_confusion`,
  `stabilityMode_descent_composition_seal_no_confusion`, and
  `stabilityMode_exhaustive`.
