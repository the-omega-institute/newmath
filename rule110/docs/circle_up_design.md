# CircleUp Design

Primary sources:

- `lean4/BEDC/Derived/ModNUp.lean`
- `lean4/BEDC/Derived/S1Up.lean`
- `lean4/BEDC/Derived/S1Up/CarrierExactness.lean`
- `lean4/BEDC/Derived/S1Up/PublicConstructor.lean`
- `lean4/BEDC/Derived/S1Up/StandardTopologicalCircleAcceptance.lean`

`CircleUp` is the roadmap name for the derived material currently split across
`ModNUp` and `S1Up`.  The rule110 mirror uses finite GroundCompiler rows over
decoded `BHist` events.  It does not claim a native cyclic-tag recognizer for
continuous maps or for the full topological-circle acceptance theorem.

## Event Encoding

The manifests reuse the existing `BHist` event encoding:

```text
Empty           = 11
e0 Empty        = 011
e1 Empty        = 1011
e1(e1 Empty)    = 101011
```

Each assertion input is a concatenation of exact `BHist` events.  The C harness
decodes the events with `gc_bhist_decode` and checks the finite row semantics.

## ModN Rows

`circle_modn_rows.enum.ct` mirrors ground instances of:

- `ModNQuotientClassifier_concrete_rows`
- `ModNQuotient_concrete_namecert_scope`

Input shape:

```text
BHist modulus ++ BHist h ++ BHist k ++ BHist witness
```

The harness checks that `modulus` is unary and that the row tag is one of:

```text
refl
symm
trans
carrier_respects_equiv
```

`ModNQuotientCarrier modulus h` is represented by a unary modulus together with
the singleton ring carrier `hsame h Empty`.  Thus the non-vacuous rows are over
`h = Empty`, while representative non-carrier inputs are treated as implication
vacuous ground instances.

## ModN Operations

`circle_modn_operations.enum.ct` mirrors ground instances of:

- `ModNQuotientCarrier_singleton_operation_descent_rows`
- `ModNQuotient_singleton_operation_descent_rows`
- `ModNQuotient_singleton_add_neg_empty_classifier`

Input shape:

```text
BHist modulus ++ BHist h ++ BHist k ++ BHist expectedAdd ++ BHist expectedMul
```

The Lean singleton operations are closed-form:

```text
RingSingletonAdd _ _ = Empty
RingSingletonMul _ _ = Empty
RingSingletonNeg _   = Empty
```

The harness checks that decoded add and multiply results are `Empty` and match
the expected result events.  For rows whose `h` or `k` is outside the singleton
carrier, the carrier premises are false and the implication is recorded as
vacuous.

## S1 Rows

`circle_s1_rows.enum.ct` mirrors the discrete readback surface of:

- `SOneHistoryCarrier_e1_components_carrier_exactness`
- `SOneHistoryCarrier_public_constructor_scope`
- `SOneStandardTopologicalCircleAcceptance_factorization_public_rows`

Input shape:

```text
BHist x ++ BHist y ++ BHist equation ++ BHist point ++ BHist pointTail
```

The accepted rows are representative e1-component cases:

```text
x        = e1 dx
y        = e1 dy
equation = SOneUnitHistory = e1(e1 Empty)
point    = e1 pointTail
pointTail = append x dy
```

Here `append` is the Lean `BEDC.FKernel.Cont.append` operation.  In the
constructor-choice list used by the C decoder, `append x dy` is the choices of
`dy` followed by the choices of `x`, because `append` recurses over the right
argument.  These rows cover the closed BHist shape and continuation readback
only; they deliberately stop before asserting the full continuous topological
acceptance boundary.

## Cross-Check Extension

A Lean cross-checker can register a `circle_up` family with these target keys:

```text
modn_classifier_concrete_rows
modn_singleton_operation_descent
modn_add_neg_empty_classifier
s1_e1_components_carrier_exactness
s1_public_constructor_scope
s1_topological_acceptance_shape
```

The manifests are representative finite ground instances of universal Lean
theorems.  Strict unbounded cyclic-tag recognizers and Lean-side registration
are outside this row.

## Assertion Keys

The assertion key set is:

```text
theorem=<target-key>
row=<row-name>
modulus=<hist-name>
h=<hist-name>
k=<hist-name>
expected_add=<hist-name>
expected_mul=<hist-name>
x=<hist-name>
y=<hist-name>
equation=<hist-name>
point=<hist-name>
point_tail=<hist-name>
carrier_premise=<true|false>
classifier_premise=<true|false>
conclusion_holds=yes
```
