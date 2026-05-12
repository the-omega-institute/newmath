# Ask Design

Target source: `lean4/BEDC/FKernel/Ask.lean`.

`AskSetup` is a Lean typeclass:

```text
class AskSetup where
  ProbeName : Type
  Evidence : Type
  Ask : ProbeName -> BHist -> BMark -> Evidence -> Prop
```

The rule110 manifests cannot encode an arbitrary typeclass parameter. They
therefore instantiate a small concrete fixture that mirrors the SigRel test
policy already used in `manifests/sig/`.

## Ground Fixture

The manifest fixture chooses:

```text
ProbeName := Nat
Evidence := one-bit event payload
```

Probe names are unary naturals:

```text
ProbeName(n) payload = [0 repeated n, 1]
ProbeNameEncoding(n) = EventEncoding(ProbeName(n))
```

Histories use `BHistEncoding` from `bhist_encoding.md`. Marks and evidence use
one-bit events:

```text
b0 = EventEncoding([0]) = "011"
b1 = EventEncoding([1]) = "1011"
```

The executable relation is deterministic:

```text
expected = (probe_name + depth(history)) mod 2
Ask probe history mark evidence
  iff mark = expected and evidence = expected
```

This fixture gives every decoded `(probe, history)` exactly one mark/evidence
witness. It supports representative checks for `AskEvent`, `AskPolicy`
totality, determinacy, and history-respecting behavior without changing the
abstract Lean interface.

## Input Contract

`ask_basic` cases use exactly four events:

```text
ProbeNameEncoding(probe)
+ BHistEncoding(history)
+ EventEncoding(mark)
+ EventEncoding(evidence)
```

The decoder rejects:

- probe events that are not unary naturals ending in one `1`;
- mark events that are not exactly one bit;
- evidence events that are not exactly one bit;
- streams with missing or trailing input.

Once decoded, the semantic harness computes the expected parity mark and
compares both mark and evidence to it.

## Relation to SigRel

`SigRel` consumes an abstract `Ask pi h m delta`. The existing SigRel fixture
uses the same parity mark rule:

```text
mark = (probe_name + depth(history)) mod 2
```

The Ask module makes that policy explicit at the relation boundary. SigRel then
uses only the mark part of the witness, while Ask checks that the witness also
carries a matching evidence token.

## Covered Lean Shape

The fixture aligns with the main shapes in `Ask.lean`:

- an `AskEvent` corresponds to the decoded positive quadruple plus its
  semantic check;
- `askEvent_witness` and `AskEvent_iff_exists` correspond to the concrete
  mark/evidence pair produced by the parity rule;
- determinacy corresponds to the uniqueness of the parity mark for a fixed
  probe and history;
- `respectsHistory` is reflected by dependence on history depth, which is
  stable for byte-equal representative histories in the current BHist fixture.

The manifests are examples of one concrete `AskSetup`; they do not claim that
all possible Lean `AskSetup` instances are executable by this fixture.
