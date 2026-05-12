# Lean <-> rule110 Cross-Check Design

## Purpose

The rule110 manifests currently prove a local property: their bit strings can
be decoded by the rule110 test harness, and the decoded objects satisfy the
same fixture predicates that the C tests expect.

That is self-consistency, not cross-verification.

Self-consistency can miss a mismatch between a manifest name and the Lean
theorem it is meant to represent.  A file named `msame_refl.enum.ct` could
still contain a non-reflexive pair, or a `SigRel` fixture could drift away from
the Lean `AskSetup` surface.  The C tests would still be valuable, but they
would not close the Lean trust loop.

Level 4 adds a Lean-side checker:

```text
manifest assertion input
  -> Lean channel decoder
  -> typed BEDC values
  -> theorem-specific semantic checker
  -> PASS / FAIL for the assertion
```

The C evaluator continues to show that the manifest is executable by the
minimal substrate harness.  The Lean checker shows that each assertion is a
ground instance, complement case, or fixture instance of the intended Lean
surface.

## Scope

The first strict target is `*.enum.ct`.

Most `*.enum.ct` manifests have `PRODUCTIONS 0`.  Their meaningful content is
the assertion table, so the cross-check reads those assertions directly.

Most `*.algo.ct` manifests still have placeholder productions.  Level 4 should
parse and classify them, but the strict production-recognizer gate belongs to
Level 2.  The bounded `hist/hsame_refl.algo.ct` case can be treated separately
because it already carries a finite recognizer.

The checker is read-only: no Lean generation, no writes into `lean4/BEDC/`,
and no cyclic-tag recognizer synthesis.

## Manifest Parser Contract

The Lean executable only needs a small line parser:

```text
PRODUCTIONS <nat>
ASSERTIONS <nat>
case <name>: input=<bits> ; key=value ; key=value
```

It preserves manifest path, production count, declared assertion count, case
name, input bit string, and family-specific fields.  It rejects non-binary
input, missing metadata, count mismatch, duplicate cases, missing `input=`,
unknown paths, and unknown fields for the registered target.

## Shared Decoding

The checker should reuse:

```text
lean4/BEDC/GroundCompiler/ChannelEncoding.lean
DecEvent : List DisplayAlphabet -> Option (RawEvent x List DisplayAlphabet)
Decode   : List DisplayAlphabet -> Option EventFlow
```

Manifest bits map to display alphabet symbols:

```text
0 -> BMark.b0
1 -> BMark.b1
```

Typed parsers consume the stream using `DecEvent`:

```text
parseBMark     : Cursor -> Option (BMark x Cursor)
parseBHist     : Cursor -> Option (BHist x Cursor)
parseProbeName : Cursor -> Option (Nat x Cursor)
parseBundle    : Cursor -> Option (ProbeBundle Nat x Cursor)
parseBoolEvent : Cursor -> Option (Bool x Cursor)
parseTag       : Cursor -> Option (Nat x Cursor)
```

Payload conventions:

- `BMark`: raw event `[b0]` or `[b1]`.
- `BHist`: constructor choices, outermost first; `[]` is `Empty`,
  `b0 :: rest` is `e0 rest`, `b1 :: rest` is `e1 rest`.
- `ProbeName`: unary raw event `[b0 repeated n, b1]`.
- `ProbeBundle Nat`: `ProbeName` event list ending in sentinel `[b1,b1]`.
- Tags: unary natural-number events.
- Package, evidence, domain, and certificate payloads are interpreted by the
  fixture instance for their manifest family.

Every positive semantic case must consume the whole input.  Trailing-input
cases pass only when the spec says the case is a rejection check.

## Manifest Spec Shape

Each file gets a registered spec:

```text
ManifestSpec:
  path            : String
  productionKind  : enumOnly | algoCurrent | algoStrict
  defaultTarget   : Target
  assertionParser : fields -> AssertionKind
  inputParser     : AssertionKind -> bits -> TypedInput
  checker         : TypedInput -> Bool
```

`Target` should be a finite dispatch key, not arbitrary string-to-theorem
reflection.  Each target can use ordinary Lean definitions and Boolean checks.

Example: `check_msame m n := decide (m = n)`.

Parameterized modules use concrete fixture instances matching the manifest
comments; they do not change the abstract FKernel interfaces.

## Manifest Family Map

| Family | Input shape | Lean target |
|---|---|---|
| Mark / Hist | two or three mark/history events | sameness reflexivity, symmetry, transitivity, inversion, distinctness |
| Ext / Cont / ExternalBinary | triples of history-like values, plus mark for Ext | constructors, append equality, determinacy, complements |
| SigRel / SameSig / Ask | bundle/probe/history/signature payloads | parity-fixture `AskSetup`, `SigRel`, `SameSig` |
| Bundle / Unary | bundle/probe streams or unary history triples | membership, append, length, split, cancel, unary closure |
| Gap / Package | tagged fixture payloads | `InGapSig`, composition, `TokIntro`, `psame`, token policy |
| NameCert / Settled | tagged certificate or aggregate payloads | certificate projections, stability, descent, lower-family checks |

## Representative Schema: `msame_refl`

Manifest:

```text
rule110/manifests/mark/msame_refl.enum.ct
case b0_b0: input=011011  ; expected_reflexive=yes
case b1_b1: input=10111011; expected_reflexive=yes
```

Lean target:

```text
BEDC.FKernel.Mark.msame_refl : forall m : BMark, msame m m
```

Parser:

```text
input := BMarkEncoding(m1) ++ BMarkEncoding(m2)
decode exactly two events
parse both as BMark
require no remaining input
```

Checker:

```text
expected_reflexive=yes:
  require m1 = m2
  instantiate msame_refl m1
  compare the theorem conclusion with msame m1 m2
```

This catches a manifest that names a reflexive theorem but encodes `b0,b1`.

## Representative Schema: `hsame_refl`

Manifest:

```text
rule110/manifests/hist/hsame_refl.enum.ct
case empty:       input=1111
case e0_empty:    input=011011
case e1_empty:    input=10111011
case e0_e1_empty: input=0101101011
case e1_e0_e1:    input=10010111001011
```

Lean target:

```text
BEDC.FKernel.Hist.hsame_refl : forall h : BHist, hsame h h
```

Parser:

```text
input := BHistEncoding(h1) ++ BHistEncoding(h2)
decode exactly two history events
```

Checker:

```text
require h1 = h2
instantiate hsame_refl h1
compare the theorem conclusion with hsame h1 h2
```

`BHist` is infinite, so the manifest is representative.  Lean's theorem is
the universal proof; the manifest rows are checked as actual ground instances.

## Representative Schema: `ext_step`

Manifest:

```text
rule110/manifests/ext/ext_step.enum.ct
case empty_b0_e0_empty: input=11011011; ext_holds=yes
case empty_b0_empty:    input=1101111 ; ext_holds=no
```

Lean targets:

```text
Ext.e0 : Ext h b0 (e0 h)
Ext.e1 : Ext h b1 (e1 h)
ext_constructor_characterization
```

Parser:

```text
input := BHistEncoding(source) ++ BMarkEncoding(mark) ++ BHistEncoding(result)
decode source, mark, result
```

Checker:

```text
semanticExt(source, mark, result):
  mark = b0 -> result = e0 source
  mark = b1 -> result = e1 source

ext_holds=yes:
  require semanticExt = true
  construct by Ext.e0 or Ext.e1

ext_holds=no:
  require semanticExt = false
  use constructor characterization to justify Not (Ext source mark result)
```

Negative rows are important: they ensure the checker validates the relation,
not just the presence of a theorem name.

## Fixture Instances

The Level 4 executable should define one fixture namespace:

```text
namespace BEDC.Rule110CrossCheck.Fixture
```

Fixture choices:

- `ProbeName := Nat`.
- `Evidence` is the event payload type needed by the family, normally a small
  BHist-compatible wrapper.
- `Ask n h m evidence` holds when `m` is the parity of `n + depth(h)` and the
  evidence carries the same bit.
- `Pkg := BHist`.
- `TokIntro bundle s p := hsame s p`.
- `Domain := Nat`.
- `InDom D h := depth(h) <= D`.
- `Carrier_bound bound h := depth(h) <= bound`.
- `Equiv h k := depth(h) = depth(k)`.
- Stable transformation map is identity on `BHist`.

These definitions let `SigRel`, `Package`, `Gap`, `NameCert`, and `Settled`
manifests be checked as concrete Lean instances.

## Executable Architecture

Target path:

```text
lean4/scripts/rule110_cross_check.lean
```

Lake entry:

```text
lake build rule110-cross-check
```

Stages:

1. Load registered manifest paths.
2. Parse each file, validate `PRODUCTIONS` and `ASSERTIONS`, and dispatch by path.
3. Parse fields, decode input, and convert raw events to typed BEDC values.
4. Evaluate the target checker.
5. Print `PASS` or `FAIL` per assertion and exit nonzero on failure.

Output shape:

```text
PASS mark/msame_refl.enum.ct b0_b0 -> BEDC.FKernel.Mark.msame_refl
FAIL ext/ext_step.enum.ct empty_b0_empty -> expected ext_holds=no, got yes
```

## Worked Example: `msame_refl.enum.ct`

Case `b0_b0` reads `input=011011`, converts it to
`[b0,b1,b1,b0,b1,b1]`, and uses `DecEvent` to read payload `[b0]` followed
by payload `[b0]`.  Both parse as `BMark.b0`; `expected_reflexive=yes`
requires equality; `msame_refl BMark.b0` proves the instance.

Case `b1_b1` reads `input=10111011`.  `DecEvent` reads payload `[b1]`
followed by payload `[b1]`.  Both parse as `BMark.b1`; `msame_refl
BMark.b1` proves the instance.

If the second case encoded `b1,b0`, the row would still decode as two marks,
but it would fail as a ground instance of `msame_refl`.

## Negative and Rejection Cases

Fields like `ext_holds=no`, `cont_holds=no`, `sigrel=no`, `ask_holds=no`,
and `reject=yes` are target-specific.  The manifest spec supplies the meaning:

- `Ext`: prove the complement using constructor characterization.
- `Cont`: unfold to `r = append h k` and decide equality.
- `UnaryHistory`: recurse over `BHist`.
- malformed or trailing cases: expect parser rejection or leftover input.

The field controls polarity; the target spec controls semantics.

## Open Questions

Algorithm manifests: classify `*.algo.ct` as `algoCurrent` until Level 2
provides real recognizers.  The checker can validate assertion semantics, but
CI should not claim placeholder productions compute the relation.

ProbeBundle-parameterized manifests: concrete `AskSetup`, `PackageSetup`, and
`DomainSetup` instances must match the manifest comments.  Missing fixture data
should report `fixture-incomplete`.

Name certificates: `name_cert_basic.enum.ct` contains several interfaces under
one file, so dispatch should use tag and case kind, not only file path.

Settled: `settled_basic.enum.ct` should reuse lower-family checkers where
possible; the settled layer mainly performs tag dispatch and projection checks.

Metadata: current manifests rely on path and case-field conventions.  A future
format could add explicit fields:

```text
target=BEDC.FKernel.Mark.msame_refl
arity=2
polarity=yes
```

The first checker can avoid changing manifests by using path-based dispatch.

## CI Integration

Required commands:

```text
cd rule110 && make test
cd lean4 && lake build rule110-cross-check
```

Scale estimate:

```text
44 manifests x about 30 assertions = about 1320 checks
```

Inputs are small, so runtime should be dominated by Lean startup and imports.
Expected runtime is seconds to low tens of seconds after imports are compiled.

Failure classes are parse failure, decode failure, typed payload failure,
leftover input, unknown field, semantic mismatch, fixture incompleteness, and
missing target registration.  Each failure should include manifest path, case
name, field key, and decoded values when available.

## Level 4 Task Refinement

Concrete implementation sequence:

1. Build parser and typed event conversion.
2. Register closed-kernel specs: Mark, Hist, Ext, Cont, ExternalBinary, Unary.
3. Add fixture setup definitions for Ask, SigRel, Package, Gap, NameCert, and
   Settled.
4. Implement positive and negative target checkers.
5. Add aggregate reporting and nonzero exit behavior.
6. Add the Lake target.
7. Run all strict `.enum.ct` manifests.
8. Report `*.algo.ct` status without claiming real recognizers before Level 2.
9. Write the operational trust-chain page once the checker exists.
