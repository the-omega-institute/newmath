# rule110-m3 Notes

## Lean Reading Observations

- `Hist.lean`: 420 lines, 45 theorem declarations. `hsame` is definitionally
  `Eq`, but the file exposes many wrapper targets: equivalence packs,
  constructor congruence/inversion, no-confusion packs, and constructor
  characterization.
- `Ext.lean`: 241 lines, 24 theorem declarations. `Ext` has two constructors
  over a three-argument relation: b0 maps `h` to `e0 h`, and b1 maps `h` to
  `e1 h`.
- `Sig.lean`: 606 lines, 31 theorem declarations. `SigRel` depends on abstract
  `AskSetup`, so manifest examples need an explicit fixture Ask policy rather
  than pretending the abstract Lean parameter is ground data.
- `Sig/SameSig.lean`: 590 lines, 18 theorem declarations. Most targets are
  witness projections, equivalence packs, or explicit transitivity chains over
  the `SameSig` definition from `Sig.lean`.
- `Bundle.lean`: 641 lines, 47 theorem declarations. `ProbeBundle` itself is a
  generated list (`Bnil | Bcons p tail`) over an abstract `PName : Type`.

## Encoding Choices to Confirm Later

- hsame inputs should be exactly two BHist events:
  `EventEncoding(h1) ++ EventEncoding(h2)`, using `bhist_encoding.md` option
  alpha.
- BHist hsame cannot be exhausted by enum cases. Phase B3 needs a real CT
  equality program over event payloads.
- Ext triples are best encoded as three events: BHist source, BMark mark, BHist
  result.
- ProbeBundle manifests should ground `ProbeName` as unary natural numbers and
  reserve an encoded marker event for bundle end.
- SigRel and SameSig need a deterministic manifest Ask fixture. This fixture is
  only for executable CT examples and should not be described as changing the
  Lean abstraction.

## hsame Symmetry and Empty Inversion (B5+B7)

- `hsame_symm` coverage uses seven representative two-history streams:
  Empty/Empty, both one-step cross-constructor orders, `e0(e1 Empty)` against
  itself, one deep self-pair, and two same-depth unequal deep pairs.
- Empty inversion coverage uses Empty/Empty plus Empty against each one-step
  constructor in both left and right positions.
- The `.algo.ct` files keep vacuous productions under the current B3 boundary;
  executable semantics are checked by `gc_bhist_decode` in `tests/test_hist.c`.

## BHist hsame Transitivity And Constructor Distinctness (B6+B8)

- `hsame_trans` is represented by eight BHist triple cases spanning Empty,
  depth-1, depth-2, and mixed vacuous antecedents.
- Constructor distinctness is represented by twelve BHist pair cases: the six
  outer-constructor directions at depth 1 and matching depth-3 representatives.
- The current `hsame_trans.algo.ct` and `hsame_constructor_distinct.algo.ct`
  use vacuous productions while B3 owns the unbounded BHist equality recognizer.
## B3 P_eq_bhist Observation

- `hsame_refl.algo.ct` uses 16 non-empty productions as a bounded marker
  certifier for the five representative reflexive BHist inputs. The CTS output
  records the positions of `1` bits in each input, so the manifest pipeline is
  doing input-dependent cyclic-tag computation.
- The result is partial scope: it does not compare arbitrary BHist pairs, and it
  does not reject unequal histories. The remaining hard part is retaining the
  first event payload while the second event is consumed and detecting both
  terminators in the same comparison cycle.

## Ext Step Encoding

- `Ext` step inputs are three events:
  `EventEncoding(source) ++ EventEncoding(mark) ++ EventEncoding(result)`.
  The mark event must decode to exactly one bit.
- The executable check treats `e0 h` and `e1 h` as outer constructor extension:
  result depth is source depth plus one, result head is the mark bit, and result
  tail is byte-equal to the source choices.
- `ext_step.enum.ct` and `ext_step.algo.ct` cover five constructor-positive
  triples and three decoded non-Ext triples. The algo manifest keeps vacuous
  CT productions under the current manifest-runner boundary; semantic checking
  is in `tests/test_ext.c`.

## SigRel and SameSig Manifests

- `ProbeName` is grounded as unary natural numbers, encoded as event payloads
  `[0 repeated n, 1]`. A bundle is a sequence of these probe events followed by
  the empty event terminator `"11"`.
- The executable fixture Ask policy returns parity of `probe_name + depth(h)`.
  This keeps SigRel representative cases decidable while leaving Lean's
  abstract `AskSetup` untouched.
- `sigrel_basic` covers empty bundle, singleton probes, two-probe bundles, and
  wrong-result negative cases. `samesig_equiv` covers reflexivity, symmetry,
  transitivity, and vacuous antecedents under the same fixture signatures.

## Cont Relation Encoding

- `Cont.lean` defines `append` by recursion on the second history argument:
  `append h Empty = h`, `append h (e0 k) = e0 (append h k)`, and similarly for
  `e1`.
- Under the existing BHist event encoding, `Cont h k r` is checked by decoding
  three events and requiring `choices(r) = choices(k) ++ choices(h)`.
- `cont_basic.enum.ct` and `cont_basic.algo.ct` cover identity cases, mixed
  constructor-positive triples, and well-formed triples with wrong result
  depth or order. The algo manifest follows the current Ext pattern: vacuous CT
  production with semantic checking in `tests/test_cont.c`.

<<<<<<< HEAD
## ProbeBundle Encoding

- `ProbeBundle` uses the `sigrel_design.md` fixture: probe names are unary
  natural-number events, and bundles are event lists terminated by the reserved
  bundle-end event `[1,1]`.
- `bundle_length.*.ct` covers append length aliases, nil units, associativity,
  append equality iff nil, and fixed-length split uniqueness representatives.
- `bundle_membership.*.ct` covers nil/cons/singleton membership, append
  membership flattening up to four bundles, member split, cancellation, and
  append result inversion.
- `tests/test_bundle.c` owns executable semantics: decoded bundles are
  arrays of probe numbers, append is array concatenation, length is array
  length, and membership is array search.

## Unary Module Encoding

- `UnaryHistory` accepts exactly Empty and histories whose decoded BHist
  payload contains only `1` constructor choices. Any decoded `0` choice is the
  `e0` rejection path.
- `UnaryDomain`, `UnarySourceSpec`, and `UnaryRepetitionHistory` share the same
  executable predicate as `UnaryHistory`.
- Unary continuation closure is checked by combining the existing Cont append
  direction with the all-one predicate: if `choices(r) = choices(k) ++
  choices(h)` and both inputs are all-one, then the result is all-one.
- `unary_basic.enum.ct` and `unary_basic.algo.ct` cover Empty, one-step and
  multi-step unary histories, e0-headed rejection, classifier equality,
  continuation unit cases, mixed unary append, e0-result rejection, and e1
  result classification. The semantic checker is `tests/test_unary.c`.

## Ask Module Encoding

- `Ask.lean` exposes `AskSetup` as an abstract typeclass with `ProbeName`,
  `Evidence`, and a four-argument `Ask` relation. The rule110 encoding uses a
  concrete fixture instance rather than treating the abstract typeclass as
  ground data.
- The fixture reuses the SigRel parity policy:
  `mark = (probe_name + depth(history)) mod 2`. Evidence is encoded as the same
  one-bit event, so positive Ask quadruples carry both the deterministic mark
  and a checked evidence token.
- `ask_basic.enum.ct` and `ask_basic.algo.ct` cover six positive quadruples and
  six negative or malformed streams. The semantic harness in `tests/test_ask.c`
  rejects bad unary probe names, wrong marks, wrong evidence, and trailing
  input.

## ExternalBinary Encoding

- `ExternalBinary.lean` aliases `BWord` and `Mbin` to `BHist`, so the rule110
  representation reuses `BHistEncoding` directly: one GroundCompiler event
  whose payload is the outermost-first constructor-choice list.
- ExternalBinary `append` is `Cont.append`; executable append triples use
  `EventEncoding(a) ++ EventEncoding(b) ++ EventEncoding(r)` and require
  `choices(r) = choices(b) ++ choices(a)`.
- `external_binary_basic.enum.ct` and `.algo.ct` cover unit laws, mixed
  constructors, and negative wrong-result triples. `tests/test_external_binary.c`
  also checks representative model reuse, constructor-result inversion,
  cross-bit impossibility, cancellation, and congruence cases.

## Gap Module Encoding

- `InGapSig bundle D p h` is executed as domain membership plus an explicit
  signature/token witness. The ground fixture uses `Domain := Nat` with
  `depth(h) <= D`, and `Pkg := BHist` with token introduction by BHist equality
  to the witness signature.
- The Gap harness reuses the SigRel deterministic Ask fixture:
  `Ask(n, h) = parity(n + depth(h))`. This preserves the abstract Lean
  interface while making representative manifests executable.
- `CompGap` is represented by an explicit source/intermediate/final ledger and
  a two-bit event for the two supplied relation facts. This directly mirrors
  the Lean existential middle-witness shape.

## Package Module Encoding

- `PackageSetup` remains abstract in Lean, so the rule110 ground fixture uses
  the concrete signature package instance: `Pkg := BHist` and `TokIntro bundle
  s p` iff the decoded source history and package history are byte-equal.
- `psame` is checked by decoding two source histories and two packages,
  requiring both token introductions and equality of the source histories. This
  directly represents the constructor witness in `Package/Core.lean`.
- `PackageTokenPolicy` classification is represented by two claim bits:
  `claimed_psame` and `claimed_hsame`. The harness recomputes both truth
  values for introduced tokens and accepts exactly matching classifications.
- `package_basic.enum.ct` and `.algo.ct` cover token positives and rejections,
  `psame` reflexivity and symmetry representatives, negative nonintroduced and
  distinct-history cases, soundness/reflection classifications, and a two-step
  transitivity chain.
