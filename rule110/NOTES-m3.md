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
