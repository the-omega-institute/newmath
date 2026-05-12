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
