# Rule110 Lean Cross-Check

Run from the repository root:

```bash
cd lean4
lake build rule110-cross-check
lake exe rule110-cross-check
```

With no arguments, `lake exe rule110-cross-check` checks every registered
`.enum.ct` manifest under `rule110/manifests`:

- `mark/msame_refl.enum.ct`
- `mark/msame_symm.enum.ct`
- `mark/msame_trans.enum.ct`
- `mark/msame_no_confusion.enum.ct`
- `hist/hsame_refl.enum.ct`
- `hist/hsame_symm.enum.ct`
- `hist/hsame_trans.enum.ct`
- `hist/hsame_empty_inversion.enum.ct`
- `hist/hsame_constructor_distinct.enum.ct`
- `ext/ext_step.enum.ct`
- `cont/cont_basic.enum.ct`
- `sig/sigrel_basic.enum.ct`
- `sig/samesig_equiv.enum.ct`
- `bundle/bundle_length.enum.ct`
- `bundle/bundle_membership.enum.ct`
- `unary/unary_basic.enum.ct`
- `ask/ask_basic.enum.ct`
- `external_binary/external_binary_basic.enum.ct`
- `gap/gap_basic.enum.ct`
- `package/package_basic.enum.ct`
- `name_cert/name_cert_basic.enum.ct`
- `settled/settled_basic.enum.ct`

To run selected manifests manually:

```bash
cd lean4
lake env lean --run scripts/rule110_cross_check.lean \
  ../rule110/manifests/sig/sigrel_basic.enum.ct
```

The checker parses `PRODUCTIONS` and `ASSERTIONS`, extracts each `input=`
bit string, and decodes events with
`BEDC.GroundCompiler.ChannelEncoding.DecEvent`.  Every manifest must declare
`PRODUCTIONS 0`; any parse, decode, target, fixture, or semantic mismatch exits
nonzero.

Strict closed-kernel checks instantiate existing Lean targets for mark, hist,
ext, cont, bundle, unary, and external-binary assertions.  Negative assertions
are checked as relation complements or malformed-input rejection according to
the manifest field.

The parameterized families use the concrete manifest fixtures:

- Ask: `ProbeName := Nat`, `Evidence := BMark`, with parity policy
  `(probe + depth(history)) mod 2`.
- Sig: the same parity Ask fixture, with signatures computed in bundle order.
- Package: `Pkg := BHist`, `TokIntro bundle s p := hsame s p`.
- Gap: `Domain := Nat`, `InDom D h := depth(h) <= D`, plus the Sig and Package
  fixtures.
- NameCert: bounded carrier, depth equivalence, and identity stable
  transformation fixture.
- Settled: projection assertions reuse the lower-family fixture checkers where
  the payload is shared, especially signature, package, gap, and bundle
  payloads.

Bundle manifests on disk are split into `bundle_length.enum.ct` and
`bundle_membership.enum.ct`.  They together cover the ProbeBundle family in
the default executable target.

Each `PASS` line includes the manifest path, family, case name, decoded value
summary, assertion polarity when relevant, and Lean target key.  The checks are
ground instances of Lean definitions and theorems over finite manifest inputs;
they are not exhaustive coverage claims for infinite carriers such as `BHist`
or `ProbeBundle Nat`.
