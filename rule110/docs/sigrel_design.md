# SigRel and SameSig Design

Phase D target: encode `BEDC.FKernel.Sig.SigRel` and `SameSig`.
Primary sources: `lean4/BEDC/FKernel/Sig.lean`,
`lean4/BEDC/FKernel/Sig/SameSig.lean`, and
`lean4/BEDC/FKernel/Bundle.lean`.

`Bundle.lean` defines `ProbeBundle` at lines 4-6:

```text
inductive ProbeBundle (PName : Type) where
  | Bnil
  | Bcons (p : PName) (b : ProbeBundle PName)
```

`PName` is abstract in Lean. CT manifests need a ground representation, so use:

```text
ProbeName := Nat
```

Encode each probe name as a unary natural number in an event payload. Encode a
bundle as a list of those events followed by a reserved bundle-end event.

`Sig.lean` defines `SigRel` at lines 16-22:

```text
inductive SigRel : ProbeBundle ProbeName -> BHist -> BHist -> Prop where
  | empty (h : BHist) : SigRel Bnil h Empty
  | cons (pi tail h s r m delta) :
      Ask pi h m delta ->
      SigRel tail h s ->
      Ext s m r ->
      SigRel (Bcons pi tail) h r
```

Semantic intent:

- Empty bundle asks no probes and returns Empty.
- Cons bundle asks head probe `pi` against the original input history `h`,
  recursively computes the tail signature `s`, and extends `s` by the returned
  mark.

`SameSig` is defined at lines 119-120 of `Sig.lean`:

```text
def SameSig (bundle : ProbeBundle ProbeName) (h k : BHist) : Prop :=
  exists s, exists t, SigRel bundle h s /\ SigRel bundle k t /\ hsame s t
```

Two histories have the same signature when both have generated signatures under
the bundle and those signature histories are `hsame`.

SigRel targets in `Sig.lean`:

- `sig_empty_constructor`
  - Lines 24-26. Empty bundle produces Empty.
- `sig_cons_constructor`
  - Lines 28-33. Builds cons SigRel from Ask, tail SigRel, and Ext.
- `sig_cons_inversion`
  - Lines 35-42. Inverts cons SigRel into Ask, tail, and Ext witnesses.
- `sig_cons_head_mark_determinacy`, `sig_cons_head_marks_same`
  - Lines 45-81. Deterministic policy gives same head marks.
- `sig_cons_result_inversion`
  - Lines 83-104. Cons result has the constructor implied by the head mark.
- `sigRel_cons_inversion`, `sig_empty_inversion`
  - Lines 106-117. Inversion wrappers for cons and empty bundle.
- `SigTotalOn`, `sig_total_from_policy`, `sigTotalOn_from_policy`,
  `sigTotalOn_tail_of_cons`
  - Lines 148-193. Totality and tail extraction.
- `sig_deterministic`
  - Lines 195-211. Deterministic Ask policy gives deterministic signatures.
- `sig_cons_determinacy_spine`, `sig_cons_tail_deterministic`
  - Lines 214-274. Witness-rich determinacy wrappers.
- `sig_respects_history`
  - Lines 276-294. Input `hsame` transports signatures under a policy.

## SameSig Equivalence Theorems

SameSig targets in `Sig.lean`:

- Intro/projection/reflexive witness:
  `sameSig_intro_from_witnesses`, `sameSig_witnesses`,
  `sameSig_refl_from_witness` at lines 123-146.
- Policy transport:
  `sameSig_of_hsame_under_policy`, `sameSig_of_hsame_from_ask_policy` at lines
  297-317.
- Equivalence fields:
  `sameSig_refl`, `sameSig_refl_under_policy`, `sameSig_symm`,
  `sameSig_trans_from_middle_determinacy`, `sameSig_trans`,
  `sameSig_trans_under_policy` at lines 319-414.
- Packed equivalence wrappers:
  `sameSig_equivalence_from_total_and_determinacy`, `sameSig_equivalence`,
  `signature_sameness_equivalence_policy_spine`,
  `sameSig_equivalence_under_policy` at lines 417-604.

Witness targets in `Sig/SameSig.lean`:

- Witness projections and empty bundle:
  `sameSig_left_witness`, `sameSig_right_witness`,
  `sameSig_hsame_witness`, `signature_sameness_witnesses`,
  `sameSig_empty_bundle`, `sameSig_witness_pair_symm` at lines 9-75.
- Policy witness transport and transitivity chains:
  `sameSig_of_hsame_witnesses_under_policy`,
  `signature_totality_respects_hsame_witnesses`,
  `sameSig_trans_with_middle_witness`,
  `sameSig_middle_witnesses_hsame_under_policy`,
  `sameSig_trans_explicit_witness_chain`,
  `sameSig_four_step_chain_under_policy` at lines 77-267.
- Equivalence and witness-pack wrappers:
  `signature_sameness_equivalence_total_determinacy`,
  `signature_sameness_equivalence`,
  `sameSig_equivalence_policy_spine_fields`,
  `signature_sameness_equivalence_proof_spine`,
  `sameSig_equivalence_witness_pack`,
  `sameSig_equivalence_explicit_witnesses` at lines 269-588.

## Encoding Strategy

Concrete manifest choice:

```text
ProbeName(n) payload = [0 repeated n, 1]
ProbeNameEncoding(n) = EventEncoding(ProbeName(n) payload)
```

Bundle encoding:

```text
BundleEncoding(Bnil) = EventEncoding([1,1])
BundleEncoding(Bcons p tail) = ProbeNameEncoding(p) ++ BundleEncoding(tail)
```

The `[1,1]` payload is a reserved bundle-end marker encoded as a normal event
payload. If this marker is too close to existing conventions, Phase D2 can pick
another reserved payload such as `[1,0,1]`.

SigRel decision input:

```text
BundleEncoding(bundle) ++ BHistEncoding(source) ++ BHistEncoding(result)
```

SameSig decision input:

```text
BundleEncoding(bundle) ++ BHistEncoding(h) ++ BHistEncoding(k)
```

Each BHist segment uses [`bhist_encoding.md`](./bhist_encoding.md).

Lean `SigRel` depends on abstract `Ask pi h m delta`. The CT substrate must use
a concrete manifest fixture. Recommended scope:

- Use a deterministic Ask policy in tests.
- Let probe `n` return parity of `n + depth(h)`.
- State that the fixture supports executable examples and does not replace
  Lean's abstract `AskSetup`.

With a fixed policy, SigRel is decidable:

1. Decode bundle and source history.
2. Start signature accumulator at Empty.
3. Traverse probes in bundle order.
4. Compute fixture Ask mark and apply Ext.
5. Compare the computed accumulator to the encoded SigRel result, or compute
   two accumulators and compare them for SameSig.

The final comparison should reuse BHist `P_eq`.

## Test Harness

`tests/test_sig.c` should combine a semantic decoder harness with CT smoke
tests. Suggested helpers:

- `decode_probe_name_event` parses one unary probe-name event.
- `decode_probe_bundle` parses probe events until the bundle-end marker.
- `fixture_ask_mark` computes the deterministic b0/b1 fixture mark.
- `compute_sigrel_result` starts from Empty and applies Ext for each mark.
- `decode_sigrel_holds` compares computed SigRel result to encoded result.
- `decode_sameSig_holds` computes two signatures and compares them by BHist
  equality.

Representative tests: empty bundle SameSig, singleton probes 0 and 1, two-probe
bundle `[0,1]` over depths 0/1/3, symmetry by swapping inputs, a transitivity
representative, and negative SigRel cases with wrong result depth, head mark, or
tail.

## Open Questions

- Which fixture Ask policy gives simple examples while exercising b0 and b1?
- Is unary `ProbeName` acceptable for CT tape size?
- Should bundle termination use a reserved marker or a length prefix?
- Should SameSig manifests include explicit witness signatures `s,t`?
- Which SameSig wrappers need dedicated manifests rather than projection tests?
