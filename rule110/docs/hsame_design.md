# hsame Design

Phase B target: encode `BEDC.FKernel.Hist.hsame` over generated histories.
Primary source: `lean4/BEDC/FKernel/Hist.lean`.

## Lean Shape

`Hist.lean` defines `BHist` at lines 8-12:

```text
inductive BHist where
  | Empty
  | e0 (h : BHist)
  | e1 (h : BHist)
```

The relation is definitionally equality at line 14:

```text
def hsame : BHist -> BHist -> Prop := Eq
```

The manifest layer therefore recognizes equality of decoded constructor-choice
payloads.

## Target Theorems

Core equality and equivalence:

- `hsame_iff_eq {h k : BHist} : hsame h k <-> h = k`
  - Lines 16-17. `hsame` is exactly equality.
- `hsame_refl : forall h : BHist, hsame h h`
  - Lines 19-21. Reflexivity.
- `hsame_symm : forall {h k : BHist}, hsame h k -> hsame k h`
  - Lines 23-25. Symmetry.
- `hsame_trans : forall {a b c : BHist}, hsame a b -> hsame b c -> hsame a c`
  - Lines 27-29. Transitivity.
- `hsame_equivalence`, `history_sameness_equivalence`
  - Lines 54-68. Packed equivalence fields.

Empty-history targets:

- `hsame_empty_inversion {x : BHist} : hsame .Empty x -> x = .Empty`
  - Lines 31-34. Left Empty inversion.
- `hsame_empty_iff {h : BHist} : hsame h BHist.Empty <-> h = BHist.Empty`
  - Lines 36-43. Right Empty characterization.
- `hsame_empty_left_iff {h : BHist} : hsame BHist.Empty h <-> h = BHist.Empty`
  - Lines 45-52. Left Empty characterization.

Constructor congruence and inversion:

- `hsame_constructor_inversion`, `hsame_constructor_inversion_full`
  - Lines 70-90. Same outer constructor and same tail, plus e1/e0
    impossibility.
- `hsame_e1_congr`, `hsame_e1_congruence`, `eone_congruence`, `eone_cong`
  - Lines 92-106. e1 congruence wrappers.
- `hsame_e0_congr`
  - Lines 108-111. e0 congruence.
- `hsame_e0_iff`, `hsame_e1_iff`
  - Lines 113-130. Constructor equality iff tail equality.
- `hsame_e0_inversion`, `hsame_e0_inversion_iff`, `hsame_e0_left_iff`
  - Lines 131-150. e0 inversion forms.
- `hsame_e1_inversion`, `hsame_e1_inversion_iff`
  - Lines 152-167. e1 inversion forms.

Constructor distinctness and no-confusion:

- `not_hsame_emp_e0`, `not_hsame_e0_empty`, `not_hsame_emp_e1`,
  `not_hsame_e1_empty`
  - Lines 169-183. Empty is distinct from both constructors, both directions.
- `not_hsame_e0_e1`, `hsame_e0_e1_iff_false`,
  `not_hsame_e1_e0`, `hsame_e1_e0_iff_false`
  - Lines 185-207. e0/e1 cross-constructor equality is impossible.
- `hsame_extension_self_absurd`
  - Lines 209-234. A history is not equal to its one-step extension.
- `hsame_no_confusion`, `hsame_no_confusion_all`, `history_no_confusion`,
  `history_no_confusion_four_cases`, `history_no_confusion_expanded_pair`,
  `history_no_confusion_empty_pair`,
  `proof_sprint_history_no_confusion_complete`,
  `hsame_no_confusion_symmetric`, `hsame_no_confusion_complete`,
  `history_no_confusion_empty_cross_pair`
  - Lines 236-298 and 366-418. Packaged no-confusion variants.

Constructor characterization:

- `hsame_constructor_kind_preserved`
  - Lines 300-317. Equality preserves Empty/e0/e1 kind and tail equality.
- `hsame_constructor_characterization`, `history_constructor_characterization`
  - Lines 319-364. Equality iff both Empty, both e0 with same tails, or both
    e1 with same tails.

## Encoding Strategy

The hsame manifest input is:

```text
EventEncoding(h1) ++ EventEncoding(h2)
```

Each event uses the BHist payload directly, as specified in
[`bhist_encoding.md`](./bhist_encoding.md). The constructor-choice list is the
event payload:

```text
Empty        -> "11"
e0 Empty     -> "011"
e1 Empty     -> "1011"
e0(e1 Empty) -> "01011"
```

Per-case enumeration is not possible for general `BHist`, because the type is
countably infinite. Phase B should use:

- Representative enum manifests for depth 0, 1, 2, 3, and one deep nesting.
- Algorithm-form manifests whose productions recognize whether two BHist event
  payloads are bit-for-bit equal.

This is the first point where algorithm-form CT productions truly matter. BMark
could fall back to vacuous productions because its domain had two values; BHist
requires an unbounded equality recognizer.

## Representative Enum Cases

Recommended examples:

- `Empty / Empty`: `11 11`.
- `e0 Empty / e0 Empty`: `011 011`.
- `e1 Empty / e1 Empty`: `1011 1011`.
- `e0(e1 Empty) / same`: `01011 01011`.
- `e0(e1(e0 Empty)) / same`: `010011 010011`.
- A deep case such as choices `[0,1,0,1,1,0,0,1]` against itself.
- No-confusion mismatches: Empty/e0, e0/Empty, Empty/e1, e1/Empty, e0/e1,
  and e1/e0.

Spaces above are explanatory only; manifest inputs are plain concatenated bit
strings.

## Real P_eq Sketch

`P_eq` should accept two well-formed BHist event encodings exactly when the
decoded constructor-choice payloads are equal.

A Markov-style cyclic-tag design:

1. Find the first event terminator `11` and thereby split the two payloads.
2. Enter a compare-next-symbol state.
3. Consume or mark one constructor bit from the first payload.
4. Rotate/copy tape state until the next bit of the second payload is active.
5. Verify the second bit is the same bit.
6. Mark both bits consumed and return to the first payload.
7. Accept only when both payloads reach their event terminators on the same
   comparison cycle.
8. Reject unequal length, `0` versus `1`, malformed event syntax, or trailing
   input if Phase B3 chooses exact-two-event semantics.

The design must make tape movement explicit. CT productions cannot randomly
index into two arrays. This is the main risk in the ROADMAP risk register and
may require 10-30 productions.

The simplest positive contract is "halt empty on equality". Negative cases can
initially be checked by the C semantic harness unless the manifest runner gains
a native reject assertion format.

## Test Harness

`tests/test_hist.c` should mirror `tests/test_mark.c`, using the Phase A BHist
decoder:

- `enum_assert_reflexive_hist(input_bits)`:
  - decode two BHist events with `gc_bhist_decode`;
  - assert both decode successfully;
  - compare `depth` and `choices`.
- `decode_two_bhist_equal(input_bits)`:
  - reusable equality helper for refl/symm/trans/characterization cases.
- `decode_two_bhist_unequal(input_bits)`:
  - semantic mismatch helper for no-confusion cases.
- `decode_three_bhist_check_trans(input_bits)`:
  - if `h1 == h2` and `h2 == h3`, assert `h1 == h3`; otherwise the implication
    is vacuous.

Use high decoder fuel for deep histories; `8192` matches the recommendation in
`bhist_encoding.md`.

## Phase B3 Open Questions

- Does `P_eq` parse event syntax itself, or may it assume decoder-normalized
  payloads?
- Should a negative `.algo.ct` case mean non-halting, non-empty halt, or an
  explicit reject marker?
- Should equality consume exactly two events and reject trailing input?
- Should `P_eq` be shared by hsame, Ext, and SameSig manifests?
- How should fuel limits be surfaced in manifest assertions?
