# Ext Design

Phase C target: encode `BEDC.FKernel.Ext.Ext`.
Primary source: `lean4/BEDC/FKernel/Ext.lean`.

## Ext Relation

`Ext.lean` defines the relation at lines 10-12:

```text
inductive Ext : BHist -> BMark -> BHist -> Prop where
  | e0 (h : BHist) : Ext h .b0 (.e0 h)
  | e1 (h : BHist) : Ext h .b1 (.e1 h)
```

There are two constructors over a three-argument relation:

- `Ext.e0 h`: source `h` extended by mark `b0` gives result `e0 h`.
- `Ext.e1 h`: source `h` extended by mark `b1` gives result `e1 h`.

The relation is total in the mark argument, deterministic in the result, and
injective from result back to source/mark because BHist constructors are
disjoint.

## Target Theorems

Main Ext targets in `Ext.lean`:

- `ext_generation_rules (h : BHist)`
  - Lines 14-18. Both constructor cases are available for any source.
- `ext_total : forall h m, exists r, Ext h m r`
  - Lines 20-24. Every source/mark pair has a result.
- `ext_deterministic`
  - Lines 26-29. Same source and mark imply same result up to `hsame`.
- `ext_determinacy_up_to_hsame_spine`,
  `proof_sprint_extension_determinacy`
  - Lines 31-39. Determinism wrappers.
- `ext_mark_deterministic_from_result`
  - Lines 41-44. Same source/result imply same mark.
- `ext_source_deterministic_from_result`
  - Lines 46-49. Same mark/result imply same source.
- `ext_result_injective_pair`
  - Lines 51-54. Same result gives source `hsame` and mark `msame`.
- `ext_result_hsame_injective_pair`
  - Lines 56-69. Same result up to `hsame` gives source/mark equality.
- `ext_cross_mark_result_impossible`
  - Lines 71-75. A fixed source/result cannot be both b0 and b1 extension.
- `ext_respects_sameness`
  - Lines 77-83. Source `hsame` and mark `msame` transport results.
- `ext_result_hsame_source_mark_hsame_iff`
  - Lines 85-92. Result equality iff source equality and mark equality, given
    Ext witnesses.
- `ext_respects_internal_sameness_spine`, `ext_respects_mark_sameness`
  - Lines 94-105. Respectfulness wrappers.
- `ext_constructor_inversion`
  - Lines 107-115. Any Ext proof is either the b0/e0 or b1/e1 case.
- `ext_constructor_characterization`
  - Lines 117-141. Ext iff one of the two constructor equations holds.
- `ext_result_constructor_iff`
  - Lines 143-168. Result constructor determines mark and source tail.
- `ext_result_for_mark`
  - Lines 170-181. b0/b1 mark determines e0/e1 result.
- `ext_b0_result_hsame`, `ext_b1_result_hsame`
  - Lines 183-193. Result is `hsame` to the expected constructor.
- `ext_result_ne_empty`
  - Lines 195-200. Ext results are never Empty.
- `ext_same_source_cross_mark_results_not_hsame`
  - Lines 202-207. b0 and b1 results from same source are not `hsame`.
- `ext_result_source_not_hsame`
  - Lines 209-214. A one-step extension is not `hsame` to its source.
- `ext_two_step_cycle_absurd`
  - Lines 221-239. No two-step extension cycle returns to the original source.

The prompt mentions `Ext_step` and `Ext_inversion`; the current file uses
constructor names `Ext.e0`/`Ext.e1` and theorem names such as
`ext_constructor_inversion`.

## Encoding Strategy

The decision input is a concatenated triple:

```text
BHistEncoding(source) ++ BMarkEncoding(mark) ++ BHistEncoding(result)
```

Recommended concrete form:

- Source and result are BHist events from `bhist_encoding.md`.
- Mark is a full BMark event from the vertical slice:
  - b0 as `EventEncoding([0])`;
  - b1 as `EventEncoding([1])`.

Decision procedure:

1. Decode source BHist.
2. Decode mark event and require exactly one payload byte.
3. Decode result BHist.
4. If mark is b0, accept exactly when result choices are `[0] ++ source`.
5. If mark is b1, accept exactly when result choices are `[1] ++ source`.
6. Reject malformed streams, malformed marks, Empty result for positive Ext,
   wrong constructor, or wrong tail.

The CT algorithm can reuse BHist equality after stripping the expected result
head. In the b0 branch, require result head `0` and compare the result tail with
the source. In the b1 branch, require result head `1` and compare the result
tail with the source.

## Manifest Families

Recommended Phase C manifests:

- Constructor cases: `ext_e0.*.ct`, `ext_e1.*.ct`.
- Inversion and characterization:
  - positive b0/e0 and b1/e1 cases;
  - negative b0/e1, b1/e0, Empty result, and wrong tail cases.
- Determinism:
  - same source/mark with two valid candidate results implies decoded equality.
- Injectivity:
  - same result under two valid triples recovers same source and mark.
- Cycle impossibility:
  - representative histories showing `Ext h m r` and `Ext r n h` cannot both
    hold.

## Test Harness

`tests/test_ext.c` should mirror the mark and hist harnesses.

Suggested helpers:

- `decode_ext_triple(input_bits, &source, &mark, &result)`:
  - decode BHist, BMark event, BHist.
- `mark_is_b0`, `mark_is_b1`:
  - require one-byte decoded mark payload.
- `bhist_tail_equal(result, source)`:
  - compare `result.choices + 1` with `source.choices`.
- `decode_ext_holds(input_bits)`:
  - run the decision procedure above.
- `decode_ext_not_holds(input_bits)`:
  - expects successful decoding but semantic mismatch.

Representative cases:

- `Ext Empty b0 (e0 Empty)`.
- `Ext Empty b1 (e1 Empty)`.
- `Ext (e0 Empty) b0 (e0 (e0 Empty))`.
- `Ext (e1 (e0 Empty)) b1 (e1 (e1 (e0 Empty)))`.
- Negative: `Ext Empty b0 Empty`.
- Negative: `Ext h b0 (e1 h)`.
- Negative: `Ext h b1 (e0 h)`.
- Negative: `Ext h b0 (e0 k)` with `h != k`.

Run semantic assertions through the decoder and CT smoke checks on each
manifest's first positive case.

## Open Questions

- Should the mark inside an Ext triple be a full event or a raw mark payload?
- Should Ext manifests reject trailing input after the third event?
- Will Phase C inline `P_eq` or share a production block with hsame?
- Should malformed mark payloads be explicit negative assertions?
- How much of `ext_two_step_cycle_absurd` should be represented by finite
  runtime cases?
