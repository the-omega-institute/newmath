# Cont Design

Target: encode `BEDC.FKernel.Cont.Cont`.
Primary source: `lean4/BEDC/FKernel/Cont.lean`.

## Lean Shape

`Cont.lean` defines an append operation and a relation:

```text
def append : BHist -> BHist -> BHist
  | h, .Empty => h
  | h, .e0 k => .e0 (append h k)
  | h, .e1 k => .e1 (append h k)

def Cont (h k r : BHist) : Prop := r = append h k
```

The second argument drives recursion. If `BHist` is represented as an
outermost-first constructor-choice list, then:

```text
choices(append h k) = choices(k) ++ choices(h)
```

For example, `append (e0 Empty) (e1 Empty) = e1 (e0 Empty)`.

## Encoding Strategy

The manifest input is a concatenated triple:

```text
EventEncoding(h) ++ EventEncoding(k) ++ EventEncoding(r)
```

Each component is a BHist event as specified in
[`bhist_encoding.md`](./bhist_encoding.md). The checker:

1. Decodes exactly three BHist events.
2. Rejects trailing input after the third event.
3. Requires `depth(r) = depth(h) + depth(k)`.
4. Requires the first `depth(k)` result choices to equal `k`.
5. Requires the remaining result choices to equal `h`.

This directly mirrors the Lean recursion on `k`.

## Covered Cases

`manifests/cont/cont_basic.enum.ct` and
`manifests/cont/cont_basic.algo.ct` cover:

- `Cont Empty Empty Empty`.
- `Cont h Empty h`.
- `Cont Empty k k`.
- Mixed constructor cases where result choices are `k ++ h`.
- Negative well-formed triples with the wrong result depth or constructor
  order.

The current `.algo.ct` file uses a vacuous production, matching the Ext
precedent. The semantic Cont check is executable in `tests/test_cont.c` through
the shared BHist decoder.

## Lean Theorem Alignment

The executable predicate supports representative cases for the main theorem
families in `Cont.lean`:

- `cont_intro` and `cont_iff_append`: direct equality with decoded append.
- `cont_step_zero`, `cont_step_one`, and `cont_relation_generated_rules`:
  adding an outer constructor to `k` adds the same outer constructor to `r`.
- `cont_left_unit`, `cont_right_unit`, and their iff/unique forms: empty
  history cases are checked explicitly.
- `cont_right_constructor_inversion`, `cont_e0_result_inversion`, and
  `cont_e1_result_inversion`: result head agrees with the right argument head
  unless the right argument is empty.
- `cont_deterministic`, cancellation wrappers, and associativity witnesses:
  all reduce to the same decoded append equation over BHist choice lists.
