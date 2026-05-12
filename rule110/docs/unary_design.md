# Unary Design

Target: encode `BEDC.FKernel.Unary`.
Primary sources: `lean4/BEDC/FKernel/Unary.lean` and the sibling files under
`lean4/BEDC/FKernel/Unary/`.

## Lean Shape

`UnaryHistory` is the closed all-one spine of `BHist`:

```text
UnaryHistory Empty      = True
UnaryHistory (e1 h)     = UnaryHistory h
UnaryHistory (e0 h)     = False
```

With the existing BHist encoding, this is exactly the event-payload predicate
"every constructor byte is `1`". Empty has an empty payload and is accepted.

`UnaryDomainSetup` uses a unit domain whose membership predicate is
`UnaryHistory`. `UnarySourceSpec` is definitionally the same predicate.
`UnaryRepetitionHistory` is also `UnaryHistory`.

## Encoding Strategy

Single-history input:

```text
BHistEncoding(h)
```

Triple input for continuation cases:

```text
BHistEncoding(h) ++ BHistEncoding(k) ++ BHistEncoding(r)
```

The checker decodes the histories and applies:

```text
unary(h) := all choices in h are 1
cont(h,k,r) := choices(r) = choices(k) ++ choices(h)
```

The relation `Cont h k r` uses the append direction already documented in
`cont_design.md`: the second continuation argument forms the prefix of the
decoded result choices.

## Covered Theorem Families

`manifests/unary/unary_basic.enum.ct` and
`manifests/unary/unary_basic.algo.ct` cover representative cases for:

- `unary_empty`, `unary_e1_closed`, `unary_double_e1_closed`, and
  `unary_history_e1_iff`.
- `unary_no_zero_extension` and e0-headed rejection at several depths.
- `UnarySourceSpec_iff_unaryHistory`, `unaryDomain_inDom_iff_unaryHistory`,
  and `UnaryRepetitionHistory`.
- `UnaryClassifierSpec`, represented by two unary histories plus decoded
  equality.
- `unary_repetition_closed_under_continuation`, `UnaryLedgerPolicy`, and
  `AddLedgerPolicy`, represented by continuation triples whose inputs and
  result are unary.
- `unary_cont_e0_result_absurd`, represented by a continuation triple with an
  e0 result.
- `unary_cont_e1_result_cases`, represented by unit and nonempty right
  argument cases.

The `.algo.ct` production is vacuous by scope. The executable semantic check is
in `tests/test_unary.c`, using the shared GroundCompiler BHist decoder.
