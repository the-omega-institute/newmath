# Manifest format

Cyclic-tag manifest (`.ct`) is a plain-text, line-based format.

## Structure

```
# comment lines start with '#'
PRODUCTIONS <N>
<bit-string for production 0>
<bit-string for production 1>
...
<bit-string for production N-1>
ASSERTIONS <K>
<assertion line 1>
<assertion line 2>
...
```

## Encoding convention

Bit strings use only `0` and `1` ASCII characters. Encoding follows the
GroundCompiler convention defined in
`lean4/BEDC/GroundCompiler/ChannelEncoding.lean`:

- `b0` (BMark zero) encodes to the single bit `0`.
- `b1` (BMark one) encodes to the two-bit sequence `10`.
- Event terminator: `11` (two ones in sequence).
- Multi-event flow: concatenation of `EventEncoding(event_i)`.

## Assertion line format

Each assertion line is human-readable text containing:
- A case label (e.g., `case b0_b1`)
- A canonical `input=` bit-string
- A semantic expectation (e.g., `expected_unequal=yes`, `holds=trivial`,
  `holds=vacuous`)

Assertions are read by humans (audit) and by `tests/test_mark.c` (runtime
verification). The runtime verification logic is in `test_mark.c`, not in
the manifest — manifests document the intent; tests execute the check.

## Reject reasons

The decoder (`groundcompiler_encoding.c::gc_dec_event`) returns one of:

| Code | Reason | Trigger |
|---|---|---|
| `GC_REJECT_DANGLING_ONE` | dangling escape | bit stream ends with `1` and no following `0` |
| `GC_REJECT_UNFINISHED_EVENT` | no terminator | bit stream ends without `11` |
| `GC_REJECT_NONBINARY_CHARACTER` | non-binary input | byte is not `0` or `1` |
| `GC_REJECT_EMPTY_INPUT_POLICY` | empty input | `in_len == 0` |
| `GC_REJECT_RESOURCE_BOUND_EXCESS` | fuel exhausted | decoder did not converge within `fuel` steps |
| `GC_REJECT_NONCANONICAL_DISPLAY` | parse OK but illegal | reserved for non-canonical orderings |
