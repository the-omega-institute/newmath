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

## Rule 110 manifest format (`.r110`)

Rule 110 manifests describe a finite cellular-automaton substrate row and the
row expected after a bounded number of Rule 110 steps. They are plain-text,
line-based files intended for `mr_run_r110_manifest` in the Phase D1 manifest
runner.

The required fields are:

```text
INITIAL_PATTERN <bit-string>
EVOLUTION_STEPS <non-negative decimal integer>
EXPECTED_FINAL_PATTERN <bit-string>
```

Comment lines begin with `#` and may appear between fields. Blank lines are
ignored. A minimal manifest is:

```text
# empty cyclic-tag Cook scaffold
INITIAL_PATTERN 0001001101111100010011011111
EVOLUTION_STEPS 0
EXPECTED_FINAL_PATTERN 0001001101111100010011011111
```

The bit strings are ASCII encodings of Rule 110 cells:

- `0` means a dead cell.
- `1` means a live cell.
- One character represents one cell.
- No whitespace is allowed inside a bit string.
- The runner rejects any character other than `0` or `1`.

The finite row uses the same boundary convention as `evaluator/rule110.c`:
cells outside the stored row are read as `0` unless a runner explicitly pads a
larger ether context before execution. Cook-construction manifests should carry
enough guard ether inside `INITIAL_PATTERN` and `EXPECTED_FINAL_PATTERN` for the
declared `EVOLUTION_STEPS`.

Best-effort Cook encodings can be phase-uncertain. A runner therefore may
accept a tolerance parameter when comparing the final row:

```text
mr_run_r110_manifest(path, tolerance)
```

The tolerance is a non-negative cell count used by behavioral tests to permit
small phase offsets around the expected disturbance window. A tolerance of `0`
means byte-for-byte equality between the evolved row and
`EXPECTED_FINAL_PATTERN`. Nonzero tolerance is only appropriate for explicitly
best-effort Cook encoder tests; it must not be used for exact evaluator tests.
