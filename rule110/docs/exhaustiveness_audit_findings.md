# Manifest exhaustiveness audit findings

`tools/manifest_exhaustiveness_audit.c` checks the finite-witness reading of
`BEDC.FKernel.Mark.msame_refl` against
`manifests/mark/msame_refl.enum.ct`.

## Scope

Target theorem:

```text
msame_refl : forall m : BMark, msame m m
```

Lean source:

```text
lean4/BEDC/FKernel/Mark.lean
```

The current `BMark` closure contains two nullary constructors:

```text
b0
b1
```

The audit enumerates `BMark` to depth 3. Since both constructors are nullary,
depth 3 has the same closure as depth 0: two instances.

## Manifest decoding

The manifest assertion input is decoded as two GroundCompiler events. For
`msame_refl`, both decoded events must be the same `BMark` value:

```text
011011     -> b0, b0
10111011   -> b1, b1
```

## Current result

```text
enumerated_total = 2
manifest_case_count = 2
manifest_covered = 2
exhaustiveness = 2/2
```

The manifest covers every `BMark` instance in the depth-3 closure for this
pilot target.

## Gate behavior

Default `make test` runs the audit in reporting mode. `make test-exhaustiveness`
runs the same audit in strict mode and exits nonzero if any enumerated instance
is absent from the manifest.
