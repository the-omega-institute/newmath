# Manifest exhaustiveness audit findings

`tools/manifest_exhaustiveness_audit.c` compares finite closure slices with the
assertion inputs listed in `.enum.ct` manifests. The audit treats each manifest
input as a GroundCompiler display stream and reports whether every generated
slice instance is present in the manifest.

## Target set

The current audit set contains nineteen concrete targets:

| target | closure slice | manifest cases | covered | status |
|---|---:|---:|---:|---|
| `BMark / msame_refl` | 2 | 2 | 2/2 | PASS |
| `BMark / msame_symm` | 4 | 4 | 4/4 | PASS |
| `BMark / msame_trans` | 8 | 8 | 8/8 | PASS |
| `BMark / msame_no_confusion` | 2 | 2 | 2/2 | PASS |
| `BHist / hsame_refl` | 3 | 5 | 3/3 | PASS |
| `BHist / hsame_symm` | 9 | 7 | 3/9 | PARTIAL |
| `BHist / hsame_trans` | 27 | 8 | 6/27 | PARTIAL |
| `BHist / hsame_empty_inversion` | 5 | 5 | 5/5 | PASS |
| `BHist / hsame_constructor_distinct` | 6 | 12 | 6/6 | PASS |
| `Ext / ext_step` | 6 | 8 | 4/6 | PARTIAL |
| `SigRel / sigrel_basic` | 27 | 9 | 0/27 | PARTIAL |
| `SameSig / samesig_equiv` | 27 | 9 | 0/27 | PARTIAL |
| `Cont / cont_basic` | 9 | 10 | 4/9 | PARTIAL |
| `Unary / unary_basic` | 7 | 14 | 6/7 | PARTIAL |
| `Ask / ask_basic` | 24 | 12 | 8/24 | PARTIAL |
| `ExternalBinary / external_binary_basic` | 9 | 12 | 4/9 | PARTIAL |
| `GroundCompiler / flow_round_trip` | 3 | 5 | 3/3 | PASS |
| `GroundCompiler / bhist_injectivity` | 9 | 6 | 4/9 | PARTIAL |
| `GroundCompiler / reject_reasons` | 6 | 6 | 6/6 | PASS |

Summary:

```text
19 audit targets
9 strict PASS
10 partial coverage
0 parse/enumeration failure
```

## Closure depths

`BMark` is nullary, so depth `1` is the full closed domain. Recursive `BHist`
targets use depth `1` unless a unary predicate needs the first mixed
depth-`2` slice. Relational fixtures such as `Ext`, `Cont`, and
`ExternalBinary` enumerate positive closure witnesses over source/input
histories up to depth `1`. GroundCompiler reject reasons are a closed
six-case decoder taxonomy.

The audit target set only includes targets with an implemented C enumerator.
The tag-heavy fixture manifests for `Bundle`, `Gap`, `Package`, `NameCert`,
and `Settled` are not counted in the strict denominator here.

## Partial coverage

Partial coverage means the manifest is a representative-case fixture for the
selected slice, not a complete manifest for that slice. In reporting mode this
is informational. In strict mode any partial target returns nonzero.

Representative missing instances:

```text
BHist / hsame_symm:
  11011
  111011
  01111
  011011
  101111
  10111011

Ext / ext_step:
  011101110011
  101101101011

Unary / unary_basic:
  0011

GroundCompiler / bhist_injectivity:
  11011
  111011
  01111
  101111
  1011011
```

`SigRel / sigrel_basic` and `SameSig / samesig_equiv` have zero coverage
against the depth-`1` fixture closure because their manifests list hand-picked
semantic examples rather than every bundle/history/result stream in that
slice.

## Gate behavior

Default `make test` runs the audit in reporting mode and exits zero when the
tool parses and enumerates successfully. `make test-exhaustiveness` runs strict
mode and exits nonzero unless every target is PASS.
