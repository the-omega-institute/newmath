# Structural Generalization Splits

- Artifact: `bedc-quality-lab:structural-generalization-splits`
- Schema: `bedc-quality-lab:structural-generalization-splits`
- Accepted split rows: `0`
- Boundary rows: `2`

## Source Artifacts

| source | status | artifact |
| --- | --- | --- |
| `input_accessibility` | `missing` | `reports/canonical/input-accessibility.json` |
| `winnability_certificates` | `resolved` | `reports/canonical/winnability-certificates.json` |

## Classifier Rows

| row | classification | family | reason |
| --- | --- | --- | --- |
| `sgs-symbol-remapping` | `excluded` | `` | `required-source-artifact-unresolved` |
| `sgs-position-shift-visible` | `excluded` | `` | `required-source-artifact-unresolved` |

## Nonclaims

- Pointer-only structural generalization split registry.
- No held-out pair protocol is owned here.
- No cross-validation verdict is recomputed here.
- No local visibility extractor or winnability arithmetic is introduced here.
- No positive split claim is emitted without resolved upstream evidence pointers.
