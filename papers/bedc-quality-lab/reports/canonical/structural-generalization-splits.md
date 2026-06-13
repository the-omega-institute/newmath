# Structural Generalization Splits

- Artifact: `bedc-quality-lab:structural-generalization-splits`
- Schema: `bedc-quality-lab:structural-generalization-splits`
- Accepted split rows: `0`
- Boundary rows: `2`

## Source Artifacts

| source | status | artifact |
| --- | --- | --- |
| `input_accessibility` | `resolved` | `reports/canonical/input-accessibility.json` |
| `winnability_certificates` | `resolved` | `reports/canonical/winnability-certificates.json` |

## Classifier Rows

| row | classification | family | reason |
| --- | --- | --- | --- |
| `sgs-symbol-remapping` | `unanswerable` | `` | `target-variable-not-visible-to-all-required-arms` |
| `sgs-position-shift-visible` | `unanswerable` | `` | `target-variable-not-visible-to-all-required-arms` |

## Nonclaims

- Pointer-only structural generalization split registry.
- No held-out pair protocol is owned here.
- No cross-validation verdict is recomputed here.
- No local visibility extractor or winnability arithmetic is introduced here.
- No positive split claim is emitted without resolved upstream evidence pointers.
