# Winnability Certificates

- Artifact: `bedc-quality-lab:winnability-certificates`
- Owner: `bedc_quality_lab.winnability`
- Audit: `fail`
- Certificates: `3`
- Fail-closed count: `3`

| certificate_id | split | method | status | upper bound | observed | coverage |
| --- | --- | --- | --- | --- | --- | --- |
| `win-f1471fec0fe8d17c` | `l1-ood-hidden-lag` | `analytic_bayes` | `fail` | `0.0625` | `0.06958` | `unresolved` |
| `win-aaf6363714569e58` | `l1-indist-finite-pair` | `analytic_bayes` | `fail` | `0.0625` | `0.981934` | `unresolved` |
| `win-86184ea92f5c516b` | `l1-held-out-pair` | `analytic_bayes` | `fail` | `0.0625` | `0.311768` | `unresolved` |

## Not Claimed

- Winnability certificates bound finite lab split evidence only.
- No oracle training is performed by this producer.
- A table-coverage certificate does not authorize generalization or rule-abstraction claims.
- An unresolved or unwinnable split remains barred from positive claim use.
