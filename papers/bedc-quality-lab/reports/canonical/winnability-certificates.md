# Winnability Certificates

- Artifact: `bedc-quality-lab:winnability-certificates`
- Owner: `bedc_quality_lab.winnability`
- Audit: `pass`
- Certificates: `3`
- Fail-closed count: `0`

| certificate_id | split | method | status | upper bound | observed | coverage |
| --- | --- | --- | --- | --- | --- | --- |
| `win-f1471fec0fe8d17c` | `l1-ood-hidden-lag` | `analytic_bayes` | `pass` | `1.0` | `0.036865` | `not-applicable` |
| `win-aaf6363714569e58` | `l1-indist-finite-pair` | `analytic_bayes` | `pass` | `0.982829` | `0.03418` | `not-table-coverage` |
| `win-86184ea92f5c516b` | `l1-held-out-pair` | `analytic_bayes` | `pass` | `1.0` | `0.038086` | `not-applicable` |

## Not Claimed

- Winnability certificates bound finite lab split evidence only.
- No oracle training is performed by this producer.
- A table-coverage certificate does not authorize generalization or rule-abstraction claims.
- An unresolved or unwinnable split remains barred from positive claim use.
