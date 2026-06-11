# Winnability Certificates

- Artifact: `bedc-quality-lab:winnability-certificates`
- Owner: `bedc_quality_lab.winnability`
- Audit: `pass`
- Certificates: `3`
- Fail-closed count: `2`

| row_id | split | method | status | upper bound | observed | coverage |
| --- | --- | --- | --- | --- | --- | --- |
| `win-ecba7e79b6540b31` | `l1-ood-hidden-lag` | `analytic_bayes` | `pass` | `0.0625` | `0.06958` | `not-applicable` |
| `win-8e8c22b9a8c063bc` | `l1-indist-finite-pair` | `analytic_bayes` | `pass` | `0.982829` | `0.981934` | `table-coverage` |
| `win-f539ef1ffa34e2d9` | `l1-held-out-pair` | `analytic_bayes` | `pass` | `1.0` | `0.311768` | `not-applicable` |

## Not Claimed

- Winnability certificates bound finite lab split evidence only.
- No oracle training is performed by this producer.
- A table-coverage certificate does not authorize generalization or rule-abstraction claims.
- An unresolved or unwinnable split remains barred from positive claim use.
