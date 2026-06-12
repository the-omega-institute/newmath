# SIGReg Training Proxy

- run_id: `sigreg-training-proxy`
- schema_id: `bedc-quality-lab:sigreg-training-proxy`
- result: `d1-pointer-accepted`
- claim capsule: `reports/runs/sigreg-training-proxy/claim_capsule.json`

## Arms

| arm | alignment | sigreg_sliced_cf | loss |
| --- | ---: | ---: | ---: |
| `covariance_proxy_current` | 0.32013642 | 0.06582335 | 0.25798346 |
| `true_sigreg_sliced_cf` | 0.00549868 | 0.02618002 | 0.01273715 |
| `vicreg_like_covariance` | 0.23469855 | 0.07944820 | 0.19287723 |
| `alignment_only` | 0.00002887 | 0.05616180 | 0.00003108 |

## D1 Hardgates

- `D1-HG1`: `pass`
- `D1-HG2`: `pass`
- `D1-HG3`: `pass`
- `D1-HG4`: `pass`
- `D1-HG5`: `pass`

## Not Claimed

- global model quality
- full LeJEPA reproduction
- full TensorNameCert
- LLM behavior quality
- mechanism closure unless D5-M gate passes
