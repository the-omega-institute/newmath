# Causal Patch Suite

- Schema: `bedc-quality-lab:causal-patch-suite`
- Artifact: `bedc-quality-lab:causal-patch-suite`
- DGT mechanism cert status: `present-but-fail-closed`

| patch type | status | source | pointer |
| --- | --- | --- | --- |
| `attention-route` | `pass` | `reports/canonical/gap-head-on-h.json` | `$.treatment_comparison` |
| `ledger-head` | `pass` | `reports/canonical/gap-head-ablation.json` | `$.factor_attribution.learned_head` |
| `gap-head` | `pass` | `reports/canonical/gap_head_attribution_capsule.json` | `$.head_channel_patch_evidence` |
| `D1 feature` | `pass` | `reports/canonical/gap-head-on-h.json` | `$.gap_channel_metadata` |
| `D2 interaction` | `pass` | `reports/canonical/gap-head-on-h.json` | `$.control_protocol` |
| `D3 composition` | `present-but-fail-closed` | `reports/canonical/gap-head-on-h.json` | `$.treatment_verdict` |
| `mechanism probe` | `pass` | `reports/canonical/gap_head_attribution_capsule.json` | `$.score_margin_causal_evidence` |
| `scope-seal` | `pass` | `reports/canonical/gap-head-on-h.json` | `$.scope_seal` |

## Hardgates

| hardgate | status | evidence |
| --- | --- | --- |
| `PATCH-HG1` | `pass` | `$.patch_records` |
| `PATCH-HG2` | `pass` | `$.patch_records[*].summary` |
| `PATCH-HG3` | `pass` | `$.patch_records` |
| `PATCH-HG4` | `pass` | `$.matched_controls` |
| `PATCH-HG5` | `pass` | `$.side_effect_ledger` |
| `PATCH-HG6` | `present-but-fail-closed` | `$.dgt_mechanism_cert` |

## Not Claimed

- No production causality or deployment intervention claim.
- No global model superiority claim.
- No full mechanism closure claim.
- No full TensorNameCert claim.
- No LLM behavior quality claim.
