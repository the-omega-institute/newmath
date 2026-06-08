# Discovery-Gated Transformer

- Generated at: `2026-06-08T21:22:53.390414+00:00`
- Schema: `bedc-quality-lab:discovery-gated-transformer`
- Artifact: `bedc-quality-lab:discovery-gated-transformer`
- Model: `discovery-gated-transformer`
- Hardgate: `pass`

## Component Refs

| component | artifact | pointer |
| --- | --- | --- |
| `hardgate_contract` | `reports/canonical/new_model_hardgates.json` | `$.gates` |
| `discovery_gated_nas` | `reports/canonical/discovery-gated-nas.json` | `$.candidate_protocol.design_search_certificate` |
| `discovery_map` | `reports/canonical/discovery_map.json` | `$.coverage_matrix` |
| `training_replay` | `reports/canonical/discovery-gated-transformer-training.json` | `$.hardgates` |

## Hardgates

| gate | status | evidence |
| --- | --- | --- |
| `DGT-HG1` | `pass` | `reports/canonical/discovery-gated-transformer.json:$.schema_id` |
| `DGT-HG2` | `pass` | `reports/canonical/discovery-gated-transformer.json:$.artifact_id` |
| `DGT-HG3` | `pass` | `reports/canonical/discovery-gated-transformer.json:$.model_id` |
| `DGT-HG4` | `pass` | `reports/canonical/discovery-gated-transformer.json:$.architecture_spec` |
| `DGT-HG5` | `pass` | `reports/canonical/discovery-gated-transformer.json:$.component_refs.hardgate_contract` |
| `DGT-HG6` | `pass` | `reports/canonical/discovery-gated-transformer.json:$.component_refs.discovery_gated_nas` |
| `DGT-HG7` | `pass` | `reports/canonical/discovery-gated-transformer.json:$.component_refs.discovery_map` |
| `DGT-HG8` | `pass` | `reports/canonical/discovery-gated-transformer.json:$.component_refs.training_replay` |
| `DGT-HG9` | `pass` | `reports/canonical/discovery-gated-transformer.json:$.discovery_map_signal` |
| `DGT-HG10` | `pass` | `reports/canonical/discovery-gated-transformer.json:$.claim_capsule_ref` |
| `DGT-HG11` | `pass` | `reports/canonical/discovery-gated-transformer.json:$.evidence_envelope_ref` |
| `DGT-HG12` | `pass` | `reports/canonical/discovery-gated-transformer.json:$.mechanism_namecert_ref` |
| `DGT-HG13` | `pass` | `reports/canonical/discovery-gated-transformer.json:$.jet_certificate_ref` |
| `DGT-HG14` | `pass` | `reports/canonical/discovery-gated-transformer.json:$.not_claimed` |
| `DGT-HG15` | `pass` | `reports/runs/discovery-gated-transformer/claim_capsule.json:$.owner_ref` |
| `DGT-HG16` | `pass` | `reports/runs/discovery-gated-transformer/evidence_envelope.json:$.component_refs` |
| `DGT-HG17` | `pass` | `reports/runs/discovery-gated-transformer/mechanism_namecert.json:$.evidence_ref` |
| `DGT-HG18` | `pass` | `reports/runs/discovery-gated-transformer/jet_certificate.json:$.owner_ref` |
| `DGT-HG19` | `pass` | `reports/canonical/discovery-gated-nas.json:$.candidate_protocol.design_search_certificate` |
| `DGT-HG20` | `pass` | `reports/canonical/discovery-gated-transformer.json:$.not_claimed` |

## Tool Route Evidence

- Schema: `bedc-quality-lab:discovery-gated-transformer.tool-route-evidence`
- Owner: `reports/canonical/discovery-gated-transformer.json:$`
- CGA route patch: `reports/canonical/certificate-gated-attention.json:$.route_patch_protocol`
- Hardgate: `pass`

| route | class | decision |
| --- | --- | --- |
| `route_math_lookup_positive` | `valid_positive_discovery` | `admit` |
| `route_ledger_patch_positive` | `valid_positive_discovery` | `admit` |
| `route_schema_invalid` | `invalid_route` | `block` |
| `route_secret_unsafe` | `unsafe_route` | `block` |
| `route_control_neutral` | `neutral_control` | `do-not-admit` |

## Family Definition

- Schema: `bedc-quality-lab:discovery-gated-transformer.family-definition`
- Owner: `reports/canonical/discovery-gated-transformer.json:$`
- Hardgate: `pass`
- Claim status: `definition-recorded`

| group | pointers |
| --- | --- |
| `architecture` | `3` |
| `objective` | `3` |
| `certificate` | `4` |

## Sidecars

- Claim capsule: `reports/runs/discovery-gated-transformer/claim_capsule.json:$`
- Evidence envelope: `reports/runs/discovery-gated-transformer/evidence_envelope.json:$`
- Mechanism NameCert: `reports/runs/discovery-gated-transformer/mechanism_namecert.json:$`
- Jet certificate: `reports/runs/discovery-gated-transformer/jet_certificate.json:$`
- Jet hardgate: `reports/canonical/discovery-gated-transformer.json:$.hardgate`
- Discovery map signal: `reports/canonical/discovery-gated-transformer.json:$.discovery_map_signal`
