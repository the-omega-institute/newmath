# Discovery-Gated Transformer

- Generated at: `2026-06-09T04:15:58.263169+00:00`
- Schema: `bedc-quality-lab:discovery-gated-transformer`
- Artifact: `bedc-quality-lab:discovery-gated-transformer`
- Model: `discovery-gated-transformer`
- Hardgate: `pass`

## Component Refs

| component | artifact | pointer |
| --- | --- | --- |
| `hardgate_contract` | `reports/canonical/new_model_hardgates.json` | `$.gates` |
| `discovery_gated_nas` | `reports/canonical/discovery-gated-transformer.json` | `$.d5_m_projection` |
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
| `DGT-HG19` | `pass` | `reports/canonical/discovery-gated-transformer.json:$.component_refs.discovery_gated_nas` |
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

## Component Ablation

- Schema: `bedc-quality-lab:discovery-gated-transformer.component-ablation`
- Owner: `reports/canonical/discovery-gated-transformer.json:$.component_ablation`
- Arms: `11`
- Hardgate: `pass`

| arm | component | effect status | claim allowed |
| --- | --- | --- | --- |
| `drop_hardgate_contract` | `hardgate_contract` | `measurable` | `True` |
| `drop_discovery_gated_nas` | `discovery_gated_nas` | `measurable` | `True` |
| `drop_discovery_map` | `discovery_map` | `measurable` | `True` |
| `drop_training_replay` | `training_replay` | `measurable` | `True` |
| `drop_tool_route_evidence` | `tool_route_evidence` | `measurable` | `True` |
| `drop_family_definition` | `family_definition` | `measurable` | `True` |
| `drop_jet_certificate` | `jet_certificate` | `measurable` | `True` |
| `drop_d4_projection` | `d4_projection` | `measurable` | `True` |
| `drop_design_pair` | `discovery_gated_nas` | `measurable` | `True` |
| `drop_evidence_pair` | `tool_route_evidence` | `measurable` | `True` |
| `drop_structural_contracts` | `family_definition` | `measurable` | `True` |

## Operational Robustness

- Owner: `reports/canonical/discovery-gated-transformer.json:$.robustness`
- Readiness: `ready`
- Discovery level: `D5-O`
- LAT evidence: `reports/canonical/ledger-aware-transformer.json:$`

| gate | status | evidence |
| --- | --- | --- |
| `DGT-ROB-HG1` | `pass` | `reports/canonical/discovery-gated-transformer.json:$.robustness.owner_ref` |
| `DGT-ROB-HG2` | `pass` | `reports/canonical/discovery-gated-transformer.json:$.d4_projection` |
| `DGT-ROB-HG3` | `pass` | `reports/canonical/discovery-gated-transformer.json:$.component_ablation.hardgate` |
| `DGT-ROB-HG4` | `pass` | `reports/canonical/discovery-gated-transformer.json:$.robustness.source_evidence.ledger_aware_transformer` |
| `DGT-ROB-HG5` | `pass` | `reports/canonical/discovery-gated-transformer.json:$.robustness.source_evidence.model_comparison` |
| `DGT-ROB-HG6` | `pass` | `reports/canonical/discovery-gated-transformer.json:$.robustness.source_artifacts` |
| `DGT-ROB-HG7` | `pass` | `reports/canonical/discovery-gated-transformer.json:$.robustness.not_claimed` |
| `DGT-ROB-HG8` | `pass` | `reports/canonical/discovery-gated-transformer.json:$.robustness.forbidden_claim_term_audit` |

## D4 Projection

- Readiness: `ready`
- Discovery level: `D4`
- Failed gate: `None`

| gate | status | evidence |
| --- | --- | --- |
| `PROJ-HG1` | `pass` | `reports/canonical/discovery-gated-transformer.json:$.hardgate` |
| `PROJ-HG2` | `pass` | `reports/canonical/discovery-gated-transformer.json:$.tool_route_evidence.hardgate` |
| `PROJ-HG3` | `pass` | `reports/canonical/discovery-gated-transformer.json:$.tool_route_evidence.net_positive_signal` |
| `PROJ-HG4` | `pass` | `reports/canonical/discovery-gated-transformer.json:$.tool_route_evidence.classifier_surface_delta` |
| `PROJ-HG5` | `pass` | `reports/canonical/discovery-gated-transformer.json:$.family_definition.hardgate` |
| `PROJ-HG6` | `pass` | `reports/canonical/discovery-gated-transformer.json:$.claim_capsule_ref` |
| `PROJ-HG7` | `pass` | `reports/canonical/discovery-gated-transformer.json:$.not_claimed` |
| `PROJ-HG8` | `pass` | `reports/canonical/discovery-gated-transformer.json:$.forbidden_claim_term_audit` |
| `PROJ-HG9` | `pass` | `reports/canonical/discovery-gated-transformer.json:$` |
| `PROJ-HG10` | `pass` | `reports/canonical/discovery-gated-transformer.json:$.discovery_map_signal_ref` |

## Bounded Mechanism Projection

- Readiness: `ready`
- Discovery level: `D5-M`
- Failed gate: `None`
- Evidence scope: `bounded-model-prototype`
- Verdict scope: `Core`

| gate | status | evidence |
| --- | --- | --- |
| `D5M-HG1` | `pass` | `reports/canonical/discovery-gated-transformer.json:$.d4_projection` |
| `D5M-HG2` | `pass` | `reports/canonical/discovery-gated-transformer.json:$.mechanism_namecert_ref` |
| `D5M-HG3` | `pass` | `reports/canonical/discovery-gated-transformer.json:$.jet_certificate_ref` |
| `D5M-HG4` | `pass` | `reports/canonical/discovery-gated-transformer.json:$.d5_m_projection.causal_patch_pointer` |
| `D5M-HG5` | `pass` | `reports/canonical/discovery-gated-transformer.json:$.robustness` |
| `D5M-HG6` | `pass` | `reports/canonical/discovery-gated-transformer.json:$.component_ablation` |
| `D5M-HG7` | `pass` | `reports/canonical/discovery-gated-transformer.json:$.d5_m_projection.negative_witness_audit` |
| `D5M-HG8` | `pass` | `reports/canonical/discovery-gated-transformer.json:$.d5_m_projection.forbidden_claim_term_audit` |

## Sidecars

- Claim capsule: `reports/runs/discovery-gated-transformer/claim_capsule.json:$`
- Evidence envelope: `reports/runs/discovery-gated-transformer/evidence_envelope.json:$`
- Mechanism NameCert: `reports/runs/discovery-gated-transformer/mechanism_namecert.json:$`
- Jet certificate: `reports/runs/discovery-gated-transformer/jet_certificate.json:$`
- Jet hardgate: `reports/canonical/discovery-gated-transformer.json:$.hardgate`
- Discovery map signal: `reports/canonical/discovery-gated-transformer.json:$.discovery_map_signal`
