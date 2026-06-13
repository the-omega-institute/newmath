# Discovery-Gated Transformer

- Generated at: `2026-06-13T11:40:35.696577+00:00`
- Schema: `bedc-quality-lab:discovery-gated-transformer`
- Artifact: `bedc-quality-lab:discovery-gated-transformer`
- Model: `discovery-gated-transformer`
- Hardgate: `pass`

## Component Refs

| component | artifact | pointer |
| --- | --- | --- |
| `hardgate_contract` | `reports/canonical/new_model_hardgates.json` | `$.gates` |
| `mechanism_dna` | `reports/canonical/mechanism_dna.json` | `$.rows` |
| `mechanism_namecert` | `reports/canonical/discovery-gated-transformer.json` | `$.mechanism_namecert_ref` |
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
| `DGT-HG6` | `pass` | `reports/canonical/discovery-gated-transformer.json:$.component_refs.mechanism_namecert` |
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
| `DGT-HG19` | `pass` | `reports/canonical/discovery-gated-transformer.json:$.component_refs.mechanism_dna` |
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
| `drop_mechanism_namecert` | `mechanism_namecert` | `measurable` | `True` |
| `drop_discovery_map` | `discovery_map` | `measurable` | `True` |
| `drop_training_replay` | `training_replay` | `measurable` | `True` |
| `drop_tool_route_evidence` | `tool_route_evidence` | `measurable` | `True` |
| `drop_family_definition` | `family_definition` | `measurable` | `True` |
| `drop_jet_certificate` | `jet_certificate` | `measurable` | `True` |
| `drop_d4_projection` | `d4_projection` | `measurable` | `True` |
| `drop_mechanism_pair` | `mechanism_namecert` | `measurable` | `True` |
| `drop_evidence_pair` | `tool_route_evidence` | `measurable` | `True` |
| `drop_structural_contracts` | `family_definition` | `measurable` | `True` |

## Operational Robustness

- Owner: `reports/canonical/discovery-gated-transformer.json:$.operational_robustness`
- Readiness: `ready`
- Discovery level: `D5-O`
- LAT evidence: `reports/canonical/ledger-aware-transformer.json:$`

| gate | status | evidence |
| --- | --- | --- |
| `DGT-ROB-HG1` | `pass` | `reports/canonical/discovery-gated-transformer.json:$.operational_robustness.owner_ref` |
| `DGT-ROB-HG2` | `pass` | `reports/canonical/discovery-gated-transformer.json:$.d4_projection` |
| `DGT-ROB-HG3` | `pass` | `reports/canonical/discovery-gated-transformer.json:$.component_ablation.hardgate` |
| `DGT-ROB-HG4` | `pass` | `reports/canonical/discovery-gated-transformer.json:$.operational_robustness.source_evidence.ledger_aware_transformer` |
| `DGT-ROB-HG5` | `pass` | `reports/canonical/discovery-gated-transformer.json:$.operational_robustness.source_evidence.model_comparison` |
| `DGT-ROB-HG6` | `pass` | `reports/canonical/discovery-gated-transformer.json:$.operational_robustness.source_artifacts` |
| `DGT-ROB-HG7` | `pass` | `reports/canonical/discovery-gated-transformer.json:$.operational_robustness.not_claimed` |
| `DGT-ROB-HG8` | `pass` | `reports/canonical/discovery-gated-transformer.json:$.operational_robustness.forbidden_claim_term_audit` |

## D5-O Projection

- Status: `ready`
- Discovery level: `D5-O`
- Source level: `D4`
- Blocked reason: `None`

| gate | status | evidence |
| --- | --- | --- |
| `D5O-HG1` | `pass` | `reports/canonical/high-impact-review.json:$.review_rows[0]` |
| `D5O-HG2` | `pass` | `reports/canonical/discovery-gated-transformer.json:$.d4_projection` |
| `D5O-HG3` | `pass` | `reports/canonical/discovery-gated-transformer.json:$.d5_o_projection.surface_summary` |
| `D5O-HG4` | `pass` | `reports/canonical/discovery-gated-transformer.json:$.d5_o_projection.surface_summary.seed` |
| `D5O-HG5` | `pass` | `reports/canonical/discovery-gated-transformer.json:$.d5_o_projection.surface_summary.threshold_frontier` |
| `D5O-HG6` | `pass` | `reports/canonical/discovery-gated-transformer.json:$.d5_o_projection.evidence_pointers.stronger_matched_random` |
| `D5O-HG7` | `pass` | `reports/canonical/discovery-gated-transformer.json:$.d5_o_projection.boundary_ledger` |
| `D5O-HG8` | `pass` | `reports/canonical/discovery-gated-transformer.json:$.d5_o_projection.not_claimed` |

## D5-M Projection

- Status: `ready`
- Discovery level: `D5-M`
- Evidence scope: `["bounded-design", "toy-model", "theorem-backed", "production-forbidden"]`
- Terminal scope: `Core`
- Blocked reason: `None`

| gate | status | evidence |
| --- | --- | --- |
| `D5M-HG1` | `pass` | `reports/canonical/discovery-gated-transformer.json:$.d5_o_projection` |
| `D5M-HG2` | `pass` | `reports/canonical/discovery-gated-transformer.json:$.d5_m_projection.evidence_scope` |
| `D5M-HG3` | `pass` | `reports/canonical/discovery-gated-transformer.json:$.mechanism_namecert_ref` |
| `D5M-HG4` | `pass` | `reports/canonical/discovery-gated-transformer.json:$.jet_certificate_ref` |
| `D5M-HG5` | `pass` | `reports/canonical/discovery-gated-transformer.json:$.operational_robustness` |
| `D5M-HG6` | `pass` | `reports/canonical/discovery-gated-transformer.json:$.neural_ablation_ref` |
| `D5M-HG7` | `pass` | `reports/canonical/discovery-gated-transformer.json:$.d5_m_projection.negative_witness_pointers.score_margin_shortcut` |
| `D5M-HG8` | `pass` | `reports/canonical/discovery-gated-transformer.json:$.d5_m_projection.negative_witness_pointers.scale_leakage` |
| `D5M-HG9` | `pass` | `reports/canonical/discovery-gated-transformer.json:$.d4_projection.matched_control.control_positive` |
| `D5M-HG10` | `pass` | `reports/canonical/discovery-gated-transformer.json:$.d5_m_projection.forbidden_claim_audit` |

## Scaling Ladder

- Status: `blocked`
- Review status: `review-line-blocked`
- Discovery level: `D5-M`
- Evidence scope: `bounded-model-prototype-scaling`
- Blocked reason: `blocked-by-SCALE-HG2`

| level | state | promotion | evidence |
| --- | --- | --- | --- |
| `L0_toy` | `scoped-boundary` | `scoped-boundary-from-l0-owner-pointer` | `reports/canonical/dgt-l0-controls.json:$.l0_toy_projection` |
| `L1_tiny_sequence` | `blocked` | `blocked-by-l1-boundary-report` | `reports/canonical/discovery-gated-transformer.json:$.scaling_ladder.levels[1].claim_capsule` |
| `L2_char_lm` | `blocked` | `blocked-until-level-local-evidence` | `reports/canonical/discovery-gated-transformer.json:$.scaling_ladder.levels[2].claim_capsule` |
| `L3_byte_lm` | `blocked` | `blocked-until-level-local-evidence` | `reports/canonical/discovery-gated-transformer.json:$.scaling_ladder.levels[3].claim_capsule` |
| `L4_tool_use_toy` | `blocked` | `blocked-until-level-local-evidence` | `reports/canonical/discovery-gated-transformer.json:$.scaling_ladder.levels[4].claim_capsule` |
| `L5_small_world_model` | `blocked` | `blocked-until-level-local-evidence` | `reports/canonical/discovery-gated-transformer.json:$.scaling_ladder.levels[5].claim_capsule` |

| gate | status | evidence |
| --- | --- | --- |
| `SCALE-HG1` | `pass` | `reports/canonical/discovery-gated-transformer.json:$.d5_m_projection` |
| `SCALE-HG2` | `fail` | `reports/canonical/discovery-gated-transformer.json:$.scaling_ladder.levels` |
| `SCALE-HG3` | `fail` | `reports/canonical/discovery-gated-transformer.json:$.scaling_ladder.levels` |
| `SCALE-HG4` | `fail` | `reports/canonical/discovery-gated-transformer.json:$.scaling_ladder.levels` |
| `SCALE-HG5` | `fail` | `reports/canonical/discovery-gated-transformer.json:$.scaling_ladder.boundary_ledger` |
| `SCALE-HG6` | `pass` | `reports/canonical/discovery-gated-transformer.json:$.scaling_ladder.evidence_scope` |

### Scaling Boundary Ledger

| level | status | gate | reason |
| --- | --- | --- | --- |
| `L0_toy` | `failed` | `SCALE-HG5` | `level state not open; promotion status not opened; ladder consumption not open` |
| `L1_tiny_sequence` | `blocked` | `SCALE-HG5` | `blocked by earlier failed level L0_toy` |
| `L2_char_lm` | `blocked` | `SCALE-HG5` | `blocked by earlier failed level L0_toy` |
| `L3_byte_lm` | `blocked` | `SCALE-HG5` | `blocked by earlier failed level L0_toy` |
| `L4_tool_use_toy` | `blocked` | `SCALE-HG5` | `blocked by earlier failed level L0_toy` |
| `L5_small_world_model` | `blocked` | `SCALE-HG5` | `blocked by earlier failed level L0_toy` |

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

## Sidecars

- Claim capsule: `reports/runs/discovery-gated-transformer/claim_capsule.json:$`
- Evidence envelope: `reports/runs/discovery-gated-transformer/evidence_envelope.json:$`
- Mechanism NameCert: `reports/runs/discovery-gated-transformer/mechanism_namecert.json:$`
- Jet certificate: `reports/runs/discovery-gated-transformer/jet_certificate.json:$`
- Jet hardgate: `reports/canonical/discovery-gated-transformer.json:$.hardgate`
- Discovery map signal: `reports/canonical/discovery-gated-transformer.json:$.discovery_map_signal`
