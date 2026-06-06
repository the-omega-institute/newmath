# Discovery-Gated Transformer

- Generated at: `2026-06-05T07:13:11.713087+00:00`
- Artifact: `bedc-quality-lab:discovery-gated-transformer`
- Schema: `bedc-quality-lab:discovery-gated-transformer`
- Status: `present-but-fail-closed`
- Model id: `discovery_gated_transformer`
- Owner pointer: `reports/canonical/discovery_gated_transformer.json:$`

## Components

| component | owner pointer | evidence pointer | pointer state |
| --- | --- | --- | --- |
| `backbone` | `reports/canonical/ledger-aware-transformer.json:$` | `reports/canonical/ledger-aware-transformer.json:$.run_artifacts` | `present-but-fail-closed` |
| `certificate_gated_attention` | `reports/canonical/certificate-gated-attention.json:$` | `reports/canonical/certificate-gated-attention.json:$.certificate_gate_summary` | `present-but-fail-closed` |
| `gap_ledger_route_mechanism_scope_heads` | `reports/canonical/gap_head_attribution_capsule.json:$` | `reports/canonical/gap_head_attribution_capsule.json:$.mechanism_evidence` | `present-but-fail-closed` |
| `discovery_regularized_training` | `reports/canonical/discovery-regularized-training.json:$` | `reports/canonical/discovery-regularized-training.json:$.torch_training_evidence` | `present-but-fail-closed` |
| `audit` | `reports/canonical/negative_discovery_reports.json:$` | `reports/canonical/negative_discovery_reports.json:$.rows` | `present-but-fail-closed` |
| `output_bundle` | `reports/canonical/discovery_gated_transformer.json:$.public_index_pointers` | `reports/canonical/discovery_gated_transformer.json:$.downstream_scope` | `present-but-fail-closed` |

## DGT Hardgate Slots

| gate | component | evidence | control | ablation | registry | state | failure mode |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `DGT-HG1` | `$.component_descriptors.backbone` | `reports/canonical/ledger-aware-transformer.json:$.metrics.UER` | `reports/canonical/ledger-aware-transformer.json:$.control_protocol` | `None` | `reports/canonical/new_model_hardgates.json:$.gates.NEW-MODEL-HG11` | `present-but-fail-closed` | `missing-evidence-pointer` |
| `DGT-HG2` | `$.component_descriptors.backbone` | `reports/canonical/discovery-gated-nas.json:$.matched_baseline_control.parameter_matched` | `reports/canonical/discovery-gated-nas.json:$.matched_baseline_control` | `None` | `reports/canonical/new_model_hardgates.json:$.gates.NEW-MODEL-HG7` | `present-but-fail-closed` | `missing-control-pointer` |
| `DGT-HG3` | `$.component_descriptors.backbone` | `reports/canonical/discovery-gated-nas.json:$.matched_baseline_control.compute_matched` | `reports/canonical/discovery-gated-nas.json:$.matched_baseline_control` | `None` | `reports/canonical/new_model_hardgates.json:$.gates.NEW-MODEL-HG8` | `present-but-fail-closed` | `missing-control-pointer` |
| `DGT-HG4` | `$.component_descriptors.backbone` | `reports/canonical/ledger-aware-transformer.json:$.metrics.UER` | `reports/canonical/ledger-aware-transformer.json:$.matched_random_control` | `None` | `reports/canonical/new_model_hardgates.json:$.gates.NEW-MODEL-HG9` | `present-but-fail-closed` | `missing-control-pointer` |
| `DGT-HG5` | `$.component_descriptors.audit` | `reports/canonical/ledger-aware-transformer.json:$.metrics.FalseLedgerRate` | `reports/canonical/ledger-aware-transformer.json:$.matched_random_control` | `None` | `reports/canonical/new_model_hardgates.json:$.gates.NEW-MODEL-HG12` | `present-but-fail-closed` | `missing-evidence-pointer` |
| `DGT-HG6` | `$.component_descriptors.audit` | `reports/canonical/discovery-gated-nas.json:$.search_objective_summary.selected_candidate.classifier_shift_count` | `None` | `None` | `reports/canonical/new_model_hardgates.json:$.gates.NEW-MODEL-HG16` | `present-but-fail-closed` | `missing-control-pointer` |
| `DGT-HG7` | `$.component_descriptors.audit` | `reports/canonical/gap_head_transfer_atlas.json:$.multi_surface_d5_o` | `reports/canonical/gap_head_transfer_atlas.json:$.config.control_arm` | `None` | `reports/canonical/new_model_hardgates.json:$.gates.NEW-MODEL-HG10` | `present-but-fail-closed` | `missing-surface-pointer` |
| `DGT-HG8` | `$.component_descriptors.certificate_gated_attention` | `reports/canonical/certificate-gated-attention.json:$.certificate_gate_summary` | `reports/canonical/certificate-gated-attention.json:$.matched_random_control` | `reports/canonical/certificate-gated-attention.json:$.discovery_map_signal` | `reports/canonical/new_model_hardgates.json:$.gates.NEW-MODEL-HG19` | `present-but-fail-closed` | `missing-ablation-pointer` |
| `DGT-HG9` | `$.component_descriptors.discovery_regularized_training` | `reports/canonical/discovery-regularized-training.json:$.torch_training_evidence` | `reports/canonical/discovery-regularized-training.json:$.matched_random_control` | `reports/canonical/discovery-regularized-training.json:$.training_loop_trace` | `reports/canonical/new_model_hardgates.json:$.gates.NEW-MODEL-HG19` | `present-but-fail-closed` | `missing-ablation-pointer` |
| `DGT-HG10` | `$.component_descriptors.gap_ledger_route_mechanism_scope_heads` | `reports/canonical/gap-head-ablation.json:$.factor_attribution` | `reports/canonical/gap-head-ablation.json:$.control_protocol` | `reports/canonical/gap-head-ablation.json:$.hardgate` | `reports/canonical/new_model_hardgates.json:$.gates.NEW-MODEL-HG19` | `present-but-fail-closed` | `missing-ablation-pointer` |
| `DGT-HG11` | `$.component_descriptors.gap_ledger_route_mechanism_scope_heads` | `reports/canonical/gap_head_mechanism_namecert.json:$.mechanism_spec` | `reports/canonical/gap_head_mechanism_namecert.json:$.source_spec.scope_seal` | `reports/canonical/gap_head_attribution_capsule.json:$.a4_hardgates` | `reports/canonical/new_model_hardgates.json:$.gates.NEW-MODEL-HG19` | `present-but-fail-closed` | `missing-ablation-pointer` |
| `DGT-HG12` | `$.component_descriptors.output_bundle` | `$.downstream_scope` | `None` | `None` | `reports/canonical/new_model_hardgates.json:$.gates.NEW-MODEL-HG20` | `present-but-fail-closed` | `missing-terminal-claim-pointer` |

- Overall state: `present-but-fail-closed`
- Downstream scope: `$.downstream_scope`
