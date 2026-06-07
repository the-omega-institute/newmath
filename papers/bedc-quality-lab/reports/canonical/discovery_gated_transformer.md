# Discovery-Gated Transformer

- Generated at: `2026-06-07T19:37:53.443698+00:00`
- Model id: `discovery_gated_transformer`
- Prototype status: `prototype-candidate`
- Hardgate contract: `reports/canonical/new_model_hardgates.json:$.gates`
- Claim capsule: `reports/runs/discovery_gated_transformer/claim_capsule.json:$`

## Sequence Task

- Task: `edge_agreement_sequence`
- Train split: `reports/runs/discovery_gated_transformer/summary.json:$.splits.train`

## Surface Delta

| surface | candidate accuracy | best baseline accuracy |
| --- | --- | --- |
| `id_length_6` | `1.0` | `0.5` |
| `ood_length_8` | `1.0` | `0.5` |
| `ood_length_10` | `1.0` | `0.5` |
| `stress_repeat_edge` | `1.0` | `0.5` |

## Hardgate Instances

| gate | status | evidence | contract |
| --- | --- | --- | --- |
| `NEW-MODEL-HG1` | `pass` | `reports/canonical/discovery_gated_transformer.json:$.model_id` | `reports/canonical/new_model_hardgates.json:$.gates.NEW-MODEL-HG1` |
| `NEW-MODEL-HG2` | `pass` | `reports/canonical/discovery_gated_transformer.json:$.sequence_task_grid` | `reports/canonical/new_model_hardgates.json:$.gates.NEW-MODEL-HG2` |
| `NEW-MODEL-HG3` | `pass` | `reports/canonical/discovery_gated_transformer.json:$.training_evidence` | `reports/canonical/new_model_hardgates.json:$.gates.NEW-MODEL-HG3` |
| `NEW-MODEL-HG4` | `pass` | `reports/canonical/discovery_gated_transformer.json:$.claim_capsule_ref` | `reports/canonical/new_model_hardgates.json:$.gates.NEW-MODEL-HG4` |
| `NEW-MODEL-HG5` | `pass` | `reports/canonical/discovery_gated_transformer.json:$.training_evidence.evidence_envelope_pointer` | `reports/canonical/new_model_hardgates.json:$.gates.NEW-MODEL-HG5` |
| `NEW-MODEL-HG6` | `pass` | `reports/canonical/discovery_gated_transformer.json:$.training_evidence.cost_protocol_pointer` | `reports/canonical/new_model_hardgates.json:$.gates.NEW-MODEL-HG6` |
| `NEW-MODEL-HG7` | `pass` | `reports/canonical/discovery_gated_transformer.json:$.baselines.parameter_control` | `reports/canonical/new_model_hardgates.json:$.gates.NEW-MODEL-HG7` |
| `NEW-MODEL-HG8` | `pass` | `reports/canonical/discovery_gated_transformer.json:$.baselines.compute_control` | `reports/canonical/new_model_hardgates.json:$.gates.NEW-MODEL-HG8` |
| `NEW-MODEL-HG9` | `pass` | `reports/canonical/discovery_gated_transformer.json:$.baselines.matched_random` | `reports/canonical/new_model_hardgates.json:$.gates.NEW-MODEL-HG9` |
| `NEW-MODEL-HG10` | `pass` | `reports/canonical/discovery_gated_transformer.json:$.sequence_task_grid.eval` | `reports/canonical/new_model_hardgates.json:$.gates.NEW-MODEL-HG10` |
| `NEW-MODEL-HG11` | `pass` | `reports/canonical/discovery_gated_transformer.json:$.net_positive_signal` | `reports/canonical/new_model_hardgates.json:$.gates.NEW-MODEL-HG11` |
| `NEW-MODEL-HG12` | `pass` | `reports/canonical/discovery_gated_transformer.json:$.training_evidence.false_ledger_rate` | `reports/canonical/new_model_hardgates.json:$.gates.NEW-MODEL-HG12` |
| `NEW-MODEL-HG13` | `pass` | `reports/canonical/discovery_gated_transformer.json:$.training_evidence.benefit_signal` | `reports/canonical/new_model_hardgates.json:$.gates.NEW-MODEL-HG13` |
| `NEW-MODEL-HG14` | `pass` | `reports/canonical/discovery_gated_transformer.json:$.training_evidence.loss_decrease` | `reports/canonical/new_model_hardgates.json:$.gates.NEW-MODEL-HG14` |
| `NEW-MODEL-HG15` | `pass` | `reports/canonical/discovery_gated_transformer.json:$.net_positive_signal.quality_q_ci_low` | `reports/canonical/new_model_hardgates.json:$.gates.NEW-MODEL-HG15` |
| `NEW-MODEL-HG16` | `pass` | `reports/canonical/discovery_gated_transformer.json:$.classifier_surface_delta` | `reports/canonical/new_model_hardgates.json:$.gates.NEW-MODEL-HG16` |
| `NEW-MODEL-HG17` | `pass` | `reports/canonical/discovery_gated_transformer.json:$.forbidden_claim_term_audit` | `reports/canonical/new_model_hardgates.json:$.gates.NEW-MODEL-HG17` |
| `NEW-MODEL-HG18` | `pass` | `reports/canonical/discovery_gated_transformer.json:$.revocation_rows` | `reports/canonical/new_model_hardgates.json:$.gates.NEW-MODEL-HG18` |
| `NEW-MODEL-HG19` | `pass` | `reports/canonical/discovery_gated_transformer.json:$.discovery_map_signal` | `reports/canonical/new_model_hardgates.json:$.gates.NEW-MODEL-HG19` |
| `NEW-MODEL-HG20` | `pass` | `reports/canonical/discovery_gated_transformer.json:$.not_claimed` | `reports/canonical/new_model_hardgates.json:$.gates.NEW-MODEL-HG20` |
