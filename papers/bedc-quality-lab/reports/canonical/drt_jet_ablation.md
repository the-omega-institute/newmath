# DRT Jet Ablation

- schema_id: `bedc-quality-lab:discovery-regularized-training:jet-sidecar`
- owner_artifact_id: `bedc-quality-lab:discovery-regularized-training`
- owner_pointer: `reports/canonical/discovery-regularized-training.json:$.jet_ablation`
- protocol_pointer: `reports/canonical/discovery-regularized-training.json:$.jet_loss_protocol`
- status: `pass`

| arm | disabled terms | gain pointer |
| --- | --- | --- |
| `full_drt_jet` | `` | `reports/canonical/discovery-regularized-training.json:$.jet_loss_surface.by_arm.DGT_full` |
| `without_jet` | `jet` | `reports/canonical/discovery-regularized-training.json:$.jet_loss_surface.by_arm.DGT_without_jet_loss` |
| `matched_random_jet` | `certificate,witness` | `reports/canonical/discovery-regularized-training.json:$.jet_loss_surface.by_arm.matched_random_structural_control` |
| `shortcut_witness_flip` | `shortcut_control` | `reports/canonical/discovery-regularized-training.json:$.jet_loss_surface.metrics.shortcut_reduction_fraction` |
