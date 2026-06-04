# Claim Graph

- Generated at: `2026-06-04T16:07:55.096198+00:00`
- Status: `pointer-only`
- Nodes: `66`

| node | type | source | depends on |
| --- | --- | --- | --- |
| `raw:mixing-family-sweep` | `raw_evidence` | `reports/canonical/mixing-family-sweep.json:$.coverage_item.debt_item` |  |
| `projected:mixing-family-sweep` | `projected_discovery` | `reports/canonical/discovery_map.json:$.rows[0]` | `raw:mixing-family-sweep` |
| `raw:anisotropic-ou-sweep` | `raw_evidence` | `reports/canonical/anisotropic-ou-sweep.json:$.transition_debt_by_grid` |  |
| `projected:anisotropic-ou-sweep` | `projected_discovery` | `reports/canonical/discovery_map.json:$.rows[1]` | `raw:anisotropic-ou-sweep` |
| `raw:gap-head-on-h` | `raw_evidence` | `reports/canonical/gap-head-on-h.json:$.treatment_verdict.positive` |  |
| `projected:gap-head-on-h` | `projected_discovery` | `reports/canonical/discovery_map.json:$.rows[2]` | `raw:gap-head-on-h` |
| `raw:gap-head-discovery` | `raw_evidence` | `reports/canonical/gap-head-discovery.json:$.positive_discovery` |  |
| `projected:gap-head-discovery` | `projected_discovery` | `reports/canonical/discovery_map.json:$.rows[3]` | `raw:gap-head-discovery` |
| `raw:gap-head-ablation` | `raw_evidence` | `reports/canonical/negative_discovery_reports.json:$.rows[0]` |  |
| `projected:gap-head-ablation` | `projected_discovery` | `reports/canonical/discovery_map.json:$.rows[4]` | `raw:gap-head-ablation` |
| `raw:gap-head-threshold-frontier` | `raw_evidence` | `reports/canonical/gap-head-threshold-frontier.json:$` |  |
| `projected:gap-head-threshold-frontier` | `projected_discovery` | `reports/canonical/discovery_map.json:$.rows[5]` | `raw:gap-head-threshold-frontier` |
| `raw:gap-head-transfer-atlas` | `raw_evidence` | `reports/canonical/gap_head_transfer_atlas.json:$.multi_surface_d5_o.decision` |  |
| `projected:gap-head-transfer-atlas` | `projected_discovery` | `reports/canonical/discovery_map.json:$.rows[6]` | `raw:gap-head-transfer-atlas` |
| `raw:gap-head-attribution-capsule` | `raw_evidence` | `reports/canonical/gap_head_attribution_capsule.json:$.d5_m` |  |
| `projected:gap-head-attribution-capsule` | `projected_discovery` | `reports/canonical/discovery_map.json:$.rows[7]` | `raw:gap-head-attribution-capsule` |
| `raw:nongaussian-distribution-sweep` | `raw_evidence` | `reports/canonical/nongaussian-distribution-sweep.json:$.negative_result_ledger` |  |
| `projected:nongaussian-distribution-sweep` | `projected_discovery` | `reports/canonical/discovery_map.json:$.rows[8]` | `raw:nongaussian-distribution-sweep` |
| `raw:certificate-guided-training` | `raw_evidence` | `reports/canonical/certificate-guided-training.json:$.arm_protocol.compat_roles.after` |  |
| `projected:certificate-guided-training` | `projected_discovery` | `reports/canonical/discovery_map.json:$.rows[9]` | `raw:certificate-guided-training` |
| `raw:certificate-guided-discovery` | `raw_evidence` | `reports/canonical/negative_discovery_reports.json:$.rows[2]` |  |
| `projected:certificate-guided-discovery` | `projected_discovery` | `reports/canonical/discovery_map.json:$.rows[10]` | `raw:certificate-guided-discovery` |
| `raw:sigreg-training-proxy` | `raw_evidence` | `reports/canonical/sigreg-training-proxy.json:$.d1_evidence.debt_delta` |  |
| `projected:sigreg-training-proxy` | `projected_discovery` | `reports/canonical/discovery_map.json:$.rows[11]` | `raw:sigreg-training-proxy` |
| `raw:spectral-ablation-hinge` | `raw_evidence` | `reports/canonical/negative_discovery_reports.json:$.rows[3]` |  |
| `projected:spectral-ablation-hinge` | `projected_discovery` | `reports/canonical/discovery_map.json:$.rows[12]` | `raw:spectral-ablation-hinge` |
| `raw:dimension-mismatch-debt-transfer` | `raw_evidence` | `reports/canonical/dimension-mismatch-debt-transfer.json:$.dimension_mismatch_debt_transfer.effective_level` |  |
| `projected:dimension-mismatch-debt-transfer` | `projected_discovery` | `reports/canonical/discovery_map.json:$.rows[13]` | `raw:dimension-mismatch-debt-transfer` |
| `negative-witness:classifier_surface_delta_zero` | `negative_witness` | `reports/canonical/discovery_negative_witnesses.json:$.witnesses[0]` |  |
| `negative-witness:matched_control_positive` | `negative_witness` | `reports/canonical/discovery_negative_witnesses.json:$.witnesses[1]` |  |
| `negative-witness:hidden_debt_positive` | `negative_witness` | `reports/canonical/discovery_negative_witnesses.json:$.witnesses[2]` |  |
| `negative-witness:cost_protocol_missing` | `negative_witness` | `reports/canonical/discovery_negative_witnesses.json:$.witnesses[3]` |  |
| `negative-witness:scorecard_not_ready` | `negative_witness` | `reports/canonical/discovery_negative_witnesses.json:$.witnesses[4]` |  |
| `negative-witness:forbidden_inference_column` | `negative_witness` | `reports/canonical/discovery_negative_witnesses.json:$.witnesses[5]` |  |
| `negative-witness:benefit_debt_tradeoff` | `negative_witness` | `reports/canonical/discovery_negative_witnesses.json:$.witnesses[6]` |  |
| `negative-witness:fresh_claim_downgrade` | `negative_witness` | `reports/canonical/discovery_negative_witnesses.json:$.witnesses[7]` |  |
| `revocation:mixing-family-sweep` | `revocation` | `reports/canonical/discovery_map.json:$.rows[0].discovery_level` | `projected:mixing-family-sweep` |
| `revocation:anisotropic-ou-sweep` | `revocation` | `reports/canonical/discovery_map.json:$.rows[1].discovery_level` | `projected:anisotropic-ou-sweep` |
| `revocation:nongaussian-distribution-sweep` | `revocation` | `reports/canonical/discovery_map.json:$.rows[8].discovery_level` | `projected:nongaussian-distribution-sweep` |
| `revocation:sigreg-training-proxy` | `revocation` | `reports/canonical/discovery_map.json:$.rows[11].discovery_level` | `projected:sigreg-training-proxy` |
| `revocation:witness:hidden_debt_positive` | `revocation` | `reports/canonical/discovery_negative_witnesses.json:$.witnesses[2]` | `negative-witness:hidden_debt_positive` |
| `revocation:witness:benefit_debt_tradeoff` | `revocation` | `reports/canonical/discovery_negative_witnesses.json:$.witnesses[6]` | `negative-witness:benefit_debt_tradeoff` |
| `revocation:witness:fresh_claim_downgrade` | `revocation` | `reports/canonical/discovery_negative_witnesses.json:$.witnesses[7]` | `negative-witness:fresh_claim_downgrade` |
| `mechanism:gap-head-mechanism-namecert` | `mechanism_certificate` | `reports/gap_head_mechanism_namecert.json:$` |  |
| `terminal:mixing-family-sweep` | `terminal_claim` | `reports/canonical/claim_verdicts.jsonl:$.lines[0]` | `revocation:mixing-family-sweep` |
| `terminal:anisotropic-ou-sweep` | `terminal_claim` | `reports/canonical/claim_verdicts.jsonl:$.lines[1]` | `revocation:anisotropic-ou-sweep` |
| `terminal:gap-head-on-h` | `terminal_claim` | `reports/canonical/claim_verdicts.jsonl:$.lines[2]` | `projected:gap-head-on-h` |
| `terminal:gap-head-discovery` | `terminal_claim` | `reports/canonical/claim_verdicts.jsonl:$.lines[3]` | `projected:gap-head-discovery` |
| `terminal:gap-head-ablation` | `terminal_claim` | `reports/canonical/claim_verdicts.jsonl:$.lines[4]` | `projected:gap-head-ablation` |
| `terminal:gap-head-threshold-frontier` | `terminal_claim` | `reports/canonical/claim_verdicts.jsonl:$.lines[5]` | `projected:gap-head-threshold-frontier` |
| `terminal:gap-head-transfer-atlas` | `terminal_claim` | `reports/canonical/claim_verdicts.jsonl:$.lines[6]` | `projected:gap-head-transfer-atlas` |
| `terminal:gap-head-attribution-capsule` | `terminal_claim` | `reports/canonical/claim_verdicts.jsonl:$.lines[7]` | `projected:gap-head-attribution-capsule` |
| `terminal:nongaussian-distribution-sweep` | `terminal_claim` | `reports/canonical/claim_verdicts.jsonl:$.lines[8]` | `revocation:nongaussian-distribution-sweep` |
| `terminal:certificate-guided-training` | `terminal_claim` | `reports/canonical/claim_verdicts.jsonl:$.lines[9]` | `projected:certificate-guided-training` |
| `terminal:certificate-guided-discovery` | `terminal_claim` | `reports/canonical/claim_verdicts.jsonl:$.lines[10]` | `projected:certificate-guided-discovery` |
| `terminal:sigreg-training-proxy` | `terminal_claim` | `reports/canonical/claim_verdicts.jsonl:$.lines[11]` | `revocation:sigreg-training-proxy` |
| `terminal:spectral-ablation-hinge` | `terminal_claim` | `reports/canonical/claim_verdicts.jsonl:$.lines[12]` | `projected:spectral-ablation-hinge` |
| `terminal:dimension-mismatch-debt-transfer` | `terminal_claim` | `reports/canonical/claim_verdicts.jsonl:$.lines[13]` | `projected:dimension-mismatch-debt-transfer` |
| `terminal:witness:classifier_surface_delta_zero` | `terminal_claim` | `reports/canonical/claim_verdicts.jsonl:$.lines[14]` | `negative-witness:classifier_surface_delta_zero` |
| `terminal:witness:matched_control_positive` | `terminal_claim` | `reports/canonical/claim_verdicts.jsonl:$.lines[15]` | `negative-witness:matched_control_positive` |
| `terminal:witness:hidden_debt_positive` | `terminal_claim` | `reports/canonical/claim_verdicts.jsonl:$.lines[16]` | `revocation:witness:hidden_debt_positive` |
| `terminal:witness:cost_protocol_missing` | `terminal_claim` | `reports/canonical/claim_verdicts.jsonl:$.lines[17]` | `negative-witness:cost_protocol_missing` |
| `terminal:witness:scorecard_not_ready` | `terminal_claim` | `reports/canonical/claim_verdicts.jsonl:$.lines[18]` | `negative-witness:scorecard_not_ready` |
| `terminal:witness:forbidden_inference_column` | `terminal_claim` | `reports/canonical/claim_verdicts.jsonl:$.lines[19]` | `negative-witness:forbidden_inference_column` |
| `terminal:witness:benefit_debt_tradeoff` | `terminal_claim` | `reports/canonical/claim_verdicts.jsonl:$.lines[20]` | `revocation:witness:benefit_debt_tradeoff` |
| `terminal:witness:fresh_claim_downgrade` | `terminal_claim` | `reports/canonical/claim_verdicts.jsonl:$.lines[21]` | `revocation:witness:fresh_claim_downgrade` |

## Hardgates

- `CG-HG1`: `pass` accepted_positive_discovery terminals trace to raw_evidence through projected_discovery
- `CG-HG2`: `pass` D5-O projected discoveries explicitly record whether a D5-M mechanism node exists
- `CG-HG3`: `pass` raw_evidence nodes are never terminal_claim nodes
- `CG-HG4`: `pass` claim verdict rows carry identity-only terminal graph foreign keys
- `CG-HG5`: `pass` all node source_pointer values resolve
