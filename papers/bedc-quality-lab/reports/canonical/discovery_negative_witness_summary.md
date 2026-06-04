# Discovery Negative Witness Summary

- Generated at: `2026-06-04T07:02:53.666685+00:00`
- Status: `pointer-only`
- Audit: `pass`
- Rows: `12`

| negative id | verdict | reason | ledger | discovery map | witness | claim verdict | audit |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `dn:gap-head-ablation` | `negative_discovery` | `discovery-level-DN` | `reports/canonical/gap-head-ablation.json:$.hardgate.status` | `reports/canonical/discovery_map.json:$.rows[4]` | `None` | `None` | `pass` |
| `dn:certificate-guided-training` | `negative_discovery` | `discovery-level-DN` | `reports/canonical/certificate-guided-training.json:$.result.status` | `reports/canonical/discovery_map.json:$.rows[8]` | `None` | `None` | `pass` |
| `dn:certificate-guided-discovery` | `negative_discovery` | `discovery-level-DN` | `reports/canonical/certificate-guided-discovery.json:$.positive_discovery` | `reports/canonical/discovery_map.json:$.rows[9]` | `None` | `None` | `pass` |
| `dn:spectral-ablation-hinge` | `negative_discovery` | `discovery-level-DN` | `reports/canonical/spectral-ablation-hinge.json:$.negative_control_summary.treatment_better_than_all_controls` | `reports/canonical/discovery_map.json:$.rows[10]` | `None` | `None` | `pass` |
| `witness:classifier_surface_delta_zero` | `negative_discovery` | `no-classifier-shift` | `reports/canonical/discovery_negative_witnesses.json:$.witnesses[0]` | `None` | `reports/canonical/discovery_negative_witnesses.json:$.witnesses[0]` | `reports/canonical/claim_verdicts.jsonl:10` | `pass` |
| `witness:matched_control_positive` | `negative_discovery` | `control-unresolved` | `reports/canonical/discovery_negative_witnesses.json:$.witnesses[1]` | `None` | `reports/canonical/discovery_negative_witnesses.json:$.witnesses[1]` | `reports/canonical/claim_verdicts.jsonl:11` | `pass` |
| `witness:hidden_debt_positive` | `rejected_due_to_hidden_debt` | `audit-improvement-tradeoff` | `reports/canonical/discovery_negative_witnesses.json:$.witnesses[2]` | `None` | `reports/canonical/discovery_negative_witnesses.json:$.witnesses[2]` | `reports/canonical/claim_verdicts.jsonl:12` | `pass` |
| `witness:cost_protocol_missing` | `negative_discovery` | `malformed-evidence` | `reports/canonical/discovery_negative_witnesses.json:$.witnesses[3]` | `None` | `reports/canonical/discovery_negative_witnesses.json:$.witnesses[3]` | `reports/canonical/claim_verdicts.jsonl:13` | `pass` |
| `witness:scorecard_not_ready` | `negative_discovery` | `scorecard-not-ready` | `reports/canonical/discovery_negative_witnesses.json:$.witnesses[4]` | `None` | `reports/canonical/discovery_negative_witnesses.json:$.witnesses[4]` | `reports/canonical/claim_verdicts.jsonl:14` | `pass` |
| `witness:forbidden_inference_column` | `rejected_due_to_scope_laundering` | `forbidden-overclaim` | `reports/canonical/discovery_negative_witnesses.json:$.witnesses[5]` | `None` | `reports/canonical/discovery_negative_witnesses.json:$.witnesses[5]` | `reports/canonical/claim_verdicts.jsonl:15` | `pass` |
| `witness:benefit_debt_tradeoff` | `revoked_due_to_fresh_evidence` | `audit-improvement-tradeoff` | `reports/canonical/discovery_negative_witnesses.json:$.witnesses[6]` | `None` | `reports/canonical/discovery_negative_witnesses.json:$.witnesses[6]` | `reports/canonical/claim_verdicts.jsonl:16` | `pass` |
| `witness:fresh_claim_downgrade` | `revoked_due_to_fresh_evidence` | `audit-improvement-tradeoff` | `reports/canonical/discovery_negative_witnesses.json:$.witnesses[7]` | `None` | `reports/canonical/discovery_negative_witnesses.json:$.witnesses[7]` | `reports/canonical/claim_verdicts.jsonl:17` | `pass` |
