# Discovery Negative Witness Summary

- Generated at: `2026-06-04T11:04:50.081457+00:00`
- Status: `pointer-only`
- Audit: `pass`
- Rows: `12`

| negative id | verdict | reason | ledger | discovery map | witness | claim verdict | audit |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `dn:gap-head-ablation` | `negative_discovery` | `discovery-level-DN` | `reports/canonical/gap-head-ablation.json:$.hardgate.status` | `reports/canonical/discovery_map.json:$.rows[4]` | `None` | `None` | `pass` |
| `dn:certificate-guided-training` | `negative_discovery` | `discovery-level-DN` | `reports/canonical/certificate-guided-training.json:$.result.status` | `reports/canonical/discovery_map.json:$.rows[7]` | `None` | `None` | `pass` |
| `dn:certificate-guided-discovery` | `negative_discovery` | `discovery-level-DN` | `reports/canonical/certificate-guided-discovery.json:$.positive_discovery` | `reports/canonical/discovery_map.json:$.rows[8]` | `None` | `None` | `pass` |
| `dn:spectral-ablation-hinge` | `negative_discovery` | `discovery-level-DN` | `reports/canonical/spectral-ablation-hinge.json:$.negative_control_summary.treatment_better_than_all_controls` | `reports/canonical/discovery_map.json:$.rows[10]` | `None` | `None` | `pass` |
| `witness:classifier_surface_delta_zero` | `ledger_only_hardening_not_ready` | `no-classifier-shift` | `reports/canonical/discovery_negative_witnesses.json:$.witnesses[0]` | `None` | `reports/canonical/discovery_negative_witnesses.json:$.witnesses[0]` | `reports/canonical/claim_verdicts.jsonl:11` | `pass` |
| `witness:matched_control_positive` | `ledger_only_hardening_not_ready` | `control-unresolved` | `reports/canonical/discovery_negative_witnesses.json:$.witnesses[1]` | `None` | `reports/canonical/discovery_negative_witnesses.json:$.witnesses[1]` | `reports/canonical/claim_verdicts.jsonl:12` | `pass` |
| `witness:hidden_debt_positive` | `demoted_audit_tradeoff` | `audit-improvement-tradeoff` | `reports/canonical/discovery_negative_witnesses.json:$.witnesses[2]` | `None` | `reports/canonical/discovery_negative_witnesses.json:$.witnesses[2]` | `reports/canonical/claim_verdicts.jsonl:13` | `pass` |
| `witness:cost_protocol_missing` | `rejected_hidden_debt` | `malformed-evidence` | `reports/canonical/discovery_negative_witnesses.json:$.witnesses[3]` | `None` | `reports/canonical/discovery_negative_witnesses.json:$.witnesses[3]` | `reports/canonical/claim_verdicts.jsonl:14` | `pass` |
| `witness:scorecard_not_ready` | `ledger_only_hardening_not_ready` | `scorecard-not-ready` | `reports/canonical/discovery_negative_witnesses.json:$.witnesses[4]` | `None` | `reports/canonical/discovery_negative_witnesses.json:$.witnesses[4]` | `reports/canonical/claim_verdicts.jsonl:15` | `pass` |
| `witness:forbidden_inference_column` | `rejected_scope_laundering` | `forbidden-overclaim` | `reports/canonical/discovery_negative_witnesses.json:$.witnesses[5]` | `None` | `reports/canonical/discovery_negative_witnesses.json:$.witnesses[5]` | `reports/canonical/claim_verdicts.jsonl:16` | `pass` |
| `witness:benefit_debt_tradeoff` | `demoted_audit_tradeoff` | `audit-improvement-tradeoff` | `reports/canonical/discovery_negative_witnesses.json:$.witnesses[6]` | `None` | `reports/canonical/discovery_negative_witnesses.json:$.witnesses[6]` | `reports/canonical/claim_verdicts.jsonl:17` | `pass` |
| `witness:fresh_claim_downgrade` | `demoted_audit_tradeoff` | `audit-improvement-tradeoff` | `reports/canonical/discovery_negative_witnesses.json:$.witnesses[7]` | `None` | `reports/canonical/discovery_negative_witnesses.json:$.witnesses[7]` | `reports/canonical/claim_verdicts.jsonl:18` | `pass` |
