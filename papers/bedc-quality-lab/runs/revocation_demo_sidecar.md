# Revocation Demo Sidecar

Source artifact: `reports/canonical/certificate-guided-discovery.json`
Source generated at: `2026-06-03T08:00:33.187099+00:00`

| Case | Source pointers | Expected predicates | Decision |
| --- | --- | --- | --- |
| `current-no-certified-claim` | `decision`: `reports/canonical/certificate-guided-discovery.json#$.revocation_decision`<br>`ledger`: `reports/canonical/certificate-guided-discovery.json#$.revocation_ledger`<br>`status`: `reports/canonical/certificate-guided-discovery.json#$.main_claim_status`<br>`not_claimed`: `reports/canonical/certificate-guided-discovery.json#$.not_claimed` | `downgraded` = `False`<br>`reason` = `no-certified-claim`<br>`ledger_rows` = `0` | `downgraded` = `False`<br>`reason` = `no-certified-claim`<br>`ledger_rows` = `0` |
| `synthetic-old-positive-tradeoff` | `function`: `bedc_quality_lab/revocation.py::reevaluate_certified_claim`<br>`tradeoff`: `reports/canonical/certificate-guided-discovery.json#$.claim_gate.training_audit_improvement_tradeoff`<br>`fresh_status`: `reports/canonical/certificate-guided-discovery.json#$.main_claim_status`<br>`not_claimed`: `reports/canonical/certificate-guided-discovery.json#$.not_claimed` | `claim_gate.training_audit_improvement_tradeoff` = `True`<br>`downgraded` = `True`<br>`new_status` = `audit-improvement-tradeoff`<br>`ledger_row.event` = `certified-claim-revocation` | `downgraded` = `True`<br>`reason` = `audit-improvement-tradeoff`<br>`ledger_rows` = `1` |

## Not-Claimed Boundary

The current canonical run has no real downgrade.
The synthetic positive transition is a demo harness only and is not a scientific result.
- formal BEDC closure is not claimed by this lab-local runner
- global optimizer behavior is not claimed by this lab-local runner
- positive quality improvement is not claimed unless the paired after-minus-before quality_q CI lower bound is above zero
- positive quality wording is not claimed for debt reduction paired with benefit decline
- positive quality wording is not claimed when the paired quality_q CI lower bound does not clear zero
- positive discovery is not claimed unless classifier surface delta, imported positive_discovery, positive net information, and training positive quality gate all hold
- Current canonical run has no real downgrade.
- Synthetic positive transition is a demo harness only, not a scientific result.
