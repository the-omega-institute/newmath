# Gap-Head MechanismNameCert Candidate

- Artifact: `bedc-quality-lab:gap-head-mechanism-namecert`
- JSON: `reports/gap_head_mechanism_namecert.json`
- Candidate: `MechanismNameCertCandidate:gap-head-on-h`
- Target classifier: `gap-head-on-h`
- Candidate mechanism: `unresolved`
- Full vs score plus margin: `separated`
- Mechanism closure debt: `open`
- Mechanism spec closure: `partial`
- Mechanism ledger pointer: `$.ledger_policy.mechanism_closure_debt`
- Mechanism closure pointer: `$.closure_status.mechanism_spec`
- D5-M ready: `False`

## Scope Seal

- not a formal BEDC NameCert
- not Lean verification
- not a paper closurestatus
- not mechanism theorem closure

## Closure Rows

| field | status | pointer |
| --- | --- | --- |
| `name` | `present` | `$.name` |
| `target_classifier` | `closed` | `$.target_classifier` |
| `source_spec` | `closed` | `$.source_spec` |
| `mechanism_spec` | `partial` | `$.mechanism_spec` |
| `intervention_spec` | `closed` | `$.intervention_spec` |
| `ablation_spec` | `closed` | `$.ablation_spec` |
| `stability_spec` | `closed` | `$.stability_spec` |
| `ledger_policy` | `open` | `$.ledger_policy` |
| `closure_status` | `closed` | `$.closure_status` |
