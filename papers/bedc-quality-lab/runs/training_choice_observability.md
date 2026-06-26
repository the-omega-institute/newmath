# Training Choice Observability

- status: pointer-only
- canonical_role: sidecar_not_in_CANONICAL_REPORTS
- local_schema_id: bedc-quality-lab:training-choice-observability-sidecar
- artifact_id: bedc-quality-lab:training-choice-observability

## Classifications

| arm | classification | ledger status | HG-TCO failed | learned AUROC | matched AUROC | learned reduction | matched reduction |
| --- | --- | --- | --- | --- | --- | --- | --- |
| deterministic_standardization_reference | reference-only | partial | none | mean=0.780, ci95=[0.744, 0.816] | mean=0.525, ci95=[0.428, 0.621] | mean=0.349, ci95=[0.270, 0.429] | mean=0.243, ci95=[0.160, 0.327] |
| adamw_reference | reference-only | open | HG-TCO-1 | mean=0.786, ci95=[0.712, 0.860] | mean=0.499, ci95=[0.398, 0.601] | mean=0.355, ci95=[0.239, 0.471] | mean=0.267, ci95=[0.130, 0.403] |
| adamw_undertrained | ledger-risk-only | open | HG-TCO-3 | mean=0.778, ci95=[0.720, 0.835] | mean=0.498, ci95=[0.439, 0.556] | mean=0.362, ci95=[0.314, 0.411] | mean=0.268, ci95=[0.189, 0.347] |

## Not Claimed

- no formal BEDC closure claim
- no global optimizer behavior claim
- no full LeJEPA conclusion
- no all-model or behavior conclusion
- no universal training-choice claim
- no promotion claim
- no total score, rank, grade, or hidden cost weight

## Revoke Conditions

- revoke observed-debt if learned-vs-matched-random CI separation disappears
- revoke observed-debt if matched-random crosses the positive ceiling
- revoke observed-debt if learned unlogged-error reduction is not above control
- revoke any claim if forbidden-feature audit fails
- revoke any claim if seed, split, source, or declared training-choice pairing fails
