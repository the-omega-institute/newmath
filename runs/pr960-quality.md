---
pr: 960
role: quality
verdict: comment
---

## Verdict
Readable and focused overall, but I would leave two quality comments around an unused private parameter and validator size.

## Evidence
- `papers/bedc-quality-lab/scripts/run_canonical_reports.py:2850` accepts `generated_at` in `_build_discovery_gated_transformer_mechanism_certificate`, and line 2851 immediately discards it while the only caller passes a timestamp at line 3000. That makes the signature look like timestamped output when the certificate has no timestamped field.
- `papers/bedc-quality-lab/scripts/run_canonical_reports.py:2884` adds a 91-line `_validate_dgt_mechanism_certificate` that mixes top-level schema checks, public pointer checks, slot row checks, evidence group checks, and shortcut checks. The surrounding file already has large validators, so this is advisory rather than a merge blocker, but the new function is just past the review threshold and will be easier to maintain if split by validation concern.

## What would change your verdict
Remove the unused `generated_at` parameter from `_build_discovery_gated_transformer_mechanism_certificate` and its call site, or make the interface reason explicit by using the timestamp in the payload. Consider extracting `_validate_dgt_mechanism_slots` and `_validate_dgt_mechanism_evidence_pointers` so the top-level validator stays small.

⟦AI:AUTO-LOOP⟧
REVIEW_DONE:960:quality:comment
