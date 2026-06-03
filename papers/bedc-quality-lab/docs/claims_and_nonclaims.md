# Claims and Non-Claims

## Report Claim Posture

The v1.0 report posture is lab-local: it reports EvidenceEnvelope artifacts, CostProtocol projections, `quality_q`, theorem-bound projection pointers, and canonical artifact pointers. The report may claim that a local artifact records a declared status at a JSON pointer; it must not turn that pointer into a broader BEDC or model-quality claim.

BEDC references are opaque pointers only, such as chapter path, label, or Lean target name stored in `bedc_refs`. This document does not copy BEDC chapter body or define BEDC semantics.

## Not Claimed

- not full LeJEPA
- not full Tensor NameCert
- not global quality
- not LLM behavior
- not solved model quality

## Positive Wording Boundary

`gap-head-on-h` is the only positive discovery prototype in this report frame, and only through `reports/canonical/gap-head-on-h.{json,md}` plus `reports/canonical/gap-head-on-h.json` pointers such as `$.main_claim_status`, `$.control_verdict`, `$.treatment_comparison`, and `$.applicability_boundary`.

Mixed/negative or observed-debt reports are under a forbidden positive wording boundary. This includes `gap-head-discovery`, `certificate-guided-training`, `certificate-guided-discovery`, and `nongaussian-distribution-sweep`.

`certificate-guided-training` is mixed/negative and is governed by `reports/canonical/certificate-guided-training.json` `$.result.status` and `$.claim_gate`. `certificate-guided-discovery` is negative and is governed by `reports/canonical/certificate-guided-discovery.json` `$.main_claim_status` and `$.claim_gate`.

`nongaussian-distribution-sweep` is observed-debt only and is governed by `reports/canonical/nongaussian-distribution-sweep.json` `$.main_claim_status`, `$.claim_gate`, and `$.negative_result_ledger`.

## BEDC Pointer Discipline

Allowed BEDC references in this report layer are pointers to source locations or formal names. Examples of allowed pointer forms are:

- `papers/bedc/...`
- `ch:<theme>-<concept>`
- `sec:<theme>-<concept>`
- `thm:<concept>`
- `def:<concept>`
- `BEDC.<module>.<target>`

The report layer does not copy BEDC prose, theorem bodies, proof bodies, or chapter status blocks. Use `reports/canonical/index.json` and the envelope `bedc_refs` fields as pointer surfaces.
