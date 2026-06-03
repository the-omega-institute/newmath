# Claims and Non-Claims

## Report Claim Posture

The v1 alpha report posture is lab-local and pointer-only. It reports EvidenceEnvelope artifacts, CostProtocol projections, `quality_q`, theorem-bound projection pointers, discovery-map rows, claim-verdict rows, negative-witness rows, and canonical artifact pointers.

BEDC references are opaque pointers only, such as chapter path, label, or Lean target name stored in `bedc_refs`. This document does not copy BEDC chapter body or define BEDC semantics.

The forbidden exact-term source is `bedc_quality_lab/claim_terms.py:FORBIDDEN_POSITIVE_CLAIM_TERMS`.

## Not Claimed

- No BEDC closure claim.
- No broad model-quality claim.
- No production classifier behavior claim.
- No external model behavior claim.
- No certification claim beyond local artifact pointers.

## Positive Wording Boundary

`gap-head-on-h` is the only positive discovery prototype in this freeze frame, and only through `reports/canonical/discovery_map.json:$.rows[report=gap-head-on-h]` plus `reports/canonical/gap-head-on-h.json` pointers such as `$.main_claim_status`, `$.control_verdict`, `$.treatment_comparison`, and `$.applicability_boundary`.

Mixed, negative, or audit-improvement reports are under the nonclaim boundary. This includes `gap-head-discovery`, `certificate-guided-training`, `certificate-guided-discovery`, `nongaussian-distribution-sweep`, and `anisotropic-ou-sweep`.

`certificate-guided-discovery` is negative and is governed by `reports/canonical/discovery_map.json:$.rows[report=certificate-guided-discovery]`, `reports/canonical/certificate-guided-discovery.json:$.main_claim_status`, and `reports/canonical/certificate-guided-discovery.json:$.claim_gate`.

`nongaussian-distribution-sweep` and `anisotropic-ou-sweep` are audit-improvement pointers and are governed by `reports/canonical/discovery_map.json:$.rows[report=nongaussian-distribution-sweep]`, `reports/canonical/discovery_map.json:$.rows[report=anisotropic-ou-sweep]`, and their canonical report debt pointers.

## BEDC Pointer Discipline

Allowed BEDC references in this report layer are pointers to source locations or formal names. Examples of allowed pointer forms are:

- `papers/bedc/...`
- `ch:<theme>-<concept>`
- `sec:<theme>-<concept>`
- `thm:<concept>`
- `def:<concept>`
- `BEDC.<module>.<target>`

The report layer does not copy BEDC prose, theorem bodies, proof bodies, or chapter status blocks. Use `reports/canonical/index.json` and the envelope `bedc_refs` fields as pointer surfaces.
