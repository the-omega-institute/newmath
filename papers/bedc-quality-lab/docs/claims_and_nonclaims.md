# Claims and Non-Claims

## Report Claim Posture

The alpha-stage report posture is lab-local and pointer-only. It reports EvidenceEnvelope artifacts, CostProtocol projections, `quality_q`, theorem-bound projection pointers, discovery-map rows, claim-verdict rows, negative-witness rows, and canonical artifact pointers.

BEDC references are opaque pointers only, such as chapter path, label, or Lean target name stored in `bedc_refs`. This document does not copy BEDC chapter body or define BEDC semantics.

The forbidden exact-term source is `bedc_quality_lab/claim_terms.py:FORBIDDEN_POSITIVE_CLAIM_TERMS`.

## Not Claimed

- No BEDC closure claim.
- No broad model-quality claim.
- No production classifier behavior claim.
- No external model behavior claim.
- No certification claim beyond local artifact pointers.

## Positive Wording Boundary

Positive and non-positive report cells are read from `reports/canonical/discovery_map.json:$.rows[*]` and `reports/canonical/index.json:$.claims_nonclaims`; this document names `gap-head-on-h` only as the selected worked case for the report narrative.

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
