# BEDC Quality Lab v1.0 Report Outline

本 outline 是人类报告骨架。canonical metric、scorecard、status 和 report body 以 `reports/canonical/index.json` 与对应 artifact 为机器源；本文件只保留 section 级导航和 JSON pointer。

## 1. Scope & honest boundary

Purpose: state the lab-local EvidenceEnvelope boundary and the report's honest boundary without claiming global BEDC closure.

Pointers: `README.md` "证据边界"; `reports/canonical/index.json` `$.honest_boundary`; `$.claims_nonclaims`.

## 2. EvidenceEnvelope schema

Purpose: identify the envelope schema as the local evidence carrier used by reports.

Pointers: `bedc_quality_lab/schema.py`; `reports/canonical/index.json` `$.schema_id`; `reports/canonical/index.json` `$.root`.

## 3. CostProtocol & quality_q

Purpose: explain that cost and quality projections are read from the CostProtocol surface rather than recomputed in the prose report.

Pointers: `configs/default_cost_protocol.yaml`; `reports/canonical/quality-scorecard.{json,md}`; `reports/canonical/index.json` `$.quality_scorecard`; `$.reports[*].json_artifact`.

## 4. Theorem-bound metrics

Purpose: locate theorem-bound projection artifacts and the JSON fields that carry theorem-bound quality evidence.

Pointers: `reports/canonical/index.json` `$.quality_scorecard.metrics`; `reports/canonical/*.{json,md}`; `bedc_quality_lab/claim_projection.py`.

## 5. TensorNameCertCandidate

Purpose: describe the candidate layer as a lab-local pointer-bearing artifact, not a full Tensor NameCert claim.

Pointers: `tests/test_tensor_namecert_candidate.py`; `tests/test_tensor_namecert_candidate_closure.py`; `reports/canonical/index.json` `$.claims_nonclaims.nonclaims`.

## 6. Canonical reports

Purpose: enumerate the canonical report bundle by role and artifact path while leaving status to the machine index.

Pointers: `reports/canonical/index.json` `$.reports[*].name`; `$.reports[*].bundle_role`; `$.reports[*].json_artifact`; `$.reports[*].markdown_artifact`; `$.reports[*].status`.

## 7. Positive: gap-head-on-h

Purpose: mark `gap-head-on-h` as the only positive discovery prototype in this report frame.

Pointers: `reports/canonical/gap-head-on-h.{json,md}`; `reports/canonical/index.json` `$.reports[?(@.name=="gap-head-on-h")]`; `reports/canonical/gap-head-on-h.json` `$.main_claim_status`; `$.matched_random_control`; `$.applicability_boundary`.

## 8. Negative: certificate-guided

Purpose: mark certificate-guided training and discovery as mixed/negative evidence under a non-positive boundary.

Pointers: `reports/canonical/certificate-guided-training.{json,md}`; `reports/canonical/certificate-guided-discovery.{json,md}`; `reports/canonical/certificate-guided-training.json` `$.result.status`; `$.claim_gate`; `reports/canonical/certificate-guided-discovery.json` `$.main_claim_status`.

## 9. Observed-debt: non-Gaussian

Purpose: mark the non-Gaussian sweep as observed-debt evidence only.

Pointers: `reports/canonical/nongaussian-distribution-sweep.{json,md}`; `reports/canonical/nongaussian-distribution-sweep.json` `$.main_claim_status`; `$.claim_gate`; `$.negative_result_ledger`.

## 10. Formal hardening

Purpose: point to hardening checks and verification surfaces without restating BEDC chapter body.

Pointers: `bedc_quality_lab/hardening.py`; `tests/test_hardening.py`; `reports/canonical/index.json` `$.literature_ledger`; BEDC pointer fields under envelope `bedc_refs`.

## 11. Limitations

Purpose: collect explicit non-claims and applicability limits for the report frame.

Pointers: `docs/claims_and_nonclaims.md`; `reports/canonical/index.json` `$.claims_nonclaims.nonclaims`; `$.honest_boundary.not_claimed`; `reports/canonical/*.{json,md}` `$.main_claim_status`.

## 12. Remote target

Purpose: identify the remote target as a future-facing integration target, separate from the local evidence bundle.

Pointers: epic `#600`; issue `#601`; `reports/canonical/index.json`; artifact manifest `docs/artifact_manifest.md`.
