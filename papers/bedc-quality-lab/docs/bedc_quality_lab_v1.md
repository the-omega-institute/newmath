# BEDC Quality Lab v1.0 Technical Report

This report is a pointer-only capstone for the local BEDC Quality Lab evidence bundle. Canonical status, report rows, discovery levels, and claim boundaries stay in machine-owned artifacts under `reports/canonical/`.

## 1. Scope & honest boundary

The lab scope is the local EvidenceEnvelope reporting surface. It points to canonical evidence artifacts and states the honest boundary without claiming global BEDC closure.

Pointers: `reports/canonical/index.json` `$.honest_boundary`; `reports/canonical/index.json` `$.claims_nonclaims`.

## 2. EvidenceEnvelope schema

The EvidenceEnvelope schema is the local evidence carrier used by canonical producers and report validators. This report names the schema surface and leaves schema identity to the canonical index.

Pointers: `reports/canonical/index.json` `$.schema_id`; `reports/canonical/index.json` `$.root`; `bedc_quality_lab/schema.py`.

## 3. CostProtocol & quality_q

Cost and quality projections are read from the configured CostProtocol surface and canonical scorecard outputs. This report does not recompute those projections in prose.

Pointers: `reports/canonical/index.json` `$.quality_scorecard`; `reports/canonical/quality-scorecard.json` `$.rows`; `configs/default_cost_protocol.yaml`.

## 4. Theorem-bound metrics

The theorem-bound evidence surface is carried by canonical scorecard metrics and report payloads. Prose here only identifies the artifacts that own those fields.

Pointers: `reports/canonical/index.json` `$.quality_scorecard.metrics`; `reports/canonical/quality-scorecard.json` `$.input_reports`; `bedc_quality_lab/claim_projection.py`.

## 5. TensorNameCertCandidate

TensorNameCertCandidate is treated as a lab-local pointer-bearing candidate layer. Full Tensor NameCert status is outside this report frame and stays under the nonclaim boundary.

Pointers: `reports/canonical/index.json` `$.claims_nonclaims.nonclaims`; `reports/canonical/index.json` `$.claims_nonclaims.status`; `tests/test_tensor_namecert_candidate.py`.

## 6. Canonical reports

The canonical report bundle is enumerated by the machine index. Report role, status, validation state, and artifact paths are read from that index instead of repeated here.

Pointers: `reports/canonical/index.json` `$.reports[*].name`; `reports/canonical/index.json` `$.reports[*].bundle_role`; `reports/canonical/index.json` `$.reports[*].json_artifact`; `reports/canonical/index.json` `$.reports[*].status`.

## 7. Selected positive worked case: gap-head-on-h

`gap-head-on-h` is the selected positive worked case for this report frame; positive-discovery classification is read from `reports/canonical/discovery_map.json:$.rows[*]`, so this section does not claim uniqueness among positive rows.

This navigation section follows the selected row into its canonical report payload and boundary fields. It does not summarize the discovery map or restate the complete set of positive and non-positive cells.

Pointers: `reports/canonical/discovery_map.json` `$.rows[report=gap-head-on-h]`; `reports/canonical/gap-head-on-h.json` `$.main_claim_status`; `reports/canonical/gap-head-on-h.json` `$.control_verdict`; `reports/canonical/gap-head-on-h.json` `$.treatment_comparison`; `reports/canonical/gap-head-on-h.json` `$.applicability_boundary`.

## 8. Negative: certificate-guided

Certificate-guided training and discovery are navigated as canonical evidence surfaces under their own report payloads and claim gates. Their classification is not inferred from prose.

Pointers: `reports/canonical/certificate-guided-training.json` `$.result.status`; `reports/canonical/certificate-guided-training.json` `$.claim_gate`; `reports/canonical/certificate-guided-discovery.json` `$.main_claim_status`; `reports/canonical/certificate-guided-discovery.json` `$.claim_gate`.

## 9. Observed-debt: non-Gaussian

The non-Gaussian sweep is an observed-debt evidence surface in this report frame. The status and ledger rows stay in its canonical artifact.

Pointers: `reports/canonical/nongaussian-distribution-sweep.json` `$.main_claim_status`; `reports/canonical/nongaussian-distribution-sweep.json` `$.claim_gate`; `reports/canonical/nongaussian-distribution-sweep.json` `$.negative_result_ledger`.

## 10. Formal hardening

Formal hardening is reported by canonical hardening pointers and local test surfaces. This report does not copy BEDC chapter body, theorem body, proof body, or closure status text.

Pointers: `reports/canonical/index.json` `$.formal_hardening`; `reports/canonical/index.json` `$.literature_ledger`; `tests/test_hardening.py`; `bedc_quality_lab/hardening.py`.

## 11. Limitations

The limitation surface is the union of explicit nonclaims, honest-boundary rows, report validation status, and the human claims boundary document.

Pointers: `reports/canonical/index.json` `$.claims_nonclaims.nonclaims`; `reports/canonical/index.json` `$.honest_boundary.not_claimed`; `reports/canonical/index.json` `$.reports[*].validation.status`; `docs/claims_and_nonclaims.md`.

## 12. Remote target

The remote target is a future-facing integration target, separate from the local evidence bundle and the canonical report artifacts in this repository.

Pointers: `reports/canonical/index.json` `$.paper_outline`; `reports/canonical/index.json` `$.root`; `docs/artifact_manifest.md`; epic `#600`; issue `#601`.
