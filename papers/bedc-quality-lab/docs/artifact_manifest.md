# Artifact Manifest

This manifest is a human navigation layer, not a second status cache. `reports/canonical/index.json` is the machine source for report status, canonical bundle role, scorecard linkage, and report artifact paths.

## Canonical Index

- Path: `reports/canonical/index.json`
- Role: machine-readable canonical report index and status source.
- Pointers: `$.reports`; `$.quality_scorecard`; `$.claims_nonclaims`; `$.honest_boundary`; `$.paper_outline`; `$.literature_ledger`; `$.schema_id`.

## Scorecard

- Path: `reports/canonical/quality-scorecard.json`
- Role: machine-readable scorecard artifact.
- Pointers: `$.rows`; `$.artifact_id`.

- Path: `reports/canonical/quality-scorecard.md`
- Role: human-readable scorecard artifact.
- Pointers: section headings in the markdown artifact.

## Core Reports

- Path: `reports/canonical/mixing-family-sweep.{json,md}`
- Role: canonical core report; status and role live in `reports/canonical/index.json`.
- Pointers: `$.coverage_item`; `$.negative_result_summary`.

- Path: `reports/canonical/anisotropic-ou-sweep.{json,md}`
- Role: canonical core report; status and role live in `reports/canonical/index.json`.
- Pointers: `$.config`; `$.transition_debt_by_grid`; `$.negative_result_summary`.

- Path: `reports/canonical/gap-head-on-h.{json,md}`
- Role: `gap-head-on-h` canonical core report and only positive discovery prototype in this report frame.
- Pointers: `$.main_claim_status`; `$.control_verdict`; `$.treatment_comparison`; `$.applicability_boundary`.

- Path: `reports/canonical/gap-head-discovery.{json,md}`
- Role: canonical core projection report under the non-positive boundary for this report frame.
- Pointers: `$.final_main_claim_status`; `$.matched_random_control`; `$.source_artifacts.source_json_artifact`.

- Path: `reports/canonical/certificate-guided-training.{json,md}`
- Role: canonical core mixed/negative report.
- Pointers: `$.result.status`; `$.claim_gate`; `$.paired_seed_protocol`.

- Path: `reports/canonical/certificate-guided-discovery.{json,md}`
- Role: canonical core negative projection report.
- Pointers: `$.main_claim_status`; `$.claim_gate`; `$.matched_random_baseline`.

## Auxiliary Reports

- Path: `reports/canonical/nongaussian-distribution-sweep.{json,md}`
- Role: auxiliary observed-debt report.
- Pointers: `$.main_claim_status`; `$.claim_gate`; `$.negative_result_ledger`.

- Path: `reports/canonical/spectral-ablation-hinge.{json,md}`
- Role: auxiliary hardening and ablation report.
- Pointers: `$.ledger_summary`; `$.negative_control_summary`.

## Schema and Protocol Sources

- Path: `bedc_quality_lab/schema.py`
- Role: local EvidenceEnvelope schema source.
- Pointers: `QualityEvidenceEnvelope`; `bedc_refs`.

- Path: `configs/default_cost_protocol.yaml`
- Role: default local CostProtocol configuration.
- Pointers: YAML keys consumed by `bedc_quality_lab/cost_protocol.py`.

- Path: `bedc_quality_lab/cost_protocol.py`
- Role: local cost and quality projection implementation.
- Pointers: public names imported by tests and canonical producers.

## Report Producers

- Path: `scripts/run_canonical_reports.py`
- Role: canonical report producer and index writer.
- Pointers: CLI help; generated `reports/canonical/index.json`.

- Path: `scripts/run_gap_ledger_head_on_h.py`
- Role: source producer for `gap-head-on-h`.
- Pointers: `reports/canonical/gap-head-on-h.{json,md}`.

- Path: `scripts/run_certificate_guided_training.py`
- Role: source producer for certificate-guided training.
- Pointers: `reports/canonical/certificate-guided-training.{json,md}`.

- Path: `scripts/run_nongaussian_distribution_sweep.py`
- Role: source producer for non-Gaussian observed-debt sweep.
- Pointers: `reports/canonical/nongaussian-distribution-sweep.{json,md}`.
