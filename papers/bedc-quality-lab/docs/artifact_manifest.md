# Artifact Manifest

This manifest is a human navigation layer, not a second machine source. Each row gives an artifact id, a path, a discovery-level pointer, and a pointer status. Report status, bundle role, scorecard linkage, and report artifact paths stay in `reports/canonical/index.json`.

## Freeze Surfaces

| artifact id | path | discovery_level pointer | pointer status |
| --- | --- | --- | --- |
| `bedc-quality-lab:canonical-report-index` | `reports/canonical/index.json` | `$.discovery_map` | pointer-only |
| `bedc-quality-lab:canonical-report-index-md` | `reports/canonical/index.md` | `## Freeze status pointers` | pointer-only |
| `bedc-quality-lab:quality-scorecard` | `reports/canonical/quality-scorecard.json` | `$.rows` | pointer-only |
| `bedc-quality-lab:quality-scorecard-md` | `reports/canonical/quality-scorecard.md` | `## Freeze pointers` | pointer-only |
| `bedc-quality-lab:v1-alpha-freeze` | `docs/bedc_quality_lab_v1_alpha.md` | `## Discovery Levels` | pointer-only |
| `bedc-quality-lab:claims-and-nonclaims` | `docs/claims_and_nonclaims.md` | `## Positive Wording Boundary` | pointer-only |
| `bedc-quality-lab:artifact-manifest` | `docs/artifact_manifest.md` | `## Freeze Surfaces` | pointer-only |

## Discovery Rows

| artifact id | path | discovery_level pointer | pointer status |
| --- | --- | --- | --- |
| `bedc-quality-lab:discovery-map` | `reports/canonical/discovery_map.json` | `$.rows[report=gap-head-on-h].discovery_level` | pointer-only |
| `bedc-quality-lab:discovery-map` | `reports/canonical/discovery_map.json` | `$.rows[report=certificate-guided-discovery].discovery_level` | pointer-only |
| `bedc-quality-lab:discovery-map` | `reports/canonical/discovery_map.json` | `$.rows[report=nongaussian-distribution-sweep].discovery_level` | pointer-only |
| `bedc-quality-lab:discovery-map` | `reports/canonical/discovery_map.json` | `$.rows[report=anisotropic-ou-sweep].discovery_level` | pointer-only |

## Canonical Report Artifacts

| artifact id | path | discovery_level pointer | pointer status |
| --- | --- | --- | --- |
| `bedc-quality-lab:mixing-family-sweep` | `reports/canonical/mixing-family-sweep.{json,md}` | `reports/canonical/discovery_map.json:$.rows[report=mixing-family-sweep].discovery_level` | pointer-only |
| `bedc-quality-lab:anisotropic-ou-sweep` | `reports/canonical/anisotropic-ou-sweep.{json,md}` | `reports/canonical/discovery_map.json:$.rows[report=anisotropic-ou-sweep].discovery_level` | pointer-only |
| `bedc-quality-lab:gap-head-on-h` | `reports/canonical/gap-head-on-h.{json,md}` | `reports/canonical/discovery_map.json:$.rows[report=gap-head-on-h].discovery_level` | pointer-only |
| `bedc-quality-lab:gap-head-discovery` | `reports/canonical/gap-head-discovery.{json,md}` | `reports/canonical/discovery_map.json:$.rows[report=gap-head-discovery].discovery_level` | pointer-only |
| `bedc-quality-lab:gap-head-ablation` | `reports/canonical/gap-head-ablation.{json,md}` | `reports/canonical/discovery_map.json:$.rows[report=gap-head-ablation].discovery_level` | pointer-only |
| `bedc-quality-lab:gap-head-threshold-frontier` | `reports/canonical/gap-head-threshold-frontier.{json,md}` | `reports/canonical/discovery_map.json:$.rows[report=gap-head-threshold-frontier].discovery_level` | pointer-only |
| `bedc-quality-lab:nongaussian-distribution-sweep` | `reports/canonical/nongaussian-distribution-sweep.{json,md}` | `reports/canonical/discovery_map.json:$.rows[report=nongaussian-distribution-sweep].discovery_level` | pointer-only |
| `bedc-quality-lab:certificate-guided-training` | `reports/canonical/certificate-guided-training.{json,md}` | `reports/canonical/discovery_map.json:$.rows[report=certificate-guided-training].discovery_level` | pointer-only |
| `bedc-quality-lab:certificate-guided-discovery` | `reports/canonical/certificate-guided-discovery.{json,md}` | `reports/canonical/discovery_map.json:$.rows[report=certificate-guided-discovery].discovery_level` | pointer-only |
| `bedc-quality-lab:spectral-ablation-hinge` | `reports/canonical/spectral-ablation-hinge.{json,md}` | `reports/canonical/discovery_map.json:$.rows[report=spectral-ablation-hinge].discovery_level` | pointer-only |

## Schema and Protocol Sources

| artifact id | path | discovery_level pointer | pointer status |
| --- | --- | --- | --- |
| `bedc-quality-lab:evidence-envelope` | `bedc_quality_lab/schema.py` | `QualityEvidenceEnvelope` | pointer-only |
| `bedc-quality-lab:cost-protocol-config` | `configs/default_cost_protocol.yaml` | YAML keys consumed by `bedc_quality_lab/cost_protocol.py` | pointer-only |
| `bedc-quality-lab:cost-protocol-source` | `bedc_quality_lab/cost_protocol.py` | public names imported by tests and canonical producers | pointer-only |
| `bedc-quality-lab:claim-terms-source` | `bedc_quality_lab/claim_terms.py` | `FORBIDDEN_POSITIVE_CLAIM_TERMS` | pointer-only |

## Report Producers

| artifact id | path | discovery_level pointer | pointer status |
| --- | --- | --- | --- |
| `bedc-quality-lab:canonical-runner` | `scripts/run_canonical_reports.py` | generated `reports/canonical/index.json` | pointer-only |
| `bedc-quality-lab:gap-head-on-h-producer` | `scripts/run_gap_ledger_head_on_h.py` | `reports/canonical/gap-head-on-h.{json,md}` | pointer-only |
| `bedc-quality-lab:certificate-guided-training-producer` | `scripts/run_certificate_guided_training.py` | `reports/canonical/certificate-guided-training.{json,md}` | pointer-only |
| `bedc-quality-lab:nongaussian-sweep-producer` | `scripts/run_nongaussian_distribution_sweep.py` | `reports/canonical/nongaussian-distribution-sweep.{json,md}` | pointer-only |
