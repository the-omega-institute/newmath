# BEDC Quality Lab Alpha Milestone

This document is a pointer hub for the alpha-stage quality baseline. Machine-readable status stays in canonical artifacts and local Python sources.

## Discovery Levels

Discovery levels are read from `reports/canonical/discovery_map.json` at `$.rows[*].discovery_level`. DN report bodies are machine-owned by `reports/canonical/negative_discovery_reports.json:$.rows[*]`; discovery-map DN rows carry only the resolvable owner pointer.

| level | pointer meaning |
| --- | --- |
| `D5-O` | robust operational discovery pointer |
| `D5-M` | mechanism-closed discovery pointer |
| `D4` | discovery-level pointer |
| `DN` | negative discovery pointer |
| `D1` | audit-improvement pointer |

Selected alpha milestone pointers are:

| report | baseline level pointer | evidence pointer |
| --- | --- | --- |
| `gap-head-on-h` | `reports/canonical/discovery_map.json:$.rows[report=gap-head-on-h].discovery_level` | `reports/canonical/discovery_map.json:$.rows[report=gap-head-on-h].evidence_pointer` |
| `certificate-guided-discovery` | `reports/canonical/discovery_map.json:$.rows[report=certificate-guided-discovery].discovery_level` | `reports/canonical/negative_discovery_reports.json:$.rows[report=certificate-guided-discovery].failed_gate` |
| `nongaussian-distribution-sweep` | `reports/canonical/discovery_map.json:$.rows[report=nongaussian-distribution-sweep].discovery_level` | `reports/canonical/discovery_map.json:$.rows[report=nongaussian-distribution-sweep].debt_row_pointer` |
| `anisotropic-ou-sweep` | `reports/canonical/discovery_map.json:$.rows[report=anisotropic-ou-sweep].discovery_level` | `reports/canonical/discovery_map.json:$.rows[report=anisotropic-ou-sweep].debt_row_pointer` |

## Artifact Pointers

| surface | pointer |
| --- | --- |
| canonical index | `reports/canonical/index.json`; `reports/canonical/index.md` |
| discovery map | `reports/canonical/discovery_map.json`; `reports/canonical/discovery_map.md` |
| claim verdicts | `reports/canonical/claim_verdicts.jsonl` |
| negative witnesses | `reports/canonical/discovery_negative_witnesses.json` |
| scorecard | `reports/canonical/quality-scorecard.json`; `reports/canonical/quality-scorecard.md` |
| claims boundary | `docs/claims_and_nonclaims.md` |
| artifact manifest | `docs/artifact_manifest.md` |

## Evidence Pointers

| evidence class | pointer |
| --- | --- |
| `D4` | scoped operational row: `reports/canonical/discovery_map.json:$.rows[report=gap-head-on-h]`; transfer surface: `reports/canonical/gap-head-observed-debt-transfer.json:$.gap_head_on_h_observed_debt_transfer.status` |
| `D5-M` | mechanism closure row state: `reports/canonical/discovery_map.json:$.rows[*].discovery_level`; attribution evidence: `reports/canonical/gap_head_attribution_capsule.json:$.d5_m` |
| `D4` | full set: `reports/canonical/discovery_map.json:$.rows[*].discovery_level` |
| `DN` | `reports/canonical/discovery_map.json:$.rows[report=certificate-guided-discovery]` |
| `D1` | `reports/canonical/discovery_map.json:$.rows[report=nongaussian-distribution-sweep]`; `reports/canonical/discovery_map.json:$.rows[report=anisotropic-ou-sweep]` |

## Nonclaim Boundary

Positive wording is bounded by `docs/claims_and_nonclaims.md` and forbidden exact terms are sourced from `bedc_quality_lab/claim_terms.py`.

The report layer points to local evidence artifacts only. It does not claim BEDC closure, broad model quality, production classifier behavior, or external model behavior.
