# Release Manifest Sidecar

- Schema: `bedc-quality-lab:release-manifest-sidecar`
- Artifact: `bedc-quality-lab:release-manifest-sidecar`
- Canonical role: `sidecar_not_in_CANONICAL_REPORTS`
- Generated at: `2026-06-04T16:07:55.096198+00:00`
- Version: `0.0.1`
- Tag ref: `None`
- Release bundle status: `ready`
- Tag status: `absent`

## Source Pointers

| source | path | pointer |
| --- | --- | --- |
| `canonical_index` | `reports/canonical/index.json` | `$` |
| `artifact_manifest` | `docs/artifact_manifest.md` | `## Quality Baseline Surfaces` |
| `literature_ledger_release_navigation` | `docs/lit/literature_ledger.yaml` | `$.records[id=lit-artifact-release-navigation]` |
| `version` | `VERSION` | `file` |

## Required Pointers

| id | path | pointer | status | failure |
| --- | --- | --- | --- | --- |
| `canonical-index` | `reports/canonical/index.json` | `$.schema_id` | `resolved` | `None` |
| `artifact-manifest-navigation` | `docs/artifact_manifest.md` | `## Quality Baseline Surfaces` | `resolved` | `None` |
| `literature-ledger-release-navigation` | `docs/lit/literature_ledger.yaml` | `$.records[id=lit-artifact-release-navigation]` | `resolved` | `None` |
| `version-file` | `VERSION` | `file` | `resolved` | `None` |
| `canonical-index-markdown` | `reports/canonical/index.md` | `# Canonical Report Index` | `resolved` | `None` |
| `artifact-manifest-self-row` | `docs/artifact_manifest.md` | `row:bedc-quality-lab:artifact-manifest` | `resolved` | `None` |

## Not Claimed

- tag_status is falsifiable metadata, not a release-quality proof
- not the release tag itself
- not lab bundle release-ready unless all required pointers and the tag predicate resolve
- not a positive scientific result
- not model-quality evidence
- not a BEDC closure, NameCert, or scorecard upgrade
- not a substitute for PR-3 or PR-6 hardening coverage

## Revoke If

Revoke ready status if any required pointer stops resolving, the requested tag becomes stale, or this sidecar is used as report status evidence.
