# Reproduction Package

- Artifact: `bedc-quality-lab:reproduction-package`
- Generated at: `2026-06-13T08:49:46.900678+00:00`

| target | kind | owner | fingerprints |
| --- | --- | --- | --- |
| `dgt-l0-honest-rerun` | `full-repro-ci` | `reports/canonical/dgt-l0-controls.json:$` | `reports/canonical/dgt-l0-controls.fingerprint.json:$` |
| `fair-l1-training` | `full-repro-ci` | `reports/canonical/dgt-l1-controls.json:$` | `reports/canonical/dgt-l1-controls.fingerprint.json:$` |
| `honest-ablation-null-training` | `full-repro-ci` | `reports/canonical/dgt-neural-ablation.json:$` | `reports/canonical/dgt-neural-ablation.fingerprint.json:$, reports/canonical/dgt-ablation-null-decomposition.fingerprint.json:$` |
| `canonical-index-view` | `projection-only` | `reports/canonical/index.json:$` | `reports/canonical/reproduction-package.fingerprint.json:$` |
| `claim-capsule-view` | `projection-only` | `reports/canonical/claim_capsule.json:$` | `reports/canonical/reproduction-package.fingerprint.json:$` |
| `claim-graph-view` | `projection-only` | `reports/canonical/claim_graph.json:$` | `reports/canonical/reproduction-package.fingerprint.json:$` |
| `scaling-ladder-view` | `projection-only` | `reports/canonical/discovery-gated-transformer.json:$.scaling_ladder` | `reports/canonical/discovery-gated-transformer.fingerprint.json:$` |
| `generated-markdown-views` | `projection-only` | `reports/canonical/index.md` | `reports/canonical/reproduction-package.fingerprint.json:$` |

## Boundaries

- This package contains reproduction pointers only; metric values remain owned by source artifacts.
- Projection-only targets never satisfy measured-training full reproduction.
- Full training replay is only evaluated under the explicit full-repro-ci profile.
- Upstream owner gaps are reported as blocked rather than guessed.
