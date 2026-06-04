# Single Threshold Escape Witness

- artifact: `runs/single_threshold_escape_witness.json`
- schema_id: `bedc-quality-lab:single-threshold-escape-witness-sidecar`
- canonical_role: `sidecar-not-in-CANONICAL_REPORTS`
- status: `escaped-positive-captured`
- projection: `D4`
- escaped_positive_is_discovery_evidence: `false`

## Source Pointers

- control_baseline: `reports/canonical/gap-head-threshold-frontier.json:$.threshold_summary.control_baseline`
- deferred_kind: `reports/canonical/discovery_gate_escape_registry.json:$.deferred_kinds[kind=single_threshold_positive_only]`
- hardgate_checks: `reports/canonical/gap-head-threshold-frontier.json:$.hardgate.checks`
- hardgate_policy: `reports/canonical/gap-head-threshold-frontier.json:$.hardgate.policy`
- not_claimed: `reports/canonical/gap-head-threshold-frontier.json:$.applicability_boundary.not_claimed`
- threshold_curve: `reports/canonical/gap-head-threshold-frontier.json:$.threshold_curve`

## Hardgates

- HG-STEW-1: `pass`
- HG-STEW-4: `pass`
- HG-STEW-2: `pass`
- HG-STEW-3: `pass`
- HG-STEW-5: `pass`
- HG-STEW-6: `pass`

## Basis

- reports/canonical/gap-head-threshold-frontier.json:$.threshold_curve[0]: threshold=0.05, AUROC.ci95_low=0.7996948122113381

## Boundary

- No threshold tuning claim.
- No D5 claim.
- No canonical discovery-map promotion.
- No model-quality solution claim.
