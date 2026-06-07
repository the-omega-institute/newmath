# Discovery-Gated NAS

- run_id: `discovery-gated-nas`
- schema_id: `bedc-quality-lab:discovery-gated-nas`
- discovery map signal: `negative`
- selected candidate: `bounded_discovery_gate`
- search score: `1.105907`
- claim capsule: `reports/runs/discovery-gated-nas/claim_capsule.json`

## Hardgates

- `DG-NAS-HG1`: `pass`
- `DG-NAS-HG2`: `pass`
- `DG-NAS-HG3`: `pass`
- `DG-NAS-HG4`: `pass`
- `DG-NAS-HG5`: `pass`
- `DG-NAS-HG6`: `pass`
- `DG-NAS-HG7`: `pass`
- `DG-NAS-HG8`: `fail`

## Negative Witness Mutations

- `score_margin_shortcut`: `score_margin_shortcut` -> `residualized_h_path`
- `scale_leakage`: `residualized_h_path` -> `scale_invariant_norm`
- `control_positive`: `scale_invariant_norm` -> `control_separated_route`

## Device Protocol

- requested: `auto`
- resolved: `not-requested`
- status: `unavailable`

## Not Claimed

- real model training
- general architecture superiority
- unbounded NAS search
- production device authority
- standalone verdict ownership
