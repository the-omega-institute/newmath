# NameCert Closure-Routing Benchmark

- profile: `smoke_audit`
- json artifact: `reports/namecert_audit.json`
- admission gate: `False`

## Metrics

- `learned` accuracy `1.0` ci `[1.0, 1.0]`
- `matched_twin_closure_blind` accuracy `0.5` ci `[0.39997916883635354, 0.6000208311636465]`
- `serialization_only_adversary` accuracy `0.5` ci `[0.39997916883635354, 0.6000208311636465]`
- `heldout_depth` accuracy `1.0` ci `[1.0, 1.0]`
- `bounded_pattern_control` accuracy `0.5` ci `[0.3267588386092959, 0.6732411613907041]`

## Hardgates

- `matched_twin_closure_blind_chance`: `pass`
- `learned_above_chance`: `pass`
- `serialization_only_adversary_chance`: `pass`
- `heldout_depth_above_chance`: `pass`
- `bounded_pattern_chance`: `pass`
- `analytic_ceiling`: `pass`
