# Cook Construction Notes for `.algo.ct`

The `.algo.r110.ct` path is a diagnostic Cook-packet track for bounded
algorithm manifests with nonempty cyclic-tag productions.

Current covered case:

- `manifests/hist/hsame_refl.algo.ct`
- 16 cyclic-tag productions
- 5 bounded input cases
- generator: `encoder/generate_r110_algo`
- verifier: `make test-algo-r110`

The generator parses the source `.algo.ct`, runs the cyclic-tag reference for
exactly the input length, checks the expected certificate when the manifest
contains `expected_certificate=...`, composes a Rule 110 row with
`cook_encode_phase_exact()`, evolves that row for the configured step count,
and records both initial and final Rule 110 rows.

This construction is deliberately diagnostic. It verifies that the
phase-exact leader, ossifier, data-block, and ether components can be placed in
one physical Rule 110 row and deterministically re-evolved by
`evaluator/rule110.c`. It does not yet decode the evolved Rule 110 pattern back
into the cyclic-tag final certificate. The missing piece is the collision-level
Cook schedule that exposes a certified CT output window after physical
evolution.

## Format

```
ALGO_R110_MANIFEST 1
SOURCE_CT manifests/hist/hsame_refl.algo.ct
CONSTRUCTION cook_phase_exact_packet_diagnostic
EVOLUTION_STEPS 128
ASSERTIONS 5
case empty
INPUT 1111
CT_STEPS 4
CT_FINAL 20
10000100011001010011
RULE110_INITIAL 21532
<21532 bits>
RULE110_FINAL 21532
<21532 bits>
ENDCASE
```

The multi-line block format is used because Cook packet rows are much wider
than the compact direct-carrier `.r110.ct` rows.

## Verification Boundary

`make test` continues to cover shipped `.enum.ct` direct-carrier `.r110.ct`
manifests. The Cook packet diagnostic is opt-in:

```bash
cd rule110
make encoder/generate_r110_algo
./encoder/generate_r110_algo manifests/hist/hsame_refl.algo.ct manifests/hist/hsame_refl.algo.r110.ct 128
make test-algo-r110
```

This keeps the shipped Tier B direct-carrier gate separate from the research
track for nonempty `.algo.ct` programs.

## Observed Obstruction

The phase-exact emitters write canonical glider ingredients, but the
repository does not yet contain a decoded collision schedule that maps evolved
Rule 110 cells back to cyclic-tag tape symbols. Without that decoded output
window, the honest claim is a physical Cook packet evolution diagnostic, not a
completed `.algo.ct` semantic round-trip.
