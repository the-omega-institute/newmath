# Cook collision lookup table

This table records which collision rows are available to the C encoder as
lookup data and which rows are still blocked by missing phase catalogs.

## Method

Each checked row is derived by direct local Rule 110 simulation.

1. Emit Cook ether over a guarded finite row.
2. Overlay incoming particle row patterns with explicit particle ID, phase, and
   separation.
3. Evolve both the perturbed row and a pure ether control row for the same
   number of generations.
4. Compare the evolved rows to count non-ether differences and localized
   islands.
5. Match outgoing islands only against phase templates that are already locally
   verified.

The method is deliberately conservative. An outgoing island is not assigned a
Cook particle name unless that particle has a checked phase template available
to this module.

## Implemented lookup rows

| Left | Right | Left phase | Right phase | Separation | Steps | Evidence | Outcome exposed by C |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `A` | `A` | `0` | `0` | caller supplied | `220` | direct Rule 110 simulation from `A(f1_1)=111110` | coarse outcome plus final difference count and any matched `A` products |

The `A` row pattern is the Level 3.1 verified `A(f1_1)=111110` phase. The C
entry is accessed through `cook_lookup_collision('A', 'A', separation)` and
through the lower-level `cook_simulate_collision_patterns` API.

The current direct simulation does not certify a complete outgoing particle
multiset for all A-A separations. It records direct simulation evidence and
leaves unmatched persistent islands as unmatched. This is safer than assigning
Cook IDs to islands while only the A phase has a verified local template.

## Pending rows

Rows involving `B`, `C`, `D`, `E`, `F`, `G`, or `H` remain pending because this
repository does not yet contain phase-exact templates for those particles.
The existing `B`, `C`, and `D` emitters are row-0 behavioral approximations, and
`E` through `H` are outside the current collision module's compiled matrix.

| Pair family | Status |
| --- | --- |
| `A` with `B` through `H` | phase catalog pending |
| `B` through `H` with any other named particle | phase catalog pending |
| leader, ossifier, data-block packet interactions | package phases pending |

The C lookup API reports supported non-A-A compiled rows as
`COLLISION_EVIDENCE_PHASES_PENDING` with `COLLISION_UNKNOWN`. That prevents the
Cook encoder from treating heuristic rows as phase-exact collision data.

## API status

`cook_simulate_collision` is kept for compatibility with the older coarse
observer. New phase-exact work should use:

- `CookGliderPattern` for input phase rows,
- `cook_simulate_collision_patterns` for direct Rule 110 simulation,
- `cook_lookup_collision` for table-backed queries with evidence status.

Adding a future row requires a verified phase pattern for both incoming
particles and a stable-product matcher for every outgoing particle family in
the row.
