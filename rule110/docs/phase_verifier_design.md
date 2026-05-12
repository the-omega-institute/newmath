# Phase Verifier Design

`encoder/phase_verifier.c` checks the Martinez phase strings registered in
`encoder/glider_phases.c` without modifying the catalog.

The verifier treats a registered phase string as one cyclic phase row. It runs
direct Rule 110 evolution for the glider's listed period and accepts the row
only when the resulting cyclic row is the original row translated by the listed
horizontal displacement.

The metadata table uses the Cook/Martinez physical parameters:

| Glider | Period | Shift |
|---|---:|---:|
| A | 3 | 2 |
| B | 4 | -2 |
| C1, C2, C3 | 7 | 0 |
| D1, D2 | 10 | 2 |
| Ebar | 30 | -8 |
| F | 36 | -4 |
| G | 42 | -14 |
| H | 92 | -18 |

The public result codes separate the failure modes:

| Code | Meaning |
|---|---|
| `PHV_OK` | The registered row is phase-exact under the direct row check. |
| `PHV_NOT_REGISTERED` | `glider_phase()` has no matching catalog row. |
| `PHV_NOT_PHASE_EXACT` | The row exists but does not recur under the listed metadata. |
| `PHV_NO_METADATA` | The row exists but no physical period/shift entry is registered. |

Current direct row outcomes for the registered catalog are:

| Family | Verified rows |
|---|---|
| A | all plain phases 1-4 |
| B | all plain phases 1-4 |
| C1 | A and B neighbor phases 1-4 |
| C2 | A and B neighbor phases 1-4 |
| C3 | A and B neighbor phases 1-4 |
| Ebar | A, B, C, and D neighbor phases 1-4 |
| F | A-neighbor phases 2 and 3 |
| G | A-neighbor phase 3 |
| H | A-neighbor phases 1, 2, and 3 |

Unverified registered rows under this direct row check:

| Row | Note |
|---|---|
| `F(A,1)` | Does not recur after 36 steps with shift -4. |
| `F(A,4)` | Does not recur after 36 steps with shift -4. |
| `G(A,1)` | Does not recur after 42 steps with shift -14. |
| `G(A,2)` | Does not recur after 42 steps with shift -14. |
| `G(A,4)` | Does not recur after 42 steps with shift -14. |
| `H(A,4)` | Does not recur after 92 steps with shift -18. |

This tool verifies phase rows. It is not a finite-ether perturbation certificate
for the whole Cook construction. Wider masks, multi-row tubes, and exact
collision contexts remain separate checks.
