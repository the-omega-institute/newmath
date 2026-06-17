# State-Generation Assignment-State Recoverability

| row | hard mean capture | hard budget-2 | hard budget-3 | hard budget-4 | hard label rho |
|---|---:|---:|---:|---:|---:|
| `real_assignment_state` | -0.532726 | -0.664333 | -0.792486 | -0.141359 | 0.163371 |
| `shuffled_assignment_state` | -0.646822 | -0.341196 | -1.13483 | -0.46444 | 0.208358 |
| `no_assignment_control` | -0.569541 | -0.361154 | -0.778504 | -0.568965 | 0.188602 |
| `swapped_assignment_state` | -0.493269 | -0.750691 | -0.202689 | -0.526426 | 0.15365 |
| `mechanism_target_ceiling` | 1 | 1 | 1 | 1 | 1 |

## Gates

- exact-budget cardinality: `True`
- real beats shuffled capture: `True`
- real beats no-assignment capture: `True`
- real beats shuffled label rho: `False`
- label prediction noninferior to controls: `False`

## Verdict

The real assignment-state channel does not pass the matched shuffled/no-assignment recoverability gate.
