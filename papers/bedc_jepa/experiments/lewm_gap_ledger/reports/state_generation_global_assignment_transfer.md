# State-Generation Global Assignment Transfer

- candidate count: `19`
- selected by non-hard slice: `state_generation_minimax_budget_policy`

| slice | mean capture | budget-2 capture | budget-3 capture | budget-4 capture | mean regret |
|---|---:|---:|---:|---:|---:|
| `selection_non_hard` | 0.408096 | 0.458031 | 0.386964 | 0.379294 | 0.0117423 |
| `heldout_hard` | -0.486893 | -0.399573 | -0.81835 | -0.242756 | 0.0625788 |

## Verdict

Non-hard selected global assignment calibration does not transfer to the hard exact-budget boundary; allocation remains open.
