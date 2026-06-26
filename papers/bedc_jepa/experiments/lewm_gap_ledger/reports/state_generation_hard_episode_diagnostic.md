# State-Generation Hard-Episode Diagnostic

- hard episode union: `[81, 115, 145, 193, 201, 213, 277]`
- hard episode count: `7`

| row | full delta | non-hard delta | hard-only delta | non-hard CI high | hard-only CI high |
|---|---:|---:|---:|---:|---:|
| `episode_best_seed` | -0.00359129 | -0.00792429 | 0.0268494 | -0.0036972 | 0.0375264 |
| `episode_objective` | -0.00129762 | -0.005756 | 0.0300239 | -0.00240684 | 0.0427181 |
| `seed_mean` | -0.00280072 | -0.00836696 | 0.0363038 | -0.00440723 | 0.0584182 |
| `episode_balanced` | 0.000327709 | -0.00767277 | 0.0565336 | -0.00338988 | 0.104124 |
| `episode_regret` | 9.9789e-05 | -0.00637426 | 0.045582 | -0.00276639 | 0.0994585 |
| `episode_dual_price` | -0.000470009 | -0.00858918 | 0.0565697 | -0.00448603 | 0.099844 |

## Verdict

The non-hard slice closes for every row under this diagnostic, while the hard-only slice remains the boundary.
