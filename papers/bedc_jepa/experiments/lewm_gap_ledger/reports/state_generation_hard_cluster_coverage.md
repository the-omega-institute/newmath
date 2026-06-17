# State-Generation Hard-Cluster Coverage

- hard episodes: `[81, 115, 145, 193, 201, 213, 277]`
- cluster count: `12`
- coverage gap: `8.49405`
- compactness unique clusters: `3`

| cluster | train+cal episodes | eval episodes | hard eval episodes | mean best-seed delta |
|---:|---:|---:|---:|---:|
| 0 | 1 | 0 | 0 | 0 |
| 1 | 25 | 7 | 0 | -0.00994079 |
| 2 | 48 | 9 | 4 | 0.0166592 |
| 3 | 14 | 3 | 0 | -0.00457585 |
| 4 | 43 | 12 | 1 | -0.01558 |
| 5 | 20 | 4 | 2 | 0.0110736 |
| 6 | 9 | 4 | 0 | -0.00990406 |
| 7 | 2 | 0 | 0 | 0 |
| 8 | 1 | 0 | 0 | 0 |
| 9 | 25 | 7 | 0 | -0.00346736 |
| 10 | 2 | 0 | 0 | 0 |
| 11 | 33 | 9 | 0 | -0.0120458 |

## Verdict

Pre-label episode summaries do not by themselves cleanly expose the hard set as an under-covered compact cluster; the next objective must use richer invariant episode descriptors or causal perturbation features.
