# Irreducibility Report

- Generated at: `2026-06-11T20:40:38.673140+00:00`
- Status: `pass`
- Positive irreducibility: `True`
- CMI table: `reports/canonical/conditional_information_table.json`

## Order Residual Analysis

| seed | order | low-order MSE | high-order MSE | gain | matched-random gain |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 101 | 2 | 1.899277 | 0.733532 | 1.165745 | -0.086475 |
| 101 | 3 | 0.733532 | 0.000661 | 0.732871 | -0.009912 |
| 211 | 2 | 1.382560 | 0.539810 | 0.842750 | 0.001577 |
| 211 | 3 | 0.539810 | 0.000544 | 0.539266 | 0.000387 |
| 307 | 2 | 2.186185 | 1.462238 | 0.723946 | 0.015125 |
| 307 | 3 | 1.462238 | 0.000611 | 1.461627 | 0.004546 |
| 401 | 2 | 1.190731 | 0.536812 | 0.653919 | -0.062068 |
| 401 | 3 | 0.536812 | 0.000646 | 0.536166 | 0.000939 |

## Hardgates

| gate | status | evidence |
| --- | --- | --- |
| `IRR-HG1` | `pass` | `$.records[*].orders[*].low_order_baseline_present` |
| `IRR-HG2` | `pass` | `$.records[*].orders[*].conditioned_residual_gain` |
| `IRR-HG3` | `pass` | `$.records[*].orders[*].matched_random_control` |
| `IRR-HG4` | `pass` | `$.seed_aggregation.orders` |

## Boundary

- CMI diagnostics do not set positive irreducibility.
- Matched-random high-order residual positives fail closed.
- The report is bounded to the deterministic lab fixture.
