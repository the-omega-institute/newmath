# State-Generation Environment-State Descriptors

- hard episodes: `[81, 115, 145, 193, 201, 213, 277]`
- strongest descriptor: `agent_y_mean`
- strongest p: `0.0159968`
- descriptor hits: `3`

| descriptor | direction | hard mean | non-hard mean | gap | p |
|---|---|---:|---:|---:|---:|
| `distance_mean` | higher | 100.73 | 108.369 | -7.63838 | 0.741452 |
| `distance_min` | higher | 76.5126 | 79.4643 | -2.95168 | 0.585483 |
| `distance_p90` | higher | 120.175 | 130.814 | -10.6394 | 0.790042 |
| `distance_change_mean` | higher | -4.4435 | -3.93409 | -0.509406 | 0.608678 |
| `agent_x_mean` | either | 118.003 | 113.063 | 4.94015 | 0.690062 |
| `agent_y_mean` | either | 60.0129 | 87.4992 | -27.4862 | 0.0159968 |
| `target_x_mean` | either | 96.3295 | 121.791 | -25.462 | 0.257948 |
| `target_y_mean` | either | 93.5759 | 129.111 | -35.5354 | 0.114977 |
| `relative_x_mean` | either | -21.674 | 8.72811 | -30.4021 | 0.357928 |
| `relative_y_mean` | either | 33.5629 | 41.6121 | -8.04918 | 0.762248 |
| `different_room_mean` | higher | 0.938776 | 0.768948 | 0.169827 | 0.0759848 |
| `same_room_mean` | lower | 0.0612245 | 0.231052 | -0.169827 | 0.0735853 |
| `crosses_midline_mean` | higher | 0.0346939 | 0.0710317 | -0.0363379 | 0.765247 |
| `crosses_midline_max` | higher | 0.428571 | 0.520833 | -0.0922619 | 0.812038 |
| `action_norm_mean` | higher | 3.14833 | 3.17784 | -0.0295178 | 0.803839 |
| `action_delta_mean` | higher | 4.29546 | 4.32827 | -0.032813 | 0.608078 |
| `transition_step_mean` | higher | 13.4901 | 13.8597 | -0.369569 | 0.687463 |
| `transition_step_p90` | higher | 21.7881 | 20.7241 | 1.06394 | 0.172765 |
| `reward_mean` | lower | 0 | 0 | 0 | 1 |
| `terminated_mean` | higher | 0 | 0 | 0 | 1 |

## Verdict

Explicit two-rooms environment-state descriptors separate the recurring hard episodes at diagnostic strength; this supports environment-state or causal-geometry conditioning for the next allocation objective.
