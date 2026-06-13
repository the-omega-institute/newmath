# LAT-style ledger-aware transformer on real LeWM latents

- claim: **positive** (auroc_sep=True, uer_sep=True)
- failure truth: prediction_mse > 0.076702 (train p75); eval failure rate 0.231
- transitions: 4991; episodes: 278; eval episodes: 55
- model: 92865 params, 360 steps, 9.69s CPU

| arm | AUROC | UER | declared gap rate | false alarm |
| --- | --- | --- | --- | --- |
| `vanilla` | 0.500 [0.500, 0.500] | 0.231 [0.205, 0.259] | 0.000 [0.000, 0.000] | 0.000 [0.000, 0.000] |
| `lat_learned` | 0.675 [0.636, 0.711] | 0.132 [0.110, 0.156] | 0.243 [0.216, 0.272] | 0.143 [0.121, 0.163] |
| `lat_matched_random` | 0.543 [0.499, 0.588] | 0.162 [0.134, 0.190] | 0.238 [0.206, 0.271] | 0.168 [0.140, 0.200] |
| `lat_without_dynamics` | 0.671 [0.634, 0.708] | 0.132 [0.108, 0.158] | 0.250 [0.219, 0.283] | 0.150 [0.129, 0.173] |

Phase1c logistic gap head reference (same protocol):

- `learned_gap_head_A_all_probe_features`: AUROC 0.732 [0.688, 0.772], UER 0.170 [0.148, 0.194]
- `learned_gap_head_B_denoised_agent_room_only`: AUROC 0.731 [0.692, 0.774], UER 0.168 [0.142, 0.191]
