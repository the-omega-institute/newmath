# State-Generation Hard Transfer Mechanism

- selected transfer score: `state_generation_minimax_budget_policy`
- strongest regret descriptor: `env_agent_x_mean`
- strongest absolute rho: `0.282395`

| descriptor | rho all | rho hard | high-low regret | hard mean | non-hard mean |
|---|---:|---:|---:|---:|---:|
| `env_agent_x_mean` | -0.282395 | -0.142857 | -0.00682686 | 118.003 | 113.063 |
| `env_same_room_mean` | -0.260678 | 0 | -0.00731028 | 0.0612245 | 0.231052 |
| `env_different_room_mean` | 0.257431 | -0.214286 | 0.00731028 | 0.938776 | 0.768948 |
| `env_agent_y_mean` | -0.254257 | -0.0357143 | -0.0236632 | 60.0129 | 87.4992 |
| `env_distance_change_mean` | 0.220491 | 0.214286 | 0.00830754 | -4.4435 | -3.93409 |
| `score_rollout_step_norm_max` | -0.203463 | -0.678571 | -0.0218983 | 20.723 | 21.171 |
| `score_best_seed_score_margin_mean` | -0.198124 | 0.642857 | -0.00425563 | 0.819724 | 1.06507 |
| `env_relative_x_mean` | 0.165296 | -0.0357143 | 0.00312732 | -21.674 | 8.72811 |
| `score_rollout_step_norm_mean` | 0.162987 | 0.25 | 0.00470267 | 16.6484 | 17.0805 |
| `env_action_norm_mean` | -0.139394 | -0.0357143 | -0.0177798 | 3.14833 | 3.17784 |
| `score_rollout_curvature_mean` | 0.138961 | 0.214286 | 0.00444655 | 28.468 | 29.0686 |
| `score_best_seed_score_entropy_mean` | 0.133405 | -0.607143 | 0.00393618 | 1.14442 | 1.06812 |

## Verdict

Fixed non-label descriptors do not strongly explain the selected-vs-oracle hard transfer regret; the next route needs richer perturbation labels rather than descriptor reweighting.
