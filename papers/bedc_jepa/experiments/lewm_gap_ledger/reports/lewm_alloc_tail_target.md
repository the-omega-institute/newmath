# Allocation Tail Targets

- status: `ok`
- oracle delta anchor: `-0.015867561326` (target `-0.015867561326`)
- decision rule: per arm positive iff rho(score, true mean_err_to_5) >= 0.58 and paired episode-bootstrap CI95_high for allocation minus uniform is < 0

## Results

| arm | rho to mean_err_to_5 | rho to own target | delta vs uniform | 95% CI | oracle gap | verdict |
|---|---:|---:|---:|---:|---:|---|
| `T1_CVaR` | 0.398078 | 0.420671 | 0.013920236 | [0.003840803, 0.026973586] | 0.029787798 | not_positive |
| `T2_max_step` | 0.398078 | 0.420671 | 0.013920236 | [0.003840803, 0.026973586] | 0.029787798 | not_positive |
| `T3_q90` | 0.440101 | 0.473249 | 0.008584554 | [-0.001803981, 0.021189209] | 0.024452115 | not_positive |

## Controls

- uniform h: `3` for every anchor
- score-sorted allocation: low score half h=`5`, high score half h=`1`, odd median h=`3`
- oracle delta vs uniform: `-0.015867561` [-0.021509230, -0.010840608]

## Not Claimed

- single checkpoint single export
- prediction budget allocation rather than planning or control
- tail statistics are synthetic training targets
- no hyperparameter scan
- no selection of only the best arm
