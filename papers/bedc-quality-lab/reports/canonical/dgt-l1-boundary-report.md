# DGT L1 Boundary Report

- Artifact role: `boundary_block`
- Claim promotion eligible: `False`
- Boundary decision: `information-access-boundary`
- Scaling claim block: `blocked`
- Blocking pointer: `$.scaling_claim_block`

## Source Pointers

- dgt_l1_controls: `reports/canonical/dgt-l1-controls.json:$`
- task_spec_ref: `reports/canonical/dgt-l1-controls.json:$.task_spec`
- training_arms_ref: `reports/canonical/dgt-l1-controls.json:$.training_arms`
- negative_witness_sweep_ref: `reports/canonical/dgt-l1-controls.json:$.negative_witness_sweep`
- step_ladder_ref: `reports/canonical/dgt-l1-controls.json:$.l1_step_ladder`
- ood_mechanism_ref: `reports/canonical/dgt-l1-controls.json:$.l1_ood_mechanism`

## Hardgates

| gate | status | evidence |
| --- | --- | --- |
| `L1B-HG1` | `pass` | `$.task_formula` |
| `L1B-HG2` | `pass` | `$.feature_reachability` |
| `L1B-HG3` | `pass` | `$.base_bayes_ceiling` |
| `L1B-HG4` | `pass` | `$.negative_witness_refs` |
| `L1B-HG5` | `pass` | `$.claim_promotion_exclusion` |

## Not Claimed

- No architecture superiority claim.
- No tiny-sequence OOD generalization claim.
- No L1 scaling claim.
- No component-causal completeness claim.
- No order-two causal rule learning claim.
- No fair architecture comparison claim before the required rebuild resolves.
