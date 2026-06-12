# DGT base undertraining audit

- Verdict: `construct-boundary`
- Claim action: `defer-to-fair-reconstruction`
- Source: `reports/canonical/dgt-l1-controls.json:$.l1_step_ladder`
- Construct validity: `construct-boundary`

## Boundary ledger

- `base-undertraining-construct-validity`: equal-compute and equal-loss-decrease rows are non-informative for an information-starved baseline

## Comparison rows

- `equal_step`: `noninformative-dgt-separated` (base `0.010986`, DGT `0.038086`, pointer `reports/canonical/dgt-l1-controls.json:$.l1_step_ladder.per_step[0]`)
- `equal_compute`: `noninformative-dgt-separated` (base `0.010986`, DGT `0.038086`, pointer `reports/canonical/dgt-l1-controls.json:$.l1_step_ladder.per_step[0]`)
- `equal_loss_decrease`: `noninformative-dgt-separated` (base `0.013672`, DGT `0.03418`, pointer `reports/canonical/dgt-l1-controls.json:$.l1_step_ladder.per_step[4]`)

## Not claimed

- Bounded L1 tiny-sequence base-undertraining audit only.
- No undertraining discharge claim under information-starved baseline.
- No production deployment claim.
- No global superiority claim.
- No LLM replacement claim.
- No cross-level verdict inheritance.
