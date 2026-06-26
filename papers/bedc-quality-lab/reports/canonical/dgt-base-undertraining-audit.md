# DGT base undertraining audit

- Verdict: `noninformative-separation`
- Claim action: `record_noninformative_rows`
- Source: `reports/canonical/dgt-l1-controls.json:$.l1_step_ladder`
- Construct validity: `construct-valid`

## Boundary ledger


## Comparison rows

- `equal_step`: `noninformative-dgt-separated` (base `0.009765`, DGT `0.038086`, pointer `reports/runs/discovery-gated-transformer/l1-tiny-sequence-controls/non_starved_fair_baseline_summary.json:$.training_config.epoch_count`)
- `equal_compute`: `noninformative-dgt-separated` (base `0.009765`, DGT `0.038086`, pointer `reports/runs/discovery-gated-transformer/l1-tiny-sequence-controls/non_starved_fair_baseline_summary.json:$.compute_units`)
- `equal_loss_decrease`: `noninformative-dgt-separated` (base `0.009765`, DGT `0.038086`, pointer `reports/runs/discovery-gated-transformer/l1-tiny-sequence-controls/non_starved_fair_baseline_summary.json:$.metrics.loss_decrease_mean`)
- `equal_validation_loss`: `noninformative-dgt-separated` (base `0.009765`, DGT `0.038086`, pointer `reports/runs/discovery-gated-transformer/l1-tiny-sequence-controls/non_starved_fair_baseline_summary.json:$.metrics.validation_loss_mean`)

## Not claimed

- Bounded L1 tiny-sequence base-undertraining audit only.
- No undertraining discharge claim from information-starved ablations.
- No production deployment claim.
- No global superiority claim.
- No LLM replacement claim.
- No cross-level verdict inheritance.
