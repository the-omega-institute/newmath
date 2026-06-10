# DGT base undertraining audit

- Verdict: `evidence-strengthen`
- Claim action: `strengthen_l1_evidence`
- Source: `reports/canonical/dgt-l1-controls.json:$.l1_step_ladder`

## Comparison rows

- `equal_step`: `dgt-separated` (base `0.0625`, DGT `0.288086`, pointer `reports/canonical/dgt-l1-controls.json:$.l1_step_ladder.per_step[0]`)
- `equal_compute`: `dgt-separated` (base `0.0625`, DGT `0.288086`, pointer `reports/canonical/dgt-l1-controls.json:$.l1_step_ladder.per_step[0]`)
- `equal_loss_decrease`: `dgt-separated` (base `0.068359`, DGT `0.982422`, pointer `reports/canonical/dgt-l1-controls.json:$.l1_step_ladder.per_step[4]`)

## Not claimed

- Bounded L1 tiny-sequence base-undertraining audit only.
- No production deployment claim.
- No global superiority claim.
- No LLM replacement claim.
- No cross-level verdict inheritance.
