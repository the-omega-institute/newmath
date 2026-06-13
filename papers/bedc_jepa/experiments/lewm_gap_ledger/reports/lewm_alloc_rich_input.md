# LEWM Allocation Rich Input

- status: `ok`
- positive rule: positive iff rho >= 0.58 and allocation delta CI95_high < 0
- E clean h=1 AUROC: `0.738515205859875` (target `0.738515205859875`)
- oracle delta: `-0.015867561` (target `-0.015867561`)

## Three Arms

| arm | input | rho | rho>=0.58 | delta vs uniform | 95% CI | oracle gap | verdict | rho > 0.51 baseline |
|---|---|---:|---|---:|---:|---:|---|---|
| `A1` | past(z,a)+pred_z[1:5]+delta_pred_z[2:5] | 0.460984 | no | 0.008216285 | [-0.002734186, 0.021459633] | 0.024083846 | not_positive | no |
| `A2` | A1+12 frozen E logits | 0.492759 | no | 0.006788651 | [-0.004112135, 0.020195480] | 0.022656212 | not_positive | no |
| `A3` | A2+4 pred_z drift norms | 0.456554 | no | 0.008580426 | [-0.002776642, 0.022853503] | 0.024447988 | not_positive | no |

## Controls

| control | rho | delta vs uniform | 95% CI |
|---|---:|---:|---:|
| `oracle` | 1.000000 | -0.015867561 | [-0.021509230, -0.010840608] |

## Interpretation

- best rich-input rho is 0.492759 from A2; baseline comparison is rho~0.51
- rich input did not push rho over the 0.51 failed-ranker baseline
- no arm satisfies the predeclared positive rule rho>=0.58 and CI95_high<0
- negative result strengthens the information-limit diagnosis under this frozen protocol

## Not Claimed

- single checkpoint single export
- prediction budget allocation rather than planning or control
- no hyperparameter scan
- no selection of only the best arm
- negative arms are reported as negative without post hoc threshold changes
