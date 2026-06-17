# Compute-Value Hard-Episode Probe

- train positives: `34` / `167`
- calibration AUROC: `0.526515152`
- eval AUROC against top missed episodes: `0.505319149`
- eval Spearman with oracle gain: `0.335930736`
- top missed mean score: `-0.65594965`
- non-top missed mean score: `-0.621581634`

The probe uses train-split oracle-gain tail labels for fitting and calibration labels for model selection.
Eval top-missed labels come from the already recorded episode decomposition and are used only after scores are produced.
