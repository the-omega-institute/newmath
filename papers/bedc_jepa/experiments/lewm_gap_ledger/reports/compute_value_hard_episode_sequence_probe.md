# Compute-Value Hard-Episode Sequence Probe

- train positives: `34` / `167`
- calibration AUROC: `0.598484848`
- eval AUROC against top missed episodes: `0.54787234`
- eval Spearman with oracle gain: `0.101587302`
- top missed mean score: `-0.845537798`
- non-top missed mean score: `-0.72752409`

This probe augments aggregate rollout features with per-episode quantiles, adjacent-change summaries, and score-distribution summaries.
