# Encoder-capacity scaling de-risk for allocation

This experiment asks one question: **is the allocation-ranking ceiling
(`rho` near `0.3`-`0.5`, allocation delta on the wrong side of a uniform budget)
limited by encoder capacity?** If a larger from-scratch encoder lifts `rho`
toward the `~0.5`-`0.58` an allocation-useful split needs, then scale is the
fix; if `rho` stays flat across orders of magnitude, the bound is not a capacity
artifact.

## Method

`runner/derisk_alloc_a100.py` is a self-contained from-scratch BEDC-native
encoder trained on fixed tworooms pixels with the same objective and
no-leakage discipline as the small-scale from-scratch study (joint next-latent
prediction + VICReg health regularization + CVaR/tail-rank allocation loss).
The encoder width, depth, and latent dimension are scaled by CLI knobs; every
run reports the allocation delta (paired episode bootstrap), the rank
correlation `rho`, the `h=5`/`q75` detection AUROC, and the verified latent
health (per-dimension variance and effective rank). Allocation targets come
from the train split only; evaluation truth is used only after the health gate
for the final metrics; train and eval episodes are isolated.

## Results

Five healthy (non-collapsed) latents span four orders of magnitude of encoder
capacity; two width-8/batch-512 configs collapsed under the default recipe and
were re-trained healthy with a lower learning rate, stronger variance weight,
and warmup (`fix_a`, `fix_b`).

| config  | encoder params | batch | effective rank | healthy | allocation `rho` | allocation delta | detection AUROC |
| ------- | -------------: | ----: | -------------: | :-----: | ---------------: | ---------------: | --------------: |
| scale1  |       136,809  |  512  |          54.6  |   yes   |          0.340   |        `+0.007`  |          0.666  |
| scale4  |     6,098,529  |  512  |          59.6  |   yes   |          0.297   |        `+0.008`  |          0.660  |
| fix_a   |    41,544,257  |  512  |         112.1  |   yes   |          0.258   |        `+0.008`  |          0.631  |
| fix_b   |    41,544,257  |  512  |         109.1  |   yes   |          0.294   |        `+0.008`  |          0.648  |
| scale16 |   165,163,649  |  256  |          54.6  |   yes   |          0.385   |        `+0.007`  |          0.691  |
| scale8  |    42,922,049  |  512  |           7.4  |   no    |     (collapsed)  |               -  |              -  |
| scale8b |    41,544,257  |  512  |           3.5  |   no    |     (collapsed)  |               -  |              -  |

## Verdict

Across a `~1200x` range of encoder capacity (`0.14M` to `165M` parameters), all
with verified healthy non-collapsed latents (effective rank `54`-`112`), the
allocation rank correlation stays flat in `0.26`-`0.39` and never approaches the
`~0.5` threshold; the matched batch-512 series (`scale1`, `scale4`, `fix_a`,
`fix_b`) is flat-to-decreasing in `rho` as capacity grows. The allocation delta
stays positive (worse than a uniform budget) throughout, and detection AUROC is
likewise flat (`0.63`-`0.69`). **Allocation is therefore not encoder-capacity
limited: scaling the encoder does not move the allocation signal.**

The collapse of the width-8/batch-512 runs is a training-stability artifact
(the larger model degenerates under the default recipe at batch 512); it is
fixed by warmup + lower learning rate (`fix_a`/`fix_b`), which restores a
healthy high-rank latent without changing the flat `rho`.

## Scope

This varies **encoder capacity** on a **fixed** tworooms pixel dataset. It does
not vary data scale or diversity, and it does not change the world-model
architecture. The flatness of `rho` across encoder scale, together with the
fixed-latent readability bound and the prediction-axis gap recorded elsewhere in
this directory, is convergent evidence that the allocation signal is not present
to extract from this gap-ledger formulation on this carrier, rather than a
capacity limitation that more encoder parameters would remove.

## Reproducibility

`runner/derisk_alloc_a100.py --h5 <tworooms_pixels.h5> --labels <g2n_labels.npz>
--out <out.json> --width-mult W --depth-mult D --latent-dim L --batch B
--epochs 160 [--lr LR --var-weight VW --warmup-frac F]` is deterministic at a
fixed seed. The tworooms pixel rollouts are regenerated from the public
LeWorldModel checkpoints (see the parent experiments README); large pixel
intermediates are not committed. `results/` holds the measured payloads for the
configurations in the table above.
