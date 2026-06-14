# G2N Integrated A100 Matrix

- status: `ok-scoped`
- runner: `/mnt/rna01/zwlexa/scratch/lewm_alloc_derisk/runners/g2n_integrated.py`
- scheduler: Slurm `g2n_matrix`, `GPUA100`, one GPU, 80G memory, 160 epochs, batch 256, seed 0
- accepted row files: `g2n_integrated_a100_H.json`, `g2n_integrated_a100_HP.json`, `g2n_integrated_a100_HR.json`, `g2n_integrated_a100_HRT.json`, `g2n_integrated_a100_HRTO.json`, `g2n_integrated_a100_predonly.json`
- not carried as evidence: Slurm stdout/stderr and the shuffled-label traceback

## Detection

| row | rollout | pred | tail | OOD | h=1 AUROC | h=3 AUROC | h=5 AUROC | h=10 AUROC | paired detection status |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---|
| H | 0 | 0 | 0 | 0 | 0.695300 | 0.650268 | 0.680858 | 0.665590 | no horizon has paired CI above zero |
| H+P | 0 | 1 | 0 | 0 | 0.690942 | 0.642278 | 0.689940 | 0.653545 | no horizon has paired CI above zero |
| H+R | 1 | 0 | 0 | 0 | 0.767285 | 0.763804 | 0.727877 | 0.705836 | h=3 paired CI above zero |
| H+R+T | 1 | 0 | 1 | 0 | 0.773308 | 0.752711 | 0.734212 | 0.723707 | h=3 paired CI above zero |
| H+R+T+OOD | 1 | 1 | 1 | 1 | 0.781655 | 0.763956 | 0.749119 | 0.714307 | h=1 and h=3 paired CIs above zero |
| pred-only | 1 | 1 | 0 | 0 | 0.487836 | 0.514063 | 0.520284 | 0.441882 | all horizons below the post-hoc reference |

The full integrated row gives $h=1$ native AUROC $0.781655$.  This exceeds the
strongest-probe scalar recorded in the hardening report, $0.743986$, and the
same runner gives an interval-separated paired gain against its train-only
current-latent post-hoc reference: native $0.781655$ versus post-hoc $0.734316$,
paired $\Delta = +0.047339$ with CI $[+0.003193,\ +0.094628]$.

The direct matrix lever is rollout-internal information.  H and H+P stay below
the in-runner post-hoc reference at $h=1$, while H+R moves to $0.767285$ and the
full row reaches $0.781655$.

The pred-only control collapses to $h=1$ AUROC $0.487836$ and paired
$\Delta=-0.246479$ with CI $[-0.309298,\ -0.180516]$, so next-latent prediction
alone does not carry the detection result.

## Selective And Allocation

The full integrated row remains bounded outside detection:

- selective risk: `0.116505` at alpha `0.10`, coverage `0.162461`, so the risk target is not met.
- allocation delta: `+0.007858616`, CI `[-0.002430128, +0.020610463]`, so the budget allocation criterion is not met.
- allocation rho: `0.421443`, CI `[0.321000, 0.512735]`.

## Boundary

- No logit distillation term is used.
- Training standardization, OOD statistics, and selective thresholds are fit on train or calibration splits only.
- Evaluation labels/errors are used only for final metrics.
- The paired detection interval is against the in-runner train-only current-latent post-hoc reference, not directly against the strongest-probe scalar.
- The strongest-probe comparison is scalar hardening: $0.781655 > 0.743986$.
- The shuffled-label permutation row is not an accepted control because it ended fail-closed with a non-finite training loss.
- No selective-claim or allocation breakthrough is claimed.
