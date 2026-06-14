# LeWM gap-ledger experiments

Reproducible experiment code and result records behind the LeWM instantiation
section of the BEDC-JEPA article (`papers/bedc_jepa/parts/lewm_instantiation.tex`).

These experiments instrument **fixed, public LeWorldModel (LeWM) checkpoints**
with a BEDC gap-ledger readout: a failure-versus-declared-gap signal read off
the frozen latent, post-hoc heads and small trained ledger transformers on top
of that latent, perturbation and horizon boundaries, an allocation
information bound, a ledger-shaped re-encoder probe, and a split-conformal
selective-prediction guarantee. The numeric claims in the article are read
directly from the JSON records under `reports/`.

## Attribution

- **Upstream LeWorldModel** — Lucas Maes, Quentin Le Lidec, Damien Scieur,
  Yann LeCun, Randall Balestriero, *LeWorldModel: Stable End-to-End
  Joint-Embedding Predictive Architecture from Pixels* (arXiv:2603.19312).
  Checkpoints: <https://huggingface.co/collections/quentinll/lewm>.
  The two files `code/jepa.py` and `code/module.py` are vendored **unmodified**
  from the LeWM repository under its MIT license (see
  `code/LICENSE.lewm-upstream`); they are the model architecture our probe
  reconstructs. We do not redistribute the upstream training/eval framework.
- **Everything else** (`code/_*.py` and `code/lewm_latent_probe.py`) is our own
  gap-ledger instrumentation, run against the public checkpoints. The latent
  probe is deliberately `stable_worldmodel`-free: it rebuilds the LeWM modules
  from `torch`/`transformers` plus the two vendored architecture files so the
  checkpoints can be loaded without the full environment stack.

## Layout

- `code/` — our experiment scripts (import graph is flat; keep them together).
  - `lewm_latent_probe.py` — load a public checkpoint, encode rollouts to latents.
  - `_phase*_*.py`, `_lat_lewm_*.py` — latent export + gap-ledger heads.
  - `_g2n_*.py`, `_crossenv_*.py`, `_allocation_*.py`, `_d_ledger_shaped_reencoder.py`,
    `_native_vs_posthoc_paired.py`, `_conformal_calibration.py`, ... — the
    boundary and bound studies.
  - `jepa.py`, `module.py`, `LICENSE.lewm-upstream` — vendored upstream (MIT).
- `reports/` — the result records (`*.json`) and human-readable summaries
  (`*.md`). These are the artifacts the article points to.

## Environment

```
python>=3.10
torch==2.6.0            # CUDA 12.4 build used on an 8 GB RTX 4060 Laptop GPU
numpy, h5py, hdf5plugin, einops
huggingface_hub, transformers
zstandard                # pusht datasets ship as .h5.zst
scikit-learn             # a couple of baseline heads
```

See `requirements.txt`. CPU transformer numerics are made deterministic by
`torch.set_num_threads(4)` at module top in the scripts that build the trained
ledger; do not move it below model construction or the anchored numbers drift.

## Reproduction pipeline

The large latent/label intermediates are **not committed** (they are
re-derivable and run to hundreds of MB): `*_latent_large.npz`, the
`crossenv_latent_cache/` per-episode caches, `g2n_labels_*_train.npz`, and the
OOD embedding caches. Regenerate them from the public checkpoints:

1. **Fetch checkpoints** (cached under `~/.cache/huggingface`): the probe pulls
   `quentinll/lewm-{tworooms,reacher,cube,pusht}` (`weights.pt` + `config.json`).
   The exact snapshot hashes used are recorded in the `reports/*.json`
   `inputs`/`source` fields.
2. **Export latents** — `lewm_latent_probe.py` and `_phase1a_export_latents.py` /
   `_crossenv_export_latents.py` encode rollouts into `*_latent_large.npz`.
3. **Build ledger heads / arms** — `_phase1c_gap_ledger.py`,
   `_lat_lewm_ood.py` / `_lat_lewm_ood_aware.py`, `_g2n_native_ledger.py`,
   `_d_ledger_shaped_reencoder.py` train the post-hoc and trained-ledger
   readouts on the exported latents.
4. **Measure boundaries** — the `_allocation_*`, `_crossenv_*`,
   `_native_vs_posthoc_paired.py`, `_conformal_calibration.py` scripts emit the
   `reports/lewm_*.json` records the article cites.

Each script writes its record to `reports/` via a `ROOT`-relative path, so the
tree is self-contained once the intermediates are regenerated next to `code/`.

## Target-oriented loop

The continuing G2N work is driven by a narrow loop around the same
fail-closed autoresearch gates:

```bash
python autoresearch/g2n_research_loop.py --once --pull-remote
```

The loop pulls finished A100 artifacts when available, runs the direct
strongest-posthoc paired comparison, the selective calibration sweep, and the
shuffled-label permutation guard, writes
`reports/g2n_integrated_a100_closure_status.json`, and then executes only the
G2N closure hypotheses (`fi-018`--`fi-020`) through the existing
executor/gate/writeback/canonical-adapter stack.  Missing A100 files are
pending and fail-closed; they do not create evidence records or change the
article claim.

## What the records establish (and do not)

The boundary results are summarized in the article; in short they form a
self-consistent system: failure-readability off the LeWM latent is real and
internalizable into a trained ledger, but capped by the latent's information
content (allocation Spearman observed `rho ~ 0.41`, CI upper `0.49` below the
`rho* ~ 0.50` ceiling). These are **external evidence records on fixed public
checkpoints**, not a BEDC NameCert / closure / canonical quality-lab result and
not (on their own) Lean-verified. The one machine-checked component is the
finite split-conformal counting core, formalized mathlib-free and axiom-free in
`papers/bedc_jepa/formal/bedc-conformal-lean/`; the statistical miscoverage
bound under exchangeability is recorded as open, not claimed.
