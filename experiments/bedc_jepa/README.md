# BEDC-JEPA Tiny World Experiment

This directory is the experiment entry point for the BEDC-JEPA tiny world construction. It keeps model training and empirical evidence separate from the BEDC paper and Lean sources while reusing the BEDC Model Quality Lab evidence boundary.

The experiment tests whether a BEDC-native objective can reduce unlogged errors relative to a vanilla latent predictor. The tracked target metric is:

```text
UnloggedErrorRate = P(error and gap_score < threshold)
```

The current implementation delegates the trained objective to `papers/bedc-quality-lab/bedc_quality_lab/torch_bedc_jepa.py`, which trains a latent predictor with distinction and gap heads on the boundary-gated toy world. This directory adds a stable research packet around that producer:

- `configs/tiny_world.yaml` declares the scoped target.
- `scripts/run_packet.py` builds the final experiment packet.
- `certs/build_namecert.py` projects the packet into a TensorNameCert-style YAML artifact.
- `certs/build_ledger.py` projects failure and scope residues into JSON.
- `metrics/quality_gate.py` checks the unlogged-error and debt-reduction gates.

Run from the repository root:

```bash
python experiments/bedc_jepa/scripts/run_packet.py
python experiments/bedc_jepa/scripts/check_gate.py
```

The generated final artifacts are written under `experiments/bedc_jepa/reports/`. Local scratch runs belong under `experiments/bedc_jepa/runs/` and are ignored by git.
