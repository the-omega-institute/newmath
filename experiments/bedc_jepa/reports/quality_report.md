# BEDC-JEPA Tiny World Quality Report

## Scope

- World: `boundary-gated-ou-world`
- Baseline: `torch-latent-only`
- BEDC objective: `torch-bedc-jepa-objective`
- Primary metric: `unlogged_error_rate`

## Objective

- `latent_prediction`
- `distinction_bce`
- `gap_bce`
- `unlogged_error_penalty`

## Single Run

- Baseline unlogged error: `0.007812`
- BEDC-JEPA unlogged error: `0.000000`
- Baseline gap AUROC: `0.500000`
- BEDC-JEPA gap AUROC: `0.999223`
- Baseline debt: `0.104297`
- BEDC-JEPA debt: `0.007459`

## Seed Sweep

- Seed count: `3`
- Mean unlogged-error reduction: `0.009983`
- Mean gap-AUROC gain: `0.498762`
- Mean debt reduction: `0.102887`
- Latent R2 delta absolute max: `0`

## Gate

- Decision: `pass`
- Blocking checks: `none`

## Evidence

- NameCert: `experiments/bedc_jepa/reports/namecert.yaml`
- Ledger: `experiments/bedc_jepa/reports/ledger.json`
- Quality packet: `experiments/bedc_jepa/reports/quality_packet.json`

## Not Claimed

- Executed public JEPA implementation comparison.
- Real-world physics.
- Open-domain semantic naming.
- Lean verification of neural training.
