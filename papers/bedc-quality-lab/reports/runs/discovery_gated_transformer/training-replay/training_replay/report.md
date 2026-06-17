# Discovery-Gated Transformer Training Replay

- run_id: `training-replay`
- schema_id: `bedc-quality-lab:discovery-gated-transformer-training-replay`
- replay digest: `8204ada44f2a33df4235efa2d68bed1010cd118c2b4d791cd467cb97cb976eb0`
- overall state: `pass`

## TRAIN-HG

- `TRAIN-HG1`: `pass` at `$.replay_digest`
- `TRAIN-HG2`: `pass` at `$.compute_ledger.rows`
- `TRAIN-HG3`: `pass` at `$.records`
- `TRAIN-HG4`: `pass` at `$.summary.control_families`
- `TRAIN-HG5`: `pass` at `$.summary.metric_means.dgt_full.uer`
- `TRAIN-HG6`: `pass` at `$.summary.metric_means.dgt_full.false_ledger_rate`
- `TRAIN-HG7`: `pass` at `$.summary.metric_means.dgt_full.benefit`
- `TRAIN-HG8`: `pass` at `$.summary.metric_means.dgt_full.classifier_shift`
- `TRAIN-HG9`: `pass` at `$.sidecar_pointers`
- `TRAIN-HG10`: `pass` at `$.run_artifacts.training_replay`

## Run Artifacts

- training_replay: `reports/runs/discovery_gated_transformer/training-replay/training_replay/training_replay.json`
- raw_metrics: `reports/runs/discovery_gated_transformer/training-replay/training_replay/raw_metrics.jsonl`
- compute_ledger: `reports/runs/discovery_gated_transformer/training-replay/training_replay/compute_ledger.json`
- claim_capsule: `reports/runs/discovery_gated_transformer/training-replay/training_replay/claim_capsule.json`
- evidence_envelope: `reports/runs/discovery_gated_transformer/training-replay/training_replay/evidence_envelope.json`
- report: `reports/runs/discovery_gated_transformer/training-replay/training_replay/report.md`
- summary: `reports/runs/discovery_gated_transformer/training-replay/training_replay/summary.json`
