# Dimension-Mismatch Anti-Triviality

- Artifact: `bedc-quality-lab:dimension-mismatch-anti-triviality`
- Status pointer: `$.status`
- Status: `scale_leakage_detected`
- Recommended projection: `demote_to_DN_or_D1`
- Mechanism status: `not_claimed`
- D5-M status: `not_claimed`
- Source pointer: `reports/canonical/dimension-mismatch-debt-transfer.json:$.dimension_mismatch_debt_transfer.status`
- Scope note: SCOPE_NOTE: requested bedc_quality_lab/gap_head.py and bedc_quality_lab/observed_debt.py do not exist in this checkout; reused the matching helpers from scripts/run_gaussian_ou_gap_ledger_head.py and scripts/run_observed_debt_sweep.py without interface changes.

## Arms

| arm | positive | learned AUROC | matched-random AUROC | delta AUROC | diagnostic wide OR | columns |
| --- | --- | ---: | ---: | ---: | --- | --- |
| `config_metadata_only` | `False` | 1.000000 | 0.593750 | 0.406250 | `True` | `encoder_dim, reference_latent_dim, abs_encoder_dim_minus_reference_dim, is_reference_encoder_dim` |
| `scale_only` | `True` | 1.000000 | 0.576215 | 0.423785 | `True` | `h_l2_mean, h_l2_std, h_abs_mean, h_abs_max, h_abs_q25, h_abs_q50, h_abs_q75, h_pair_delta_l2_mean, h_pair_delta_l2_std` |
| `h_normalized_no_scale` | `True` | 1.000000 | 0.528472 | 0.471528 | `True` | `h_direction_abs_mean, h_direction_abs_max, h_direction_abs_q25, h_direction_abs_q50, h_direction_abs_q75, h_pair_direction_abs_mean, h_pair_direction_abs_max, h_pair_direction_abs_q25, h_pair_direction_abs_q50, h_pair_direction_abs_q75, h_direction_pair_delta_l2_mean, h_direction_pair_delta_l2_std` |

## Hardgates

| gate | status |
| --- | --- |
| `HG-B1-AT1` | `pass` |
| `HG-B1-AT2` | `pass` |
| `HG-B1-AT3` | `pass` |
| `HG-B1-AT4` | `pass` |
| `HG-B1-AT5` | `pass` |
| `HG-B1-AT6` | `pass` |

## Pointer Index

- `$.arms[*]` lists only sidecar-local arm evidence.
- `$.positive_predicate` is the only status-driving positivity rule.
- `$.hardgate_evidence` records HG-B1-AT1..6.
- `$.mechanism_status` and `$.d5m_status` remain `not_claimed`.
