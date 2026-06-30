# Evaluation Note Draft

Subject: BEDC-JEPA: certified operational claims for world-model latents

Hi David, Yann, Randall,

We read "When Does LeJEPA Learn a World Model?" with particular interest in
the latent identifiability theorem, the planning connection, and the proof
inventory. We are exploring a complementary direction rather than a
reinterpretation of that result.

The question is whether a JEPA-style world model can be evaluated and trained
not only for continuous latent state, but also for operational distinctions
and explicit gap ledgers:

```text
world state = z_t + d_t + g_t
```

Here `d_t` denotes testable distinctions with transition, intervention, or
planning consequences, and `g_t` denotes states where the model should not make
an unqualified world-state claim.

The current BEDC-JEPA evidence record contains:

```text
S0 latent / prediction only
S1 post-hoc probe
S2 post-hoc BEDC report
S3 trained BEDC-JEPA distinction + gap readback
```

The evidence packet includes boundary worlds, a grid-pixel learned-transition
benchmark, a MiniGrid-style visual planning benchmark, two-object
counterfactual intervention, four-object distractor sweeps, six-object clutter
sweeps, a native MiniGrid-DoorKey S0/S1/S2/S3 packet, public MiniGrid
debt/calibration records, public V-JEPA2-AC Giant checkpoint-scope CUDA
evaluation, fixed-checkpoint V-JEPA2-AC MiniGrid latent prediction, and a
fixed-carrier V-JEPA2-AC Latent Claim Certificate Protocol record.

Selected current numbers:

```text
torch objective latent R^2 delta:                    0.000000
torch objective gap AUROC gain, BEDC - latent-only:  0.499223
torch objective gap AUROC gain mean, three seeds:    0.498762
torch objective debt reduction mean, three seeds:    0.102887
grid transition one-step R^2:                         0.998237
MiniGrid-style transition one-step accuracy:          1.000000
MiniGrid-style gap AUROC gain, S3 - S2:               0.428459
MiniGrid-style risk-adjusted planning gain:           0.313494
two-object counterfactual accuracy mean:              0.932750
four-object counterfactual accuracy mean:             0.940694
six-object clutter counterfactual accuracy mean:      0.946607
native MiniGrid S0-minus-S3 UER reduction mean:       0.067188
native MiniGrid S3-minus-S0 gap AUROC gain mean:      0.185662
V-JEPA2-AC MiniGrid latent-prediction score:          0.981246
V-JEPA2-AC MiniGrid linear-aligned R^2:               0.980652
```

The intended contribution is a model objective and a certificate protocol, not
a post-hoc report. Distinction heads and gap heads are part of trained
world-state readback in BEDC-JEPA. For arbitrary fixed carriers, LCCP returns
either a certified singleton operational claim or an explicit coverage/source
/stability debt row.

The CUDA retraining loss-term record is scoped to the boundary-gated torch
objective. It contains true retraining rows for `full_s3`,
`minus_l_unlogged`, `minus_l_gap`, `minus_l_stab`, and
`minus_l_intervention`. Removing `L_gap` preserves latent recovery while
collapsing gap ranking and certified coverage. Removing `L_unlogged`,
`L_stability`, or `L_intervention` does not produce an independent positive
effect in this setting because all retrained rows have zero mean UER and the
declared stability/intervention surfaces are narrow OU-pair surfaces.

The public MiniGrid record supports the UER and gap-ranking directions while
also exposing an unresolved debt-calibration problem and a risk-success
planning tradeoff. The V-JEPA2-AC records are fixed-checkpoint evaluations:
they do not claim official/native V-JEPA2-AC benchmark reproduction, public
benchmark superiority, or certified semantic grounding.

Reproducible local commands:

```text
python scripts/run_bedc_jepa_experiment.py
python scripts/run_torch_bedc_jepa.py
python scripts/run_torch_retraining_loss_ablation.py
python scripts/run_bedc_latent_claim_certificate.py
python scripts/run_vjepa2_ac_minigrid_claim_certificate.py
python scripts/run_vjepa2_ac_minigrid_latent_prediction.py
python scripts/build_public_jepa_baseline_registry.py
python scripts/build_bedc_jepa_external_run_kit.py
python scripts/build_bedc_jepa_artifact_manifest.py
python scripts/build_bedc_jepa_readiness.py
python scripts/build_bedc_jepa_review_bundle.py
python scripts/build_bedc_jepa_quality_backend_candidate.py
python -m pytest -q
```

Would this be a useful complementary evaluation direction or add-on benchmark
to discuss?

Best,
