# Contact Note Draft

Subject: BEDC-JEPA: certifiable distinctions and gap-aware world-state learning

Hi David, Yann, Randall,

We read "When Does LeJEPA Learn a World Model?" with particular interest in
the latent identifiability theorem, the planning connection, and the Lean proof
inventory.  We are exploring a complementary direction rather than a
reinterpretation of that result.

The question is whether a JEPA-style world model can be trained to learn not
only continuous latent state, but also operational distinctions and an explicit
gap ledger:

```text
world state = z_t + d_t + g_t
```

Here `d_t` denotes testable distinctions with transition, intervention, or
planning consequences, and `g_t` denotes states where the model should not make
an unqualified world-state claim.

Our local BEDC-JEPA branch now has a four-system ablation:

```text
S0 latent / prediction only
S1 post-hoc probe
S2 post-hoc BEDC report
S3 trained BEDC-JEPA distinction + gap readback
```

The current evidence packet includes boundary worlds, a grid-pixel learned
transition benchmark, a MiniGrid-style visual planning benchmark, two-object
counterfactual intervention, four-object distractor sweeps, and six-object
clutter sweeps.

Selected current numbers:

```text
torch objective latent R^2 delta:                    0.000000
torch objective gap AUROC gain, BEDC - latent-only:  0.499223
torch objective gap AUROC gain mean, three seeds:    0.498762
torch objective debt reduction mean, three seeds:    0.102887
torch objective unlogged error, BEDC:                0.000000
torch objective debt reduction:                      0.096838
grid transition one-step R^2:                         0.998237
MiniGrid-style transition one-step accuracy:          1.000000
MiniGrid-style gap AUROC gain, S3 - S2:               0.428459
MiniGrid-style risk-adjusted planning gain:           0.313494
two-object counterfactual accuracy mean:              0.932750
four-object counterfactual accuracy mean:             0.940694
six-object clutter counterfactual accuracy mean:      0.946607
six-object clutter gap AUROC gain mean, S3 - S2:      0.501613
six-object clutter unlogged-error reduction mean:     0.270000
```

The intended contribution is a model objective, not a post-hoc report:
distinction heads and gap heads are part of the trained world-state readback,
and planning can penalize predicted high-gap states.  The torch objective
artifact keeps the latent carrier fixed and trains the BEDC heads, so the gap
and debt gains are not coming from a different latent recovery score.  In the
visual planning benchmark this reduces high-gap and unsafe state selection
while exposing a real success-rate tradeoff.

We cannot yet claim a public JEPA implementation comparison, a robotics result,
or natural-video object interaction.  We have added a public MiniGrid adapter
probe, but the current local environment does not have `gymnasium` / `minigrid`
installed, so the public MiniGrid run is recorded as unavailable rather than
executed.

Reproducible local commands:

```text
python scripts/run_bedc_jepa_experiment.py
python scripts/run_torch_bedc_jepa.py
python scripts/build_bedc_jepa_artifact_manifest.py
python scripts/probe_public_minigrid.py
python -m pytest -q
```

Would this be a useful extension direction or add-on benchmark to discuss?

Best,
