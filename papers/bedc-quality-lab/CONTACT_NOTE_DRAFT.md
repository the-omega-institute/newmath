# Contact Note Draft

Subject: BEDC-JEPA: a small extension direction for certifiable distinctions and gap-aware world states

Hi David, Yann, Randall,

We read "When Does LeJEPA Learn a World Model?" with particular interest in
the orthogonal identifiability result and the Lean proof inventory.

We are exploring a complementary direction rather than a reinterpretation of
your latent recovery theorem.  The question is whether a JEPA-style world model
can be trained to learn not only continuous latent state, but also operational
distinctions and an explicit gap ledger:

```text
world state = z_t + d_t + g_t
```

Here `d_t` denotes testable distinctions with transition or intervention
consequences, and `g_t` denotes cases where the model should not make an
unqualified world-state claim.

Our first small synthetic world is a boundary-gated OU world.  A vanilla
LeJEPA-style model can be evaluated by latent recovery, while BEDC-JEPA is
evaluated by latent recovery plus:

```text
distinction accuracy outside the gap
gap detection AUROC
false claims inside the gap
unlogged error rate
certified coverage
```

The intended contribution is a model objective, not a post-hoc report:
distinction heads and gap heads are trained as part of the world model, and
planning can penalize predicted high-gap states.

Would this be a useful extension direction or add-on benchmark to discuss?
We can share a one-page note and a minimal script first.

Best,
