# BEDC-JEPA Directive

## Position

BEDC-JEPA is not a post-hoc report on an existing JEPA representation.  The
paper unit studies a BEDC-native world-model training principle:

```text
world state = continuous latent state + operational distinctions + gap ledger
```

The current lab keeps the LeJEPA-style Gaussian-OU runner as a calibration
baseline.  The next scientific target is different: train models whose state
contains not only `z_t`, but also distinction heads `d_t` and gap heads `g_t`.

## Central Claim

A world model should not only predict future latent states.  It should also
learn which distinctions are stable enough to claim, and where its own
prediction or classifier surface has unresolved gaps.

The intended model class is:

```text
E_theta(o_t) -> z_t
D_phi(z_t) -> d_t
G_psi(z_t, d_t) -> g_t
F_omega(z_t, d_t, g_t, a_t) -> (z_{t+1}, d_{t+1}, g_{t+1})
```

Here `d_t` is not a natural-language semantic label.  It is an operational
distinction with transition, intervention, or planning consequences.  `g_t`
is an explicit failure or uncertainty ledger state, not a report written after
training.

## First World

The first controlled world is the boundary-gated OU world:

```text
z_t in R^2
z_{t+1} = rho z_t + sqrt(1-rho^2) eta
d_t = 1[||z_t||^2 <= r^2]
g_t = 1[abs(||z_t||^2 - r^2) <= epsilon]
x_t = nonlinear_mix(z_t)
```

The inside/outside predicate is the operational distinction.  The boundary
band is the gap ledger.  A model can make low-gap distinction claims; it must
not treat near-boundary cases as equally certified.

## Baselines

The paper should compare four systems:

```text
1. LeJEPA-style latent prediction
2. LeJEPA-style representation plus post-hoc probe
3. LeJEPA-style representation plus post-hoc BEDC report
4. BEDC-JEPA with distinction and gap heads trained in the objective
```

Only the fourth system is the model contribution.  The third system is useful
as an ablation that demonstrates why reporting alone is not enough.

## Loss Sketch

The full BEDC-JEPA objective should be:

```text
L = L_latent_prediction
  + lambda_d L_distinction
  + lambda_s L_stability
  + lambda_i L_intervention
  + lambda_g L_gap
  + lambda_u L_unlogged_error
  + lambda_p L_gap_aware_planning
```

The key term is `L_unlogged_error`: prediction or distinction errors inside a
declared critical scope must be accompanied by an activated gap head.  The
model may be wrong, but it must not be confidently and silently wrong.

## Metrics

The lab reports JEPA-style metrics and BEDC-JEPA metrics separately.

JEPA-style metrics:

```text
linear_identifiability_r2
orthogonality_error
covariance_deviation
```

BEDC-JEPA metrics:

```text
distinction_accuracy
distinction_accuracy_outside_gap
gap_detection_auc
false_claim_rate_inside_gap
unlogged_error_rate
certified_coverage
bedc_debt_score
```

The primary metric is `unlogged_error_rate`.  If two models have comparable
latent recovery, the model with fewer unlogged distinction or transition
failures has the stronger BEDC world-model quality claim.

## Contact Artifact

Before contacting the LeJEPA authors, produce a one-page note and one table:

```text
LeJEPA baseline: latent recovery only
BEDC-JEPA: latent recovery + distinction accuracy + gap calibration
```

The message should not say that BEDC explains their latent.  It should say
that LeJEPA identifies latent geometry, while BEDC-JEPA studies a complementary
training objective for certifiable distinctions and gap-aware world states.

## Scope Boundary

This lab does not claim:

```text
complete autonomous intelligence
full Lean verification of the model
LLM behavior quality
large-scale pixel world modeling
natural-language semantic grounding
```

The current branch establishes the first executable protocol and report
surface for the boundary-gated world.  Full gradient-trained BEDC-JEPA heads
are the next implementation unit.
