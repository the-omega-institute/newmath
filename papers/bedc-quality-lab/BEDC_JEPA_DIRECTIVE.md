# BEDC-JEPA Directive

## Position

BEDC-JEPA is not a post-hoc report on an existing JEPA representation.  The
paper unit studies a BEDC-native world-model training principle:

```text
world state = continuous latent state + operational distinctions + gap ledger
```

The lab keeps the LeJEPA-style Gaussian-OU runner as a calibration baseline.
The scientific target is different: evaluate world-model carriers by whether
they support operational distinctions and explicit gap ledgers, and train
BEDC-JEPA heads when the supervision surface is declared.

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

## Evidence Scope

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

The current evidence record also includes public MiniGrid-DoorKey readback,
public MiniGrid debt decomposition and risk-success Pareto summaries,
object-counterfactual and distractor settings, a public V-JEPA2-AC Giant
checkpoint-scope CUDA adapter evaluation, a fixed-checkpoint V-JEPA2-AC
MiniGrid latent-prediction evaluation, and a fixed-carrier V-JEPA2-AC LCCP
certificate record.

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

## Objective Terms

The BEDC-JEPA objective is:

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

The current true retraining loss-term record is scoped to the boundary-gated
torch objective. It contains retrained `full_s3`, `minus_l_unlogged`,
`minus_l_gap`, `minus_l_stab`, and `minus_l_intervention` rows. In that
setting, removing `L_gap` preserves latent recovery while collapsing gap
ranking and certified coverage; removing `L_unlogged_error`, `L_stability`,
or `L_intervention` does not create an independent positive effect because the
retrained systems already have zero mean UER and the declared stability and
intervention surfaces are narrow OU-pair surfaces.

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

## External Evaluation Boundary

The current external-facing record can support a bounded evidence discussion:

```text
BEDC-JEPA: latent recovery + operational distinction + gap ledger
LCCP: certified singleton claim or declared coverage/source/stability debt
V-JEPA2-AC: fixed-checkpoint MiniGrid evaluation, not official benchmark reproduction
```

The message should not say that BEDC explains another model's latent space.
It should say that identifiability work studies latent geometry, while
BEDC-JEPA and LCCP study which operational claims can be certified and which
must remain ledgered as gap or source debt.

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
surface for the boundary-gated world, plus public MiniGrid and
fixed-checkpoint V-JEPA2-AC evidence records. It still does not establish
official/native V-JEPA2-AC benchmark reproduction, public benchmark
superiority, robotics-scale control, or natural-video object interaction.
