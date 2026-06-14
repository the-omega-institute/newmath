# BEDC-JEPA autoresearch pipeline

This is the self-deepening target of the BEDC-JEPA autoresearch loop. The
automation is not a retrieval layer for one experiment. It keeps a research
memory over hypotheses, evidence contacts, experiments, verdicts, gates, and
paper boundaries, then emits the next research tasks needed to deepen the
failure-aware world-model program.

The default loop is `research_loop.py`. It reads the current research memory,
runs deterministic gates, and writes:

- `state/deepening_tasks.jsonl`: prioritized research pressure.
- `state/review_queue.jsonl`: verdicts ready or blocked for review.
- `state/events.jsonl`: event stream for later agent dispatch.
- `state/agent_tasks.jsonl`: planner, experimentalist, reviewer, and writer
  prompts.
- `state/lane_dashboard.md`: compact status dashboard.

Experiments are inputs to the loop, not its purpose. A finding becomes
authoritative only after the mechanical gates (`gates.py`) and an independent
adversarial verification (`verification.py`) clear it.

- `runners/`: deterministic experiment runners for verified hypotheses.
- `findings/verified_findings.md`: authoritative findings only.
- `findings/adversarial_verdicts.jsonl`: adversarial review verdicts.
- `research_loop.py`, `executor.py`, `gates.py`, `verification.py`, `lanes.py`,
  `store.py`, and `schemas.py`: the pipeline.
- `g2n_research_loop.py`: a dedicated closure lane for the G2N A100 experiment
  rows. It is one evidence producer consumed by the research loop, not the
  automation's main target.

Large latent/cache intermediates are not committed; runners regenerate them
from the public LeWorldModel checkpoints or fail closed when artifacts are
missing.

## Research Loop

Run one research-deepening cycle:

```bash
python autoresearch/research_loop.py
```

Run the self-test:

```bash
python autoresearch/research_loop.py --self-test
```

The loop is axis-oriented. It asks whether the current evidence covers
detection, horizon semantics, selective admission, allocation, compute value,
representation shaping, OOD fail-closed behavior, tail risk, and paper-boundary
writeback. If an axis has no authoritative finding, the loop emits a task
rather than inventing a claim.

The compute-value axis treats failure probability and allocation value as
distinct targets. A valid packet must name candidate compute options `b`, such
as rollout depth, refinement, or abstention, and must supply direct
option-level marginal-value labels `MV(t,b)` from option-level errors. It is
not enough to sort anchors by a failure score and call that an allocation
model. The registered runner `fi-021.compute-value-world-model.py` evaluates
`reports/compute_value_labels.npz` when present, requiring `episode`,
`option_error`, `uniform_error`, and `predicted_mv`; otherwise it fails closed
and keeps the missing label artifact as research pressure.

## Experiment Execution

The execution adapter compiles open hypotheses into deterministic runners,
executes available runners twice, and lets the same gate stack decide whether
the verdict can be written back:

```bash
python autoresearch/executor.py --max-workers 1
```

Missing runners or missing artifacts remain research pressure. They do not
alter paper claims.

## G2N Closure Lane

The G2N lane keeps the autoresearch gate discipline but points it at one
experiment family: direct paired comparison against the strongest post-hoc
probe, calibration-only selective admission, and the shuffled-label
capacity-artifact guard for the integrated A100 row.

Run one local cycle without remote artifact fetch:

```bash
python autoresearch/g2n_research_loop.py --once
```

Run one cycle that also pulls finished A100 artifacts from the configured Slurm
workspace before executing the local closure analyses:

```bash
python autoresearch/g2n_research_loop.py --once --pull-remote
```

For a cadence loop, omit `--once` and set `--interval-seconds`. Missing A100
artifacts remain pending/fail-closed; they do not alter paper claims or
verified findings. Finite artifacts are summarized in
`reports/g2n_integrated_a100_closure_status.json`, and the corresponding
autoresearch runners are `fi-018`, `fi-019`, and `fi-020`.
