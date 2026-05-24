# BioReality Deepening Pipeline

This directory defines an independent automation substrate for biological
discovery with newmath/BEDC-style reasoning. It does not start from a benchmark,
a model, a fixed external dataset, or the BEDC paper pipeline. It starts from a
biological guess, rewrites it into minimal distinctions, derives probes,
contacts external reality, records mismatch, and keeps mechanism or
total-biology overclaim blocked until separately justified.

External biological sources are reality contact points. They constrain the
conjecture, but they do not automatically supply mechanism, causality, or
global biological law.

The JSONL files under `inbox/` are local research memory. They may be seeded by
the pipeline itself, inspected by a human, or carried across local cycles. They
are not assumed to exist before the first run.

## Durable files

- `conjecture.schema.json` records a biological conjecture and its BEDC
  minimal form.
- `reality_contact.schema.json` records an external reality contact and the
  boundary of what it can and cannot test.
- `probe.schema.json` records a falsifiable consequence derived from BEDC
  structure or a reality hint.
- `mismatch.schema.json` records alignment, mismatch, underdetermination, or
  blocked-null outcomes.
- `dna_to_protein_ladder.json` records the first domain profile for the
  DNA-to-protein realization ladder.
- `deepening_gates.py` validates records and blocks overclaim.
- `store.py` provides JSONL state loading and writing.
- `framework.py` defines restartable nested loop units and checkpoints.
- `agent_bus.py` defines event records, Codex agent tasks, review records, and
  hardening targets.
- `vision_intake.py` scans user-authored vision files into event records.
- `lanes.py` defines the `bio-V`, `bio-P`, `bio-G`, `bio-R`, `bio-W`, `bio-Q`, and
  `bio-A` local lanes.
- `bio_reality_loop.py` runs one deterministic deepening cycle and plans the
  next tasks.
- `signal_assimilator.py` summarizes loop output into local pipeline signals.
- `supervisor.py` repeats the loop and signal assimilation on a local cadence.
- `papers/bio_reality/main.tex` and `papers/bio_reality/parts/` are the
  standalone paper writeback surface. The writeback lane may update these files
  after deterministic gates pass.

Runtime input and output paths are ignored by Git:

- `tools/bio_reality/inbox/`
- `tools/bio_reality/out/`
- `tools/bio_reality/state/`
- `tools/bio_reality/cache/`

## Deepening loop

The intended self-iterating loop is:

```text
biological guess
-> BEDC minimal form
-> derived probes
-> external reality contact
-> mismatch ledger
-> refined conjecture
```

On an empty local memory, `bio-P` bootstraps the first packet set from the
durable DNA-to-protein ladder and the PR220 genetic-code control-tile
discipline: curated genetic-code labels are external reality contacts; the
codon cube/window-six reading is an internal coordinate surface; local tile
structure cannot be promoted to translation, structure, function, or a global
biological law.

The gate checks the research logic, not biological truth. A gate pass means a
packet is internally admissible for the next BioReality cycle. It does not
authorize paper claims, model claims, data commits, or mechanism claims.

The loop reads the current conjectures, contacts, probes, and mismatch records;
runs the gates; builds the conjecture-to-probe-to-contact-to-mismatch chain;
and writes ignored runtime outputs:

```text
tools/bio_reality/out/gate_results.jsonl
tools/bio_reality/out/deepening_tasks.jsonl
tools/bio_reality/out/review_queue.jsonl
tools/bio_reality/out/packet_targets.jsonl
tools/bio_reality/out/events.jsonl
tools/bio_reality/out/agent_tasks.jsonl
tools/bio_reality/out/agent_reviews.jsonl
tools/bio_reality/out/hardening_targets.jsonl
tools/bio_reality/out/lane_dashboard.md
```

## Lanes

The automation follows a P/V/G/R/W/Q/A split, mirroring the project-level
P/R/gate/taste discipline without importing BEDC paper or Lean write authority
into this directory.

- `bio-P` is the discovery packet lane. It bootstraps or extends conjectures,
  probes, contacts, and mismatch records, then writes runtime packet targets for
  the next local biological deepening step.
- `bio-V` is the vision lane. It scans `tools/bio_reality/vision/*.md`, appends
  intake rows, and emits events for ready or blocked directions.
- `bio-G` is the gate lane. It runs deterministic checks that separate external
  curated reality, BEDC internal coordinates, derived probes, mismatch ledgers,
  and mechanism claims.
- `bio-R` is the research-agent lane. It converts gate outputs and task pressure
  into event-driven Codex task prompts for named agents. By default it dispatches
  one Codex task per supervisor cycle; `--plan-only` is only for dry-run
  inspection.
- `bio-W` is the writeback lane. It reads gate-passed research memory and writes
  the standalone BioReality paper with explicit external-reality, internal
  derivation, probe, mismatch, and cannot-claim sections.
- `bio-Q` is the quality lane. It reads agent reviews and turns pass/fail reasons
  into gate or prompt hardening targets for later cycles.
- `bio-A` is the assimilation lane. It summarizes blocked packets, task
  pressure, review readiness, and packet targets into local signals that can
  harden the next cycle.

The supervisor runs these lanes as restartable loop units. Each unit has an
independent checkpoint in `tools/bio_reality/state/loop_state.json`, and
failures are localized to the failing unit. No lane merges branches, writes to
the BEDC paper pipeline, edits Lean files, pushes remote refs, or turns
un-gated signals into biological conclusions. The only durable paper write
authority in this pipeline is the BioReality paper surface named above.

This matches the useful part of the loning automation pattern: a long-lived
vision or goal is scanned into concrete targets; gates decide whether the target
is admissible; successful content is written into stable manuscript sources;
runtime ledgers remain auxiliary and are not themselves the paper.

The event-driven rule is: gates and task planners emit events; events select an
agent and action; the agent task carries allowed write paths and a complete
prompt; review records classify whether the result is ready, needs research
execution, or requires gate hardening; quality targets feed the next cycle.
Pass and fail outcomes both remain useful because each produces structured
reasons.

## DNA-to-protein boundary

The initial domain profile separates:

```text
code_read
orf_eligibility
translation_realization
structural_order
physical_admissibility
function_realization
```

No layer may be silently promoted to a higher layer. Codon assignment is not
protein realization; amino-acid sequence is not folded structure; folded
structure is not physical admissibility; physical admissibility is not
biological function; functional evidence is not universal mechanism.

## Local check

```bash
python3 tools/bio_reality/deepening_gates.py --self-test
python3 tools/bio_reality/bio_reality_loop.py --self-test
python3 tools/bio_reality/vision_intake.py --self-test
python3 tools/bio_reality/agent_bus.py --self-test
python3 tools/bio_reality/lanes.py --self-test
python3 tools/bio_reality/supervisor.py --once
```
