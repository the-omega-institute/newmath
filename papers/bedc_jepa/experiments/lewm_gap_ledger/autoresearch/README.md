# LeWM autoresearch pipeline (gated writeback)

This is the self-writeback target of the LeWM autoresearch loop. The loop
compiles open hypotheses into deterministic runners, executes them, and a
finding becomes authoritative only after the mechanical gates (`gates.py`) **and** an independent adversarial verification (`verification.py`) clear it.

- `runners/` — deterministic experiment runners for the **verified** hypotheses.
- `findings/verified_findings.md` — authoritative findings only (artifacts/pending held back).
- `findings/adversarial_verdicts.jsonl` — the adversarial review verdicts.
- `executor.py` / `gates.py` / `verification.py` / `lanes.py` / `store.py` / `schemas.py` — the pipeline.
- `g2n_research_loop.py` — the target-oriented G2N loop that first refreshes
  A100 closure artifacts, then runs the same executor/gate/writeback stack.

Large latent/cache intermediates are not committed; runners regenerate them
from the public LeWorldModel checkpoints (see the parent experiments README).

## G2N target loop

The G2N loop is the article's automatic continuation mechanism for the
BEDC-native world-model target.  It keeps the autoresearch gate discipline but
points it at the current binding questions: direct paired comparison against the
strongest post-hoc probe, calibration-only selective admission, and the
shuffled-label capacity-artifact guard for the integrated A100 row.

Run one local cycle without remote artifact fetch:

```bash
python autoresearch/g2n_research_loop.py --once
```

Run one cycle that also pulls finished A100 artifacts from the configured Slurm
workspace before executing the local closure analyses:

```bash
python autoresearch/g2n_research_loop.py --once --pull-remote
```

For a cadence loop, omit `--once` and set `--interval-seconds`.  Missing A100
artifacts remain pending/fail-closed; they do not alter paper claims or verified
findings.  Finite artifacts are summarized in
`reports/g2n_integrated_a100_closure_status.json`, and the corresponding
autoresearch runners are `fi-018`, `fi-019`, and `fi-020`.
