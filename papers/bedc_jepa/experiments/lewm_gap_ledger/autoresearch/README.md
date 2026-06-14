# LeWM autoresearch pipeline (gated writeback)

This is the self-writeback target of the LeWM autoresearch loop. The loop
compiles open hypotheses into deterministic runners, executes them, and a
finding becomes authoritative only after the mechanical gates (`gates.py`) **and** an independent adversarial verification (`verification.py`) clear it.

- `runners/` — deterministic experiment runners for the **verified** hypotheses.
- `findings/verified_findings.md` — authoritative findings only (artifacts/pending held back).
- `findings/adversarial_verdicts.jsonl` — the adversarial review verdicts.
- `executor.py` / `gates.py` / `verification.py` / `lanes.py` / `store.py` / `schemas.py` — the pipeline.

Large latent/cache intermediates are not committed; runners regenerate them
from the public LeWorldModel checkpoints (see the parent experiments README).
