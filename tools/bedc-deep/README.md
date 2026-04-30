# BEDC Deep Reasoning Tools

This directory connects BEDC proof-obligation targets to a local copy of the
ChatGPT browser bridge used by the automath outreach skeleton, while keeping
this repository out of Lean editing mode.

Existing `newmath` automation already covers:
- `lean4/scripts/codex_formalize.py`: isolated Codex formalization rounds.
- `lean4/scripts/lake_gate.py`: shared Lake concurrency guard.
- `lean4/scripts/bedc_ci.py`: paper to Lean marker audit.
- `.github/workflows/pr-gate.yml`: path-based PDF and Lean gates.
- `.github/workflows/daily-build.yml`: dev branch PDF plus Lean build.

This tool adds only a pre-formalization reasoning lane:

`BOARD.md -> initial prompt -> ChatGPT turns on :8767 -> claim packet`

The claim packet is not a proof artifact. It is advisory input for later human
review or for the existing strict formalization pipeline.

## Commands

List targets:

```bash
python3 tools/bedc-deep/dispatch_bedc_target.py --list
```

Print one initial prompt:

```bash
python3 tools/bedc-deep/dispatch_bedc_target.py --prompt B-01
```

Run the BEDC oracle server:

```bash
python3 tools/bedc-deep/bedc_oracle_server.py
```

Open one or more ChatGPT tabs with the BEDC userscript installed:

```text
https://chatgpt.com/?bedc=1
https://chatgpt.com/?bedc=2
```

Run a ChatGPT deep loop against the BEDC oracle server:

```bash
python3 tools/bedc-deep/oracle_client.py B-01 --max-turns 6
```

Ask for a terminal claim packet after the loop:

```bash
python3 tools/bedc-deep/oracle_client.py B-01 --max-turns 6 --write-packet
```

The oracle server expected by `oracle_client.py` is `http://localhost:8767`.
This is intentionally separate from automath outreach on `http://localhost:8766`,
so both projects can run in parallel.

Runtime state and generated target artifacts are ignored by git.
