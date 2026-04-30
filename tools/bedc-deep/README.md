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

## BEDC Boundary

| Dimension | Automath outreach | BEDC deep reasoning |
|---|---|---|
| Target | Solve open problems outside the project | Deepen the current BEDC paper state |
| Output | Standalone short paper, issue, or forum post | Claim packet for BEDC chapter development |
| Reference direction | External references plus project evidence | BEDC internal chapter references plus mathlib-free evidence |
| Publication route | Venue-specific submission rhythm | BEDC-controlled paper rhythm |
| First move | First-mover external contribution | Structural hardening of the current theory |

## Red Lines

These rules mirror the automath pipeline discipline while adapting it to BEDC:

- No Lean execution: this lane does not run `lake`, `lean`, `elan`, `#eval`, or
  `#check`.
- No Lean edits: this lane does not create or edit files under `lean4/`.
- No paper edits: this lane does not edit `papers/bedc/` or register markers.
- No publication: this lane does not submit issues, PRs, forum posts, email, or
  releases.
- No replacement proof: ChatGPT output is a reasoning transcript or claim
  packet, not a checked BEDC theorem.
- Boundary classification is mandatory: every substantive claim is classified as
  `Derived`, `NeedsDefinition`, `NeedsSetupField`, `NarrativeOnly`,
  `TooStrong`, or `False`.

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

Check server status:

```bash
python3 tools/bedc-deep/oracle_client.py --status
python3 tools/bedc-deep/oracle_client.py --watch-status 5
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

Wait for an active BEDC ChatGPT tab before submitting:

```bash
python3 tools/bedc-deep/oracle_client.py B-01 --preflight-agent-wait 60
```

Ask for a terminal claim packet after the loop:

```bash
python3 tools/bedc-deep/oracle_client.py B-01 --max-turns 6 --write-packet
```

Cancel stuck queued or pending work:

```bash
python3 tools/bedc-deep/oracle_client.py --cancel-task <task_id>
python3 tools/bedc-deep/oracle_client.py --cancel-all
```

The oracle server expected by `oracle_client.py` is `http://localhost:8767`.
This is intentionally separate from automath outreach on `http://localhost:8766`,
so both projects can run in parallel.

Runtime state and generated target artifacts are ignored by git.
