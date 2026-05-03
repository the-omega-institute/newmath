# BEDC Deep Reasoning Tools

Self-iterating BEDC paper-extension loop. Drives ChatGPT Pro multi-turn deep
reasoning on each `BOARD.md` target, captures the result as canonical LaTeX,
and appends into `papers/bedc/parts/`. The downstream `lean4-codex-auto-dev`
formalization lane picks up new theorem sites by scanning the paper — there
is no API handshake, only files.

Existing newmath automation this complements:
- `lean4/scripts/codex_formalize.py`: codex-driven Lean formalization rounds.
- `lean4/scripts/lake_gate.py`: shared Lake concurrency guard.
- `lean4/scripts/bedc_ci.py`: paper to Lean marker drift audit.
- `.github/workflows/pr-gate.yml`, `daily-build.yml`: path-based PDF + Lean gates.

## Architecture

```
loop:
  pick unfinished target from BOARD.md
    │
    ▼
  Stage 1: oracle deep reasoning (codex orchestrator drives)
    - codex per turn outputs {progress_delta, contribution, next_prompt}
    - safety nets: 3 consecutive low-progress turns OR 12h wall-clock
    - response regex: BREAKTHROUGH / Q.E.D. / STUCK
    - per-turn checkpoint to state/<target>/cursor.json (resumable)
    - terminal turn: WRITE_PAPER_LATEX → raw LaTeX block
    │
    ▼
  Stage 1.5: topic discovery (only if Stage 1 verdict=done)
    - codex extracts adjacent claim candidates from full transcript
    - filters by fit_score ≥ 7, novelty ≥ 6, non-duplicate title
    - appends accepted candidates to BOARD.md as new B-XX rows
    │
    ▼
  Stage 2: killo-golden writeback (only if Stage 1 verdict=done)
    - independent `claude -p` reviewer reads transcript + raw LaTeX
    - applies 10-item BEDC hygiene checklist
    - if accept: append cleaned content into papers/bedc/parts/<theme>/<file>.tex
    - run `cd papers/bedc && make` to verify; rollback on compile failure
```

## Hygiene checklist (Stage 2)

Stage 2 rejects any LaTeX that violates these (full text in
`prompts/killo_golden_writeback.txt`):

1. No `\part` / `\chapter` / `\section` / `\subsection` openings (appended
   into existing chapters).
2. No iteration vocabulary: `extend / 修订 / 增量 / patch / increment / 新增 /
   本次 / 本轮 / vNNN- / legacy / supersede`.
3. No marker macros: `\leanchecked`, `\leanvariant`, `\leansorryd`,
   `\leanstmt`, `\leandef` (added later by `codex_formalize`).
4. ≥1 of `theorem / lemma / proposition / definition / corollary` with
   `\label{…}`.
5. Labels are semantic (no version prefix).
6. After append, target file ≤ 800 lines.
7. Target is a concrete body file, not `main.tex` or a wrapper.
8. Math uses only `$...$` and `$$...$$`; `$$` on its own line.
9. Inline Lean snippets (if any) have no `axiom` / `sorry` /
   `import Mathlib`.
10. LaTeX content is English (BEDC paper body is English-only).

## Lane edge

This lane never edits `lean4/`. Stage 2 only writes to
`papers/bedc/parts/<theme>/<concept>.tex`. The handshake to the formalization
lane is the appended LaTeX, with NO marker macros. The downstream
`codex_formalize.py` Phase B grep scan picks up unmarked theorem sites
automatically.

## Commands

List targets:

```bash
python3 tools/bedc-deep/dispatch_bedc_target.py --list
```

Print one initial prompt (with prior-art block):

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

Run a single target through Stage 1 → 1.5 → 2:

```bash
python3 tools/bedc-deep/oracle_client.py B-01 --preflight-agent-wait 60
```

Run the full board loop (sequential, picks unfinished targets until none left):

```bash
python3 tools/bedc-deep/oracle_client.py --loop --preflight-agent-wait 60
```

Run the loop in parallel across N ChatGPT tabs (cap to active tabs; server
allows up to `MAX_AGENTS = 3`). Open `?bedc=1`, `?bedc=2`, `?bedc=3` first:

```bash
python3 tools/bedc-deep/oracle_client.py --loop --parallel 3 --preflight-agent-wait 60
```

Scan the paper for theory gaps (conjecture / question blocks, TODO comments,
"remains open" / "to be proved" / 未证 prose, orphan definitions) and
optionally append qualifying ones to BOARD.md as auto-spawned candidates:

```bash
python3 tools/bedc-deep/paper_gap_scanner.py            # list only
python3 tools/bedc-deep/paper_gap_scanner.py --append   # append to BOARD.md
python3 tools/bedc-deep/paper_gap_scanner.py --json     # machine-readable
```

Active target discovery — codex proposes, claude gates, accepted candidates
land on BOARD.md (same shape as Stage 1.5 fan-out):

```bash
# Global structural gap scan over papers/bedc/parts + lean4/BEDC
python3 tools/bedc-deep/auto_discovery.py probe --append

# Meta-review after a batch of completed targets — proposes under-represented
# directions across already-finished transcripts
python3 tools/bedc-deep/auto_discovery.py curator --append
```

Both commands write the full audit record (codex output, claude verdict per
candidate, appended ids) to `state/discovery_logs/<mode>_<ts>.json`.

## Supervisor (recommended for unattended runs)

`supervisor.py` is the outer-loop wrapper that keeps the pipeline alive
without manual babysitting:

- spawns `oracle_client.py --loop` and restarts it on crash with backoff
- ensures `bedc_oracle_server.py` is up; respawns if missing
- prunes stale `.in_progress` markers each pass (also fixed at oracle_client
  startup for direct invocations)
- when BOARD unfinished count drops below `--low-water`, triggers probe
- after `COMPLETIONS_PER_CURATOR` (5) targets land, triggers curator
- when `papers/bedc/parts/` or `BOARD.md` change, auto-commits and pushes
- alerts when `queue_waiting_for_browser_agent` stays stuck > 5 min
  (browser tabs probably went idle)
- every `--claude-review-hours` (6h default), runs a `claude -p` progress
  review over state + server snapshot; verdicts with
  `recommend_probe` / `recommend_curator` are auto-applied within their
  cooldowns; flagged `stuck_targets` and `concerns` are logged for human

Start (background, no on-boot):

```bash
nohup python3 tools/bedc-deep/supervisor.py --parallel 3 \
  > tools/bedc-deep/state/supervisor_logs/supervisor.out 2>&1 &
```

Stop cleanly:

```bash
touch tools/bedc-deep/.stop
# or: kill <supervisor pid>; supervisor will SIGTERM the inner loop
```

Disable individual tiers if needed:

```bash
python3 tools/bedc-deep/supervisor.py --no-claude-review --no-auto-commit
```

Logs land in `tools/bedc-deep/state/supervisor_logs/`:
- `supervisor.log` — supervisor's own decisions
- `inner.log` — oracle_client.py --loop stdout/stderr concatenated across restarts

## Target lifecycle

`lifecycle.py` classifies every final state into a `failure_kind` and
records `attempts` / `retry_budget` / `next_action` on the state file.
The supervisor's retry sweep uses these to decide what to do, instead of
the coarse stage1_verdict bucket. Failure kinds:

| kind | retry_budget | next_action | meaning |
|---|---|---|---|
| `none` | 0 | complete | Stage 2 accepted, paper updated |
| `pre_flight_duplicate` | 0 | skip | already_in_paper detection |
| `stage2_duplicate_content` | 0 | skip | Stage 2 caught a real duplicate |
| `oracle_transport_failure` | 5 | retry_resume | empty / short / extractor failure |
| `oracle_timeout` | 3 | retry_resume | poll exhausted |
| `agent_error` | 5 | retry_resume | userscript ERROR or transport bug |
| `format_crash` | 3 | retry_resume | Python error (legacy format() bug class) |
| `wall_clock_exhausted` | 1 | retry_resume | 12h ceiling hit |
| `math_stuck` | 0 | skip | three turns ≤ 1 progress |
| `stage2_hygiene_reject` | 0 | alert_user | needs prompt repair |
| `stage2_compile_failed` | 1 | retry_resume | pdflatex failed after append |
| `stage2_blocked_after_retries` | 0 | alert_user | corrective retry exhausted |

`lifecycle.reset_retriable()` runs at oracle_client startup and on every
supervisor sweep: it walks `state/*.json`, finds entries whose
`next_action == retry_resume` and `attempts <= 6`, deletes the final
state file, and bumps `cursor.json.attempts` so the resumed run picks
up from the saved turns.

## Dashboard

Single-screen status view:

```bash
python3 tools/bedc-deep/dashboard.py
```

Shows: server diagnosis, BOARD breakdown, target lifecycle table,
failure_kind histogram, Stage 2 reject clusters, recent commits,
supervisor log tail. Refresh with `watch -n 30 python3
tools/bedc-deep/dashboard.py` for a live view.

Tune Stage 1.5 spawn aggressiveness (lower thresholds → more candidates,
lower quality):

```bash
python3 tools/bedc-deep/oracle_client.py --loop --parallel 3 \
  --candidate-fit-threshold 6 --candidate-novelty-threshold 5
```

Server status / control:

```bash
python3 tools/bedc-deep/oracle_client.py --status
python3 tools/bedc-deep/oracle_client.py --watch-status 5
python3 tools/bedc-deep/oracle_client.py --cancel-task <task_id>
python3 tools/bedc-deep/oracle_client.py --cancel-all
```

Smoke test the codex orchestrator with a saved prompt:

```bash
python3 tools/bedc-deep/codex_orchestrator.py /path/to/prompt.txt
```

Run Stage 2 manually for a finished Stage 1 target:

```bash
python3 tools/bedc-deep/killo_golden_writeback.py B-01 \
  --transcript-dir tools/bedc-deep/targets/b_01_psame_base_inversion \
  --raw-latex     tools/bedc-deep/targets/b_01_psame_base_inversion/raw_oracle_latex.md
```

## Server port

The oracle server expected by `oracle_client.py` is `http://localhost:8767`
(automath outreach uses :8766; both can run side by side).

## State and artifacts

- `state/<slug>.json` — final per-target state (turns, verdict, spawned ids,
  Stage 2 result).
- `state/<slug>/cursor.json` — per-turn checkpoint for resumability.
- `state/codex_logs/` — codex orchestrator prompts + outputs (audit trail).
- `state/stage2_logs/` — Stage 2 Claude prompts + outputs.
- `targets/<slug>/turn_NN_*.md` — per-turn prompts and responses.
- `targets/<slug>/raw_oracle_latex.md` — terminal WRITE_PAPER_LATEX output.
- `targets/<slug>/candidates.json` — Stage 1.5 topic discovery output.
- `targets/<slug>/stage2_result.json` — Stage 2 verdict and target file path.

All runtime state and generated target artifacts are gitignored.
