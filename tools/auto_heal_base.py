#!/usr/bin/env python3
"""Auto-heal codex-auto-dev BASE: detect stuck dup labels / dup conclusions
and invoke codex to resolve in the main checkout.

Without this daemon, a single round push that lands a duplicate paper
label or a duplicate-conclusion theorem stalls every subsequent round
in audit-fail / SHALLOW-GROWTH cooldown loops until a human (or
emergency-fix run) deletes the duplicate. Observed in 2026-05-06
session: 36 SHALLOW + 9 cooldowns over 30 min until manual deletion
of `TopologySingleton_boundary_open_laws` / `_diffform_derham_boundary_consumption.tex`.

Cycle (every INTERVAL seconds):
  1. cd to main checkout, ensure on `codex-auto-dev`, ff to origin.
  2. run `python3 lean4/scripts/bedc_ci.py audit`. If `duplicate
     paper labels: N (N > 0)` → invoke codex with HEAL_DUP_LABELS_PROMPT.
  3. compare round-side phase_d_lint logic against BASE: if BASE has
     a `\\theorem` whose conclusion is a strict superset of another's
     (and they're in the same .lean file), report.
  4. on any commit codex made: lake build → push to origin.

Default INTERVAL=900s (15 min). Override via env AUTO_HEAL_INTERVAL_SECONDS.

Launch (in main checkout, daemon-style):
  nohup python3 tools/auto_heal_base.py >> scripts/logs/auto_heal.log 2>&1 &
  disown
"""

from __future__ import annotations

import argparse
import json
import os
import shutil
import subprocess
import sys
import tempfile
import time
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
BASE_BRANCH = "codex-auto-dev"
CODEX_PATH = shutil.which("codex") or "/opt/homebrew/bin/codex"
DEFAULT_INTERVAL = 900  # 15 min

HEAL_DUP_LABELS_PROMPT = """You are healing the BEDC paper to remove duplicate paper labels on the codex-auto-dev branch.

Audit reports the following duplicate labels (each appears in 2+ files):
{dups}

## Resolution rules

For each duplicate label X appearing in files A and B:

1. Read both files: `git show :A` and `git show :B` (or just open them).
2. The "canonical site" is the file whose name better matches X's semantic content:
   - If A is a hub (`<n>_<chapter>_namecert_construction.tex` containing only `\\input` lines + a `closurestatus` block) and B is a sibling, the canonical site is B (hubs should not contain labels).
   - If A contains the label as part of a richer obligation surface (multiple `\\begin{theorem}` blocks, a `_namecert_export.tex` style file) and B is a focused single-topic sibling, the canonical site is A.
   - If neither is clearly hub/export, prefer the file whose name's semantic stem best matches the label slug (e.g. `_derham_boundary_consumption.tex` for `thm:diffform-derham-boundary-consumption`).
3. From the NON-canonical file: delete the entire `\\begin{theorem}...\\end{theorem}` (or `\\begin{definition}...\\end{definition}`) block containing the duplicate label. If that leaves the file empty / pure whitespace, delete the file AND remove its `\\input{...}` line from any hub that referenced it.
4. Verify the canonical site still has the label and works: `python3 lean4/scripts/bedc_ci.py audit` should now report 0 dups for the labels you handled.

## Build + commit

5. After all duplicates resolved: `python3 lean4/scripts/bedc_ci.py audit` MUST exit 0 with no `duplicate paper labels` line.
6. `git add` each touched file, `git commit -m "auto-heal: resolve N stuck dup paper labels"` (no push — the daemon does that).

If any duplicate is genuinely ambiguous (canonical site unclear), leave it for a human and explain in your final message.
"""

HEAL_GATE_STORM_PROMPT = """You are healing the BEDC pipeline against a systematic gate-failure storm on the codex-auto-dev branch.

Recent BEDC pipeline observation: a single gate is rejecting many rounds in a short window, indicating a prompt-vs-gate misalignment, a regression, or a missing rule in the phase prompts. The current operator wants to repair it WITHOUT restarting the orchestrator (round prompts are hot-reloaded; code in `codex_formalize.py` / `codex_revise.py` is not).

## Storm summary

Gate signature:   `{gate}`
Window:           {minutes}-min sliding window
Failure count:    {count}
Affected rounds:  {rounds}

Representative failure lines (last 5):
{samples}

## Resolution playbook

1. Identify the rule the gate enforces by inspecting `lean4/scripts/codex_formalize.py` (for R-rounds) or `papers/bedc/scripts/codex_revise.py` (for P-rounds). The gate name above will appear in a `logger.error(...)` line near a `Rejecting round` / `Pre-merge hard gate failed` site.
2. Read the relevant phase prompt file:
   - `lean4/scripts/prompts/phase_b.txt`   — R-side target selection
   - `lean4/scripts/prompts/phase_c.txt`   — R-side implementation
   - `lean4/scripts/prompts/round_fallback_resolve.txt` — R-side recovery codex
   - `papers/bedc/scripts/prompts/phase_review.txt` — P-side target selection
   - `papers/bedc/scripts/prompts/phase_revise.txt` — P-side implementation
   Decide whether the gate is documented as a HARD GATE there. If absent or weakly stated, the prompt is the bug; the gate is correct.
3. Edit ONE prompt file to add an explicit HARD GATE block matching the gate's actual regex / path-match logic. State the rule, the rationale, and an explicit workaround (what codex should do INSTEAD when the natural target would trip the gate). Cite the observed storm: include the count + a representative round id from {rounds} so future readers see the historical justification.
4. Do NOT modify `codex_formalize.py` / `codex_revise.py` themselves — orchestrator restart would lose in-flight workers, which the project rule forbids.
5. Do NOT touch the `parts/visions/` directory, the `lean4/BEDC/**/Examples/**` tree, or any `*Examples*` / `*Scaffold*` / `*Demo*` path; those are read-only by project rule.
6. After editing: `make check` (in `papers/bedc/`) + `python3 lean4/scripts/bedc_ci.py audit` must both exit 0.
7. `git add` + `git commit -m "auto-heal: <gate-name> storm — explicit HARD GATE in <prompt-file>"`. Do NOT push (the daemon handles push).

## When NOT to act

If the storm is genuinely transient (e.g. the gate is for a now-removed file path, or the offending rounds were all dispatched before a recent prompt commit), leave alone and explain in your final message. The next dispatch wave will not reproduce the storm and human intervention is not warranted.
"""

HEAL_DUP_CONCLUSIONS_PROMPT = """You are healing the BEDC Lean library to remove a stuck duplicate-conclusion theorem on the codex-auto-dev branch.

Two theorems in `{file}` have semantically equivalent conclusions and `phase_d_lint.py` rejects every round that merges this BASE:

  Theorem A: {name_a}
  Theorem B: {name_b}

A typical case is theorem B's conclusion being a strict superset of A's (e.g. A is `P ∧ Q`, B is `R ∧ P ∧ Q`). When that holds, A is redundant — derivable from B by `.right` / `.right.right` etc — but as separate theorems they pin the lint forever.

## Resolution

1. Read `{file}`. Inspect both theorem statements and any internal references.
2. If A's conclusion is a strict subset of B's: delete A entirely. For each external reference to A (grep `lean4/BEDC/` and `papers/bedc/`), replace with the equivalent projection of B (e.g. `B.right` or pattern-match on `B`'s structure). Inline the proof if needed (see the `f23474528` precedent removing `TopologySingleton_boundary_open_laws`).
3. If A and B differ only in BHist witness (`BHistCarriesOpen_classifier_transport` vs `BHistGeneratedOpen_classifier_transport`): rename one to make the conclusion clearly distinct (add a meaningful qualifier reflecting the witness shape) so phase_d_lint accepts both. Or delete the parameter-echo one entirely if no external reference needs it.
4. After the change: `cd lean4 && lake build BEDC.Derived.<...>` for the touched module — must pass clean.

## Build + commit

5. `git add` the modified file(s), `git commit -m "auto-heal: remove stuck dup-conclusion theorem in {file}"`.
6. Do NOT push — the daemon does that.

If the duplication is intentional (e.g. both theorems serve documented different audiences and removing either would break downstream), leave alone and explain in your final message.
"""


HEAL_STUCK_DIRT_PROMPT = """You are healing a stuck working tree on the BEDC `codex-auto-dev` branch.

The main checkout has had the same set of tracked modifications for __TICKS__ consecutive heal cycles (__MINUTES_TOTAL__ minutes total). This is NOT a human edit-in-progress — the dirt has not changed across two ticks. A daemon (paper_builder_daemon, sync_with_auto_dev, or a stray codex round that wrote to the main checkout instead of its worktree) left work uncommitted, and the dirt now blocks every other heal pathway (axiom-purity storm repair, dup-label repair, etc.).

Your task: TRIAGE each modified file and bring the working tree back to a clean state, committing in pieces if the changes are genuinely-good work or `git checkout HEAD -- <file>` reverting if they are debris.

**Modified files** (`git status --porcelain` output):

```
__PORCELAIN__
```

**Decision rules per file**:

1. Inspect the diff with `git diff <file>`. If the change is a substantive addition (new theorem with proof, new chapter with NameCert obligations, new \\leanchecked marker matching a real Lean declaration), it is genuinely-good work — bundle related files (e.g., a Lean theorem + its paper-side \\leanchecked marker) into one commit with subject `auto-heal-stuck-dirt: <brief description>` and a 1-2 sentence body explaining what was recovered.

2. If the change is a deletion or partial-revert (a `\\input{...}` line removed without the chapter file also being removed, a `\\newcommand{\\<X>Up}{...}` removed without the chapter file referencing it being removed), it is debris from a half-finished revert. Either complete the revert (delete the chapter file too if it's no longer referenced anywhere) OR restore the deleted line (`git checkout HEAD -- <file>`).

3. If the change is a marker `\\leanchecked{<X>}` whose `<X>` does not resolve to a real Lean declaration in `lean4/BEDC/`, the marker is stale — `git checkout HEAD -- <file>`.

4. For any file you cannot triage with confidence in under 5 minutes, run `git checkout HEAD -- <file>` to revert. The daemon will pick the work back up via normal pipeline rounds if it was real.

**Verification before commit**:

- `python3 lean4/scripts/bedc_ci.py audit` must pass (if you committed paper-side changes)
- `cd lean4 && python3 scripts/lake_gate.py build` must pass (if you committed Lean-side changes)
- After all decisions, `git status --porcelain` must be EMPTY (no tracked modifications). Untracked `??` files are tolerated.

Branch: codex-auto-dev. Do NOT push (the heal daemon handles push). Make one or more commits with the `auto-heal-stuck-dirt:` subject prefix; multiple commits are fine if the dirt naturally splits into multiple coherent groups.

Stop after the working tree is clean.
"""


def _read_stuck_dirt_state() -> tuple[int, frozenset[str]]:
    """Read previous stuck-dirt tick count + file set from /tmp."""
    try:
        if not STUCK_DIRT_STATE_FILE.exists():
            return 0, frozenset()
        data = json.loads(STUCK_DIRT_STATE_FILE.read_text())
        return int(data.get("count", 0)), frozenset(data.get("files", []))
    except Exception:
        return 0, frozenset()


def _write_stuck_dirt_state(count: int, files: frozenset[str]) -> None:
    """Persist stuck-dirt state so consecutive ticks can detect persistence."""
    try:
        STUCK_DIRT_STATE_FILE.write_text(json.dumps({
            "count": count,
            "files": sorted(files),
        }))
    except Exception as exc:
        print(f"[heal] could not persist stuck-dirt state: {exc}", file=sys.stderr)


def heal_stuck_dirt(blocking: list[str]) -> bool:
    """Invoke codex to triage a stuck working tree.

    `blocking` is the list of git-status-porcelain lines describing
    modified-but-uncommitted tracked files. Codex inspects each diff,
    decides commit-or-revert per file, and commits any recovered work
    under `auto-heal-stuck-dirt:` subjects. Returns True iff codex made
    progress (at least one commit OR the tree ended up clean)."""
    head_before = git("rev-parse", "HEAD", capture=True).stdout.strip()
    porcelain_str = "\n".join(blocking)
    minutes_total = STUCK_DIRT_THRESHOLD_TICKS * 15
    # `.format()` would collide with literal `{...}` braces in the
    # LaTeX-laden prompt template; substitute manually with `.replace()`.
    prompt = (
        HEAL_STUCK_DIRT_PROMPT
        .replace("__TICKS__", str(STUCK_DIRT_THRESHOLD_TICKS))
        .replace("__MINUTES_TOTAL__", str(minutes_total))
        .replace("__PORCELAIN__", porcelain_str)
    )
    rc = call_codex(prompt, timeout=1800)
    head_after = git("rev-parse", "HEAD", capture=True).stdout.strip()
    # Success criteria: commit OR clean tree.
    if head_after != head_before:
        return True
    final_porcelain = git("status", "--porcelain", capture=True).stdout.strip()
    # Filter same way we did at detection time
    blocking_after = []
    for raw in final_porcelain.splitlines():
        if not raw or raw[:2] == "??":
            continue
        path = raw[3:] if len(raw) > 3 else ""
        if path == ".pipeline_parallel.json":
            continue
        blocking_after.append(raw)
    if not blocking_after:
        return True
    print(
        f"[heal] stuck-dirt: codex made no commit (rc={rc}); "
        f"{len(blocking_after)} file(s) still dirty",
        file=sys.stderr,
    )
    return False


def run(cmd, *, cwd=REPO_ROOT, check=True, capture=False, env=None, timeout=None):
    res = subprocess.run(
        cmd, cwd=cwd, env=env,
        capture_output=capture, text=True, timeout=timeout,
    )
    if check and res.returncode != 0:
        out = (res.stdout or "") + (res.stderr or "")
        raise RuntimeError(f"command failed (rc={res.returncode}): {' '.join(cmd)}\n{out}")
    return res


def git(*args, **kwargs):
    return run(["git", *args], **kwargs)


GATE_STORM_WINDOW_MINUTES = 30
GATE_STORM_THRESHOLD = 5  # ≥5 rounds rejected by same gate in window = storm

# Stuck-dirt threshold: after N consecutive ticks (~15min each) where
# the same set of tracked files remains modified, treat the working
# tree as stuck and invoke codex to triage each file (commit-or-revert).
# 2 ticks ≈ 30 minutes; enough to ensure the dirt is not from an
# in-progress edit but a daemon that crashed mid-way.
STUCK_DIRT_THRESHOLD_TICKS = 2
STUCK_DIRT_STATE_FILE = Path("/tmp/auto_heal_stuck_dirt_state.json")
LEAN_ORCH_LOG = REPO_ROOT / "lean4" / "scripts" / "logs" / "orchestrator.log"
PAPER_ORCH_LOG = REPO_ROOT / "papers" / "bedc" / "scripts" / "logs" / "orchestrator.log"

# Gate signature patterns (regex matched against orchestrator log lines).
# (gate_name, side, regex_pattern, round_id_extractor_regex)
GATE_PATTERNS = [
    ("Examples/scaffold target paths",
     "R",
     r"Rejecting round: \d+ Lean file\(s\) use Examples/scaffold target paths",
     r"\[(R\d+)\]"),
    ("NO BEDC TOUCHPOINT",
     "R",
     r"Rejecting round: \d+ new declaration\(s\) do not mention BEDC kernel/setup",
     r"\[(R\d+)\]"),
    ("axiom-purity --strict",
     "R",
     r"Pre-merge hard gate failed: python3 lean4/scripts/bedc_ci.py axiom-purity --strict",
     r"\[(R\d+)\]"),
    ("SHALLOW GROWTH PATTERN",
     "R",
     r"SHALLOW GROWTH PATTERN:",
     r"\[(R\d+)\]"),
    ("Phase B failed: no targets extracted",
     "R",
     r"Phase B failed: no targets extracted",
     r"\[(R\d+)\]"),
    ("Pre-merge lake build",
     "R",
     r"Pre-merge hard gate failed: lake build",
     r"\[(R\d+)\]"),
    ("Paper Phase REVIEW JSON parse",
     "P",
     r"Phase REVIEW failed: could not parse JSON output",
     r"\[(P\d+)\]"),
    ("Paper OVERSIZED .TEX",
     "P",
     r"OVERSIZED \.TEX:.*exceeds cap",
     r"\[(P\d+)\]"),
]


HEAL_PROPEXT_PROMPT = """You are healing a `propext`-axiom dependency in a BEDC Lean theorem on the codex-auto-dev branch.

`bedc_ci.py axiom-purity --strict` reports that the following theorem depends on `propext`, which is forbidden by BEDC's 0-axiom rule (constructive CIC only, no LEM / Quot.sound / propext):

```
__THEOREM__ -> propext
```

This is the **propext trap** previously hit and documented in commit `fcd515ed95` (around v5.17): typeclass projection equality (e.g. `BHistCarrier.fromEventFlow X = Y`) and similar typeclass field accesses unfold via `propext` when the instance is resolved at use-site. The pattern that triggers it is referencing `<TypeClass>.<field>` from another theorem's proof body without first concretising the resolution.

Your task: rewrite the offending theorem (or its dependencies) so the proof uses concrete defs / explicit instance bodies instead of typeclass projections.

**Recipe** (from the v5.17 fix):

1. Read the offending theorem source: `git grep -n "__THEOREM__"` to locate the file. The theorem is usually under `lean4/BEDC/Derived/<X>Up/` or `lean4/BEDC/Derived/<X>Up.lean`.

2. Identify the typeclass projection in the proof body. Common offenders:
   - `BHistCarrier.fromEventFlow` / `.toEventFlow` (the `BHistCarrier` typeclass)
   - `ChapterTasteGate.round_trip` / `.layer_separation`
   - `FieldFaithful.field_faithful` / `.fields` (newly added 2026-05-13)
   - `Nontrivial.witness_pair` (newly added 2026-05-13)
   - `StructurallyAtomic.nearest_siblings`

3. Replace each typeclass projection with a CONCRETE `def` or `theorem` reference. The chapter usually already has a `private` or top-level non-typeclass version of the same fact — e.g., `cauchySealBudgetSynchronizer_round_trip` exists as a non-typeclass theorem, and `ChapterTasteGate.round_trip` typeclass field is `:= cauchySealBudgetSynchronizer_round_trip` internally. Use the concrete name in the proof body, not the typeclass projection.

4. If the chapter only has the typeclass projection and no concrete counterpart, lift a private `def`:

```lean
private def <slug>_field_faithful_concrete :
    ∀ (x y : <X>Up), FieldFaithful.fields x = FieldFaithful.fields y → x = y :=
  fun x y h => by
    -- inline proof here, not `exact FieldFaithful.field_faithful`
    ...

-- then in the offending theorem
exact <slug>_field_faithful_concrete
```

5. Verify the fix: `python3 lean4/scripts/bedc_ci.py axiom-purity --strict` reports `pure=N impure=0 forbidden=...` with the offending theorem no longer listed.

6. Also verify lake build: `cd lean4 && python3 scripts/lake_gate.py build` exits 0.

7. Commit with subject `auto-heal-propext: <slug> <field-name>` and a short body identifying which typeclass projection was concretised.

Branch: codex-auto-dev. Do NOT push (the heal daemon handles push). Stop after axiom-purity --strict passes.
"""


HEAL_CI_PROMPT = """You are healing a failed CI run on the BEDC `codex-auto-dev` branch.

A GitHub Actions workflow run has failed. The failure log tail (last ~8 KB of
the failing step) is:

```
__LOG__
```

- **Workflow**: __WORKFLOW__
- **Run ID**: __RUN_ID__
- **Failing job/step (best guess)**: __JOB__

## Your task

1. Read the log tail above and identify the SINGLE most-load-bearing error.
   Common patterns:
   - **pdflatex `Undefined control sequence \\X`** — a macro is referenced but
     not defined. Add a preamble stub in `papers/bedc/preamble.tex` (e.g.
     `\\providecommand{\\X}{...}`) or, if the macro is dead code, remove the
     reference. Do NOT invent a macro that pretends to be the real thing —
     stub it as `\\providecommand{\\X}{\\textbf{??}}` so the PDF still flags
     "??" visibly.
   - **pdflatex `Missing $`** / **`Extra }`** — find the offending line in
     the just-changed `.tex` and fix the math env (use `$$...$$` with
     `\\begin{aligned}` block per the math-env rule in CLAUDE.md).
   - **lake build `unknown identifier`** / `type mismatch` — find the
     theorem and either fix the proof, or if the upstream `def`/`theorem`
     was renamed, update callers. Do NOT introduce `sorry` or `axiom`.
   - **`bedc_ci.py audit` `unresolved Lean marker`** — paper has
     `\\leanchecked{X}` for which `X` doesn't exist in `lean4/BEDC/`. Either
     add the missing Lean theorem OR change the paper marker to
     `\\leanstmt{X}` if only the statement form is intended.
   - **`bedc_ci.py axiom-purity --strict` `propext` / `Classical.choice`** —
     see the propext recipe under HEAL_PROPEXT_PROMPT; concretise the
     typeclass projection.
   - **conservativity-audit failure** — an `\\origin{ai}` chapter leaks into
     baseline import. Move the import behind the meta-logic conservativity
     fence or relabel the chapter.
   - **`drift audit` `STALE MARKER`** — same as unresolved Lean marker.

2. Make the minimal fix. Do NOT bundle unrelated cleanups, do NOT add new
   theorems, do NOT mass-rewrite proofs.

3. Verify the fix locally before committing:
   - For Lean-side: `cd lean4 && lake build` exits 0; `python3
     tools/check-axioms.py` exits 0.
   - For paper-side: `cd papers/bedc && make check` exits 0 (single-pass
     pdflatex catches macro / math-env errors without the full ~75s build).
   - For audit: `python3 lean4/scripts/bedc_ci.py audit` exits 0.

4. Commit with subject `auto-heal-ci: fix <one-line failure>` and a 1-line
   body identifying the failing workflow + run ID.

Branch: codex-auto-dev. Do NOT push (the heal daemon handles push). Stop
after the failing gate passes locally.
"""


CI_HEAL_CACHE = Path("/tmp/auto_heal_ci_seen.json")


def _ci_seen() -> set[int]:
    try:
        return set(json.loads(CI_HEAL_CACHE.read_text()))
    except Exception:
        return set()


def _mark_ci_seen(run_id: int) -> None:
    seen = _ci_seen()
    seen.add(run_id)
    if len(seen) > 200:
        seen = set(sorted(seen)[-200:])
    try:
        CI_HEAL_CACHE.write_text(json.dumps(sorted(seen)))
    except Exception:
        pass


def detect_ci_failures(window_minutes: int = 60) -> list[dict]:
    """Query GitHub Actions for recently-failed workflow runs on BASE_BRANCH.

    Returns a list of {run_id, workflow, name, created_at} dicts ordered
    newest-first. Empty if `gh` CLI is unavailable, no runs in the window
    failed, or any query error occurred (auto_heal stays passive).
    """
    if not shutil.which("gh"):
        return []
    try:
        r = run([
            "gh", "run", "list",
            "--branch", BASE_BRANCH,
            "--limit", "20",
            "--json", "status,conclusion,name,workflowName,databaseId,createdAt",
        ], check=False, capture=True, timeout=60)
    except Exception:
        return []
    if r.returncode != 0:
        return []
    try:
        rows = json.loads(r.stdout or "[]")
    except Exception:
        return []
    cutoff = time.time() - window_minutes * 60
    failures: list[dict] = []
    for row in rows:
        if row.get("status") != "completed":
            continue
        if row.get("conclusion") != "failure":
            continue
        ts = row.get("createdAt", "")
        try:
            t = time.mktime(time.strptime(ts[:19], "%Y-%m-%dT%H:%M:%S"))
        except Exception:
            t = time.time()
        if t < cutoff:
            continue
        failures.append({
            "run_id": int(row.get("databaseId", 0)),
            "workflow": row.get("workflowName", "?"),
            "name": row.get("name", "?"),
            "created_at": ts,
        })
    return failures


def heal_ci_failure(failure: dict) -> bool:
    """Fetch the failing log tail and invoke codex with HEAL_CI_PROMPT."""
    run_id = failure["run_id"]
    if not shutil.which("gh"):
        return False
    try:
        r = run([
            "gh", "run", "view", str(run_id),
            "--log-failed",
        ], check=False, capture=True, timeout=120)
    except Exception as e:
        print(f"[heal] gh run view {run_id} failed: {e}", file=sys.stderr)
        _mark_ci_seen(run_id)
        return False
    log_tail = (r.stdout or "")[-8192:]
    if not log_tail.strip():
        # No failing-step log — try the full run view as fallback.
        try:
            r2 = run([
                "gh", "run", "view", str(run_id), "--log",
            ], check=False, capture=True, timeout=120)
            log_tail = (r2.stdout or "")[-8192:]
        except Exception:
            pass
    if not log_tail.strip():
        print(f"[heal] CI run {run_id} produced empty log; marking seen",
              file=sys.stderr)
        _mark_ci_seen(run_id)
        return False
    # Best-effort job guess: first line matching `<job>\t<step>\t...`.
    job_guess = "?"
    for line in log_tail.splitlines()[:5]:
        parts = line.split("\t")
        if len(parts) >= 2:
            job_guess = f"{parts[0]} / {parts[1]}"
            break
    prompt = (HEAL_CI_PROMPT
              .replace("__LOG__", log_tail)
              .replace("__WORKFLOW__", failure.get("workflow", "?"))
              .replace("__RUN_ID__", str(run_id))
              .replace("__JOB__", job_guess))
    _mark_ci_seen(run_id)  # prevent ping-pong even if codex fails
    head_before = git("rev-parse", "HEAD", capture=True).stdout.strip()
    rc = call_codex(prompt, timeout=1800)
    head_after = git("rev-parse", "HEAD", capture=True).stdout.strip()
    if head_before == head_after:
        print(f"[heal] codex did not commit on CI run {run_id} (rc={rc})",
              file=sys.stderr)
        return False
    return True


def detect_propext_violations_from_log() -> list[str]:
    """Parse the orchestrator log tail for `<theorem> -> propext` lines.

    The lean orchestrator logs the full `[bedc-ci] axiom-purity FAIL`
    output when an R-round hits the pre-merge axiom-purity gate. This
    parser pulls the theorem names from those log entries without
    re-running the (~60s) audit script.

    Only consulted when `detect_gate_storms()` reports an
    `axiom-purity --strict` storm — i.e., when the pipeline has
    already surfaced the failure. Passive consumption, not active
    polling."""
    try:
        size = LEAN_ORCH_LOG.stat().st_size
        with LEAN_ORCH_LOG.open("rb") as f:
            if size > 4 * 1024 * 1024:
                f.seek(size - 4 * 1024 * 1024)
            tail = f.read().decode("utf-8", errors="ignore")
    except Exception:
        return []
    violations: list[str] = []
    for line in tail.splitlines():
        s = line.strip()
        if " -> propext" not in s:
            continue
        name = s.split(" -> propext", 1)[0].strip()
        if name and name not in violations:
            violations.append(name)
    return violations


def heal_propext_violations(violations: list[str]) -> bool:
    """Invoke codex once per violation to concretise the typeclass
    projection. Returns True iff at least one violation was committed."""
    head_before = git("rev-parse", "HEAD", capture=True).stdout.strip()
    healed_any = False
    for thm in violations[:3]:  # cap 3 per cycle so a bad fix can't loop
        prompt = HEAL_PROPEXT_PROMPT.replace("__THEOREM__", thm)
        before = git("rev-parse", "HEAD", capture=True).stdout.strip()
        rc = call_codex(prompt, timeout=1800)
        after = git("rev-parse", "HEAD", capture=True).stdout.strip()
        if after != before:
            healed_any = True
            print(f"[heal] propext: codex healed {thm}", flush=True)
        else:
            print(
                f"[heal] propext: codex made no commit for {thm} (rc={rc})",
                file=sys.stderr,
            )
    return healed_any


def detect_gate_storms() -> list[dict]:
    """Scan orchestrator logs for any single gate that has rejected
    >= GATE_STORM_THRESHOLD rounds in the last GATE_STORM_WINDOW_MINUTES.
    Returns a list of dicts: {gate, side, count, rounds, samples} sorted
    by count desc.

    Reads only the tail of each log (4 MB) to keep the scan cheap; that
    covers ~6-12 hours of orchestrator log on a busy day."""
    from datetime import datetime, timedelta
    cutoff = (datetime.now() - timedelta(minutes=GATE_STORM_WINDOW_MINUTES)).strftime("%Y-%m-%d %H:%M:%S")

    def read_tail(p: Path, mb: int = 4) -> str:
        if not p.exists():
            return ""
        try:
            size = p.stat().st_size
            with p.open("rb") as f:
                if size > mb * 1024 * 1024:
                    f.seek(size - mb * 1024 * 1024)
                return f.read().decode("utf-8", errors="ignore")
        except Exception:
            return ""

    lean_tail = read_tail(LEAN_ORCH_LOG)
    paper_tail = read_tail(PAPER_ORCH_LOG)
    side_tails = {"R": lean_tail, "P": paper_tail}

    import re as _re
    storms: list[dict] = []
    for gate_name, side, pattern, rid_extractor in GATE_PATTERNS:
        tail = side_tails.get(side, "")
        if not tail:
            continue
        rid_re = _re.compile(rid_extractor)
        gate_re = _re.compile(pattern)
        rounds: list[str] = []
        samples: list[str] = []
        for line in tail.splitlines():
            if line[:19] < cutoff:
                continue
            if not gate_re.search(line):
                continue
            m = rid_re.search(line)
            if m:
                rounds.append(m.group(1))
            if len(samples) < 5:
                samples.append(line[:240])
        # Dedup rounds (one gate trigger per round)
        rounds_unique = list(dict.fromkeys(rounds))
        if len(rounds_unique) >= GATE_STORM_THRESHOLD:
            storms.append({
                "gate": gate_name,
                "side": side,
                "count": len(rounds_unique),
                "rounds": rounds_unique[:20],
                "samples": samples,
            })
    storms.sort(key=lambda s: s["count"], reverse=True)
    return storms


def heal_gate_storm(storm: dict) -> bool:
    """Invoke codex to repair a recurring gate-failure storm via prompt fix."""
    head_before = git("rev-parse", "HEAD", capture=True).stdout.strip()
    prompt = HEAL_GATE_STORM_PROMPT.format(
        gate=storm["gate"],
        minutes=GATE_STORM_WINDOW_MINUTES,
        count=storm["count"],
        rounds=", ".join(storm["rounds"]),
        samples="\n".join(f"  {s}" for s in storm["samples"]),
    )
    rc = call_codex(prompt, timeout=1800)
    head_after = git("rev-parse", "HEAD", capture=True).stdout.strip()
    if head_before == head_after:
        print(f"[heal] gate-storm '{storm['gate']}': codex made no commit (rc={rc})", file=sys.stderr)
        return False
    return True


def detect_dup_labels() -> list[tuple[str, list[str]]]:
    """Run bedc_ci.py audit. If it reports duplicate paper labels, parse
    each into (label, [file:line, file:line, ...]) and return.

    Returns empty list when audit is clean."""
    try:
        res = run(
            ["python3", "lean4/scripts/bedc_ci.py", "audit"],
            check=False, capture=True, timeout=120,
        )
    except subprocess.TimeoutExpired:
        return []
    if res.returncode == 0:
        return []
    out = (res.stdout or "") + (res.stderr or "")
    if "duplicate paper labels" not in out:
        return []
    dups: list[tuple[str, list[str]]] = []
    capturing = False
    for line in out.splitlines():
        if "duplicate paper labels" in line:
            capturing = True
            continue
        if capturing:
            if not line.strip():
                break
            # Format: `  thm:foo  @ a.tex:N, b.tex:M`
            stripped = line.strip()
            if "@" not in stripped:
                continue
            label_part, sites_part = stripped.split("@", 1)
            label = label_part.strip()
            sites = [s.strip() for s in sites_part.split(",") if s.strip()]
            dups.append((label, sites))
    return dups


def call_codex(prompt: str, cwd: Path = REPO_ROOT, timeout: int = 1800) -> int:
    """Invoke codex with the given prompt. Returns rc."""
    if not Path(CODEX_PATH).exists():
        print(f"[heal] codex CLI not found at {CODEX_PATH}", file=sys.stderr)
        return 127
    with tempfile.NamedTemporaryFile(mode="w", suffix=".txt", delete=False) as pf:
        pf.write(prompt)
        prompt_file = pf.name
    cmd = [
        "timeout", str(timeout),
        CODEX_PATH, "exec",
        "--dangerously-bypass-approvals-and-sandbox",
        "-C", str(cwd),
        "-",
    ]
    try:
        with open(prompt_file, "r") as pf:
            res = subprocess.run(cmd, stdin=pf, cwd=cwd, text=True)
    finally:
        os.unlink(prompt_file)
    return res.returncode


def heal_dup_labels(dups: list[tuple[str, list[str]]]) -> bool:
    """Invoke codex to delete duplicates. Returns True if codex made
    a commit, False otherwise."""
    head_before = git("rev-parse", "HEAD", capture=True).stdout.strip()
    dump_lines = [f"  {label} @ {', '.join(sites)}" for label, sites in dups]
    prompt = HEAL_DUP_LABELS_PROMPT.format(dups="\n".join(dump_lines))
    rc = call_codex(prompt, timeout=1800)
    head_after = git("rev-parse", "HEAD", capture=True).stdout.strip()
    if head_before == head_after:
        print(f"[heal] codex did not commit (rc={rc})", file=sys.stderr)
        return False
    return True


def push_to_origin() -> bool:
    res = run(["git", "push", "origin", BASE_BRANCH],
              check=False, capture=True, timeout=60)
    if res.returncode != 0:
        print(f"[heal] push failed: {res.stderr}", file=sys.stderr)
        return False
    return True


def cycle() -> None:
    """One healing cycle: fetch, audit, heal if needed, push."""
    ts = time.strftime("%Y-%m-%d %H:%M:%S")
    print(f"[heal] {ts} tick", flush=True)
    # Always work on codex-auto-dev (or skip if not).
    try:
        cur = git("rev-parse", "--abbrev-ref", "HEAD", capture=True).stdout.strip()
    except Exception as e:
        print(f"[heal] cannot read branch: {e}", file=sys.stderr)
        return
    if cur != BASE_BRANCH:
        print(f"[heal] not on {BASE_BRANCH} (on {cur}); skipping cycle",
              file=sys.stderr)
        return
    # Skip if working tree has TRACKED modifications, UNLESS the same
    # dirt has been stuck for ≥ STUCK_DIRT_THRESHOLD_TICKS consecutive
    # cycles. Untracked files (`?? path`) are tolerated.
    # `.pipeline_parallel.json` is also tolerated (autotune rewrites
    # every 300s; codex never touches it).
    porcelain = git("status", "--porcelain", capture=True).stdout
    blocking = []
    for raw in porcelain.splitlines():
        if not raw:
            continue
        status = raw[:2]
        path = raw[3:] if len(raw) > 3 else ""
        if status == "??":
            continue
        if path == ".pipeline_parallel.json":
            continue
        blocking.append(raw)
    if blocking:
        # Check if same dirt has been stuck across consecutive ticks.
        # If so, invoke codex to triage (commit-or-revert each file).
        dirt_set = frozenset(blocking)
        stuck_count, prev_set = _read_stuck_dirt_state()
        if dirt_set == prev_set:
            stuck_count += 1
        else:
            stuck_count = 1
        _write_stuck_dirt_state(stuck_count, dirt_set)

        if stuck_count >= STUCK_DIRT_THRESHOLD_TICKS:
            print(f"[heal] working tree dirt stuck for {stuck_count} tick(s); "
                  f"invoking codex to triage {len(blocking)} file(s)",
                  file=sys.stderr)
            for b in blocking[:5]:
                print(f"[heal]   {b}", file=sys.stderr)
            if heal_stuck_dirt(blocking):
                if push_to_origin():
                    print("[heal] codex resolved stuck dirt + pushed", flush=True)
                else:
                    print("[heal] codex resolved stuck dirt; push failed (retry next tick)",
                          flush=True)
                _write_stuck_dirt_state(0, frozenset())
                return
            else:
                print(f"[heal] codex could not resolve stuck dirt; "
                      f"will retry next tick", file=sys.stderr)
                return
        else:
            print(f"[heal] working tree has {len(blocking)} tracked modification(s); "
                  f"skipping cycle (stuck tick {stuck_count}/{STUCK_DIRT_THRESHOLD_TICKS})",
                  file=sys.stderr)
            for b in blocking[:3]:
                print(f"[heal]   {b}", file=sys.stderr)
            return
    else:
        # Tree clean; reset stuck-dirt counter.
        _write_stuck_dirt_state(0, frozenset())
    # Fetch and try ff.
    run(["git", "fetch", "origin", BASE_BRANCH], check=False, timeout=60)
    run(["git", "merge", "--ff-only", f"origin/{BASE_BRANCH}"],
         check=False, timeout=30)

    # Detect dup labels.
    dups = detect_dup_labels()
    if dups:
        print(f"[heal] {len(dups)} stuck dup label group(s) detected; invoking codex",
              flush=True)
        for label, sites in dups[:5]:
            print(f"[heal]   {label} @ {sites}", flush=True)
        if heal_dup_labels(dups):
            if push_to_origin():
                print("[heal] codex committed + pushed (dup labels)", flush=True)
            else:
                print("[heal] codex committed but push failed (will retry next tick)",
                      flush=True)
            return  # one heal per cycle is enough
    else:
        print("[heal] audit clean (0 dup labels)", flush=True)

    # Detect CI failures on origin/BASE_BRANCH within last 60min.
    ci_failures = detect_ci_failures(window_minutes=60)
    if ci_failures:
        attempted = False
        for failure in ci_failures:
            if failure["run_id"] in _ci_seen():
                continue
            attempted = True
            print(f"[heal] CI failure detected (run={failure['run_id']} "
                  f"workflow={failure.get('workflow','?')}); invoking codex",
                  flush=True)
            if heal_ci_failure(failure):
                if push_to_origin():
                    print("[heal] codex committed + pushed (CI fix)", flush=True)
                else:
                    print("[heal] codex committed but push failed (retry next tick)",
                          flush=True)
                return  # one heal per cycle is enough
            break
        if not attempted:
            print(f"[heal] all {len(ci_failures)} CI failure(s) already attempted; "
                  f"skipping (operator triage needed)", flush=True)
    else:
        print("[heal] CI clean (no failures in last 60min)", flush=True)

    # Detect propext-axiom violations from log tail. Runs independently
    # of the gate-storm threshold (5/30min) because propext violations
    # block ALL R-side rounds — even one in the log tail is a critical
    # issue that should be healed immediately. Threshold-based gate
    # detection misses cases where R-side stopped retrying (e.g., after
    # cooldown decay) before storm window expired.
    propext_v = detect_propext_violations_from_log()
    if propext_v:
        print(f"[heal] {len(propext_v)} propext violation(s) parsed from log "
              f"(threshold=1); invoking codex per-theorem", flush=True)
        for v in propext_v[:5]:
            print(f"[heal]   {v}", flush=True)
        if heal_propext_violations(propext_v):
            if push_to_origin():
                print("[heal] codex committed + pushed (propext)", flush=True)
            else:
                print("[heal] codex committed but push failed (retry next tick)",
                      flush=True)
            return  # one heal per cycle is enough
    else:
        print("[heal] no propext violation in log tail", flush=True)

    # Detect generic gate-failure storms in orchestrator logs.
    storms = detect_gate_storms()
    if not storms:
        print("[heal] no gate-failure storm in last 30min", flush=True)
        return
    print(f"[heal] {len(storms)} gate-failure storm(s) detected:", flush=True)
    for s in storms:
        print(f"[heal]   {s['side']}-side '{s['gate']}': {s['count']} rounds in 30min",
              flush=True)
    # Heal the worst one this cycle (next cycle picks up the next if codex's
    # fix actually drained the top storm).
    top = storms[0]
    print(f"[heal] healing top storm: {top['gate']} ({top['count']} rounds)",
          flush=True)
    # Route by storm gate name: content-level failures (propext) get
    # the focused per-theorem heal; everything else falls through to the
    # generic prompt-fix heal.
    healed = False
    if "axiom-purity --strict" in top["gate"]:
        propext_v = detect_propext_violations_from_log()
        if propext_v:
            print(f"[heal] axiom-purity storm: {len(propext_v)} propext violation(s) "
                  f"parsed from log; invoking codex per-theorem", flush=True)
            for v in propext_v[:5]:
                print(f"[heal]   {v}", flush=True)
            healed = heal_propext_violations(propext_v)
        else:
            # Storm reported axiom-purity gate but log didn't contain
            # `-> propext` lines — fall through to generic heal.
            healed = heal_gate_storm(top)
    else:
        healed = heal_gate_storm(top)

    if healed:
        if push_to_origin():
            print(f"[heal] codex committed + pushed (gate storm: {top['gate']})",
                  flush=True)
        else:
            print(f"[heal] codex committed but push failed (will retry next tick)",
                  flush=True)


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--interval", type=int, default=DEFAULT_INTERVAL,
                    help="Cycle interval seconds (default 900)")
    p.add_argument("--once", action="store_true",
                    help="Run a single cycle and exit (for testing)")
    args = p.parse_args()

    if args.once:
        cycle()
        return 0

    interval = int(os.environ.get("AUTO_HEAL_INTERVAL_SECONDS", args.interval))
    print(f"[heal] starting (interval={interval}s)", flush=True)
    while True:
        try:
            cycle()
        except Exception as e:
            print(f"[heal] cycle exception: {e}", file=sys.stderr)
        time.sleep(interval)


if __name__ == "__main__":
    raise SystemExit(main())
