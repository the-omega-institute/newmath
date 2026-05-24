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
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time
from datetime import datetime, timedelta
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
BASE_BRANCH = "codex-auto-dev"
CODEX_PATH = shutil.which("codex") or "/opt/homebrew/bin/codex"
DEFAULT_INTERVAL = 900  # 15 min

_HEAL_VERIFY_FOOTER = """

Before committing or claiming done: run every verification command named
in the task above; for any Lean-side or mixed fix ALSO run
`python3 lean4/scripts/bedc_ci.py axiom-purity --strict` and
`(cd lean4 && lake build)`. If any verification fails, keep fixing in
THIS codex session — do NOT commit, do NOT signal success.
"""

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
6. `git add` each touched file, `git commit -m "auto-heal: 重复标签 <main-label>"` (no push — the daemon does that). The commit subject MUST contain the dedup signature supplied by the daemon.

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
7. `git add` + `git commit -m "auto-heal: gate-storm <gate-name> 提示约束"`; the commit subject MUST contain the dedup signature supplied by the daemon. Do NOT push (the daemon handles push).

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

5. `git add` the modified file(s), `git commit -m "auto-heal: 删除重复结论 {file}"`.
6. Do NOT push — the daemon does that.

If the duplication is intentional (e.g. both theorems serve documented different audiences and removing either would break downstream), leave alone and explain in your final message.
"""

COOLDOWN_NO_TOUCHPOINT_PROMPT = """You are healing a BEDC Phase D lint narrow-anchor rejection on the codex-auto-dev branch.

Phase D lint rejected declaration `{decl}` in `{file}` with "NO BEDC TOUCHPOINT".

Rejected context:
```
{snippet}
```

The declaration name suggests it is BEDC-anchored, but the lint's anchor
regex did not recognize one of its symbols as a BEDC anchor.

## Task

1. Open `lean4/scripts/phase_d_lint.py`.
2. Inspect `BHIST_CONSTRUCTOR_RE`.
3. Add only the missing BEDC-defined anchor symbol(s) referenced by `{decl}`.
   Do not broaden the regex with a generic catch-all.
4. Verify: `python3 lean4/scripts/phase_d_lint.py --help` exits 0 and
   `python3 -m py_compile lean4/scripts/phase_d_lint.py` exits 0.
5. Commit with message `auto-heal: cooldown NO_BEDC_TOUCHPOINT_NARROW {symbol}`. The commit subject MUST contain the dedup signature supplied by the daemon.

Do NOT push. The heal daemon handles push.
"""

COOLDOWN_SHALLOW_PROMPT = """You are healing a repeated BEDC SHALLOW GROWTH lint failure on the codex-auto-dev branch.

Recent cooldown analysis found repeated SHALLOW GROWTH failures for chapter or file `{chapter}`.

Representative failures:
```
{snippet}
```

## Task

1. Inspect the file/chapter named above and the exact theorem names in the
   SHALLOW GROWTH message.
2. Remove the redundant duplicate-conclusion theorem, or rename/refactor it
   only if the conclusion is genuinely distinct after inspecting the statement.
3. Update any local references to use the surviving theorem or a projection
   from it.
4. Verify: `cd lean4 && lake build` exits 0.
5. Commit with message `auto-heal: cooldown SHALLOW_GROWTH_REPEATED {slug}`. The commit subject MUST contain the dedup signature supplied by the daemon.

Do NOT push. The heal daemon handles push.
"""

COOLDOWN_LAKE_DUP_PROMPT = """You are healing a stuck BEDC lake-build duplicate declaration failure on the codex-auto-dev branch.

The pre-merge hard gate failed at lake build with a duplicate declaration error.

Build error summary:
```
{snippet}
```

Likely duplicate symbol: `{symbol}`

## Task

1. Locate the duplicate declaration(s) with `git grep -n "{symbol}" -- lean4/BEDC/`
   if a symbol is available; otherwise inspect the build error paths above.
2. Keep the canonical declaration and remove or rename the duplicate. Prefer
   deleting the newer redundant helper if it is not referenced.
3. Update references only as needed.
4. Verify: `cd lean4 && lake build` exits 0.
5. Commit with message `auto-heal: cooldown LAKE_BUILD_STUCK_DUP {symbol}`. The commit subject MUST contain the dedup signature supplied by the daemon.

Do NOT push. The heal daemon handles push.
"""


HEAL_STUCK_DIRT_PROMPT = """You are healing a stuck working tree on the BEDC `codex-auto-dev` branch.

The main checkout has had the same set of tracked modifications for __TICKS__ consecutive heal cycles (__MINUTES_TOTAL__ minutes total). This is NOT a human edit-in-progress — the dirt has not changed across two ticks. A daemon (paper_builder_daemon, sync_with_auto_dev, or a stray codex round that wrote to the main checkout instead of its worktree) left work uncommitted, and the dirt now blocks every other heal pathway (axiom-purity storm repair, dup-label repair, etc.).

Your task: TRIAGE each modified file and bring the working tree back to a clean state, committing in pieces if the changes are genuinely-good work or `git checkout HEAD -- <file>` reverting if they are debris.

**Modified files** (`git status --porcelain` output):

```
__PORCELAIN__
```

**Decision rules per file**:

1. Inspect the diff with `git diff <file>`. If the change is a substantive addition (new theorem with proof, new chapter with NameCert obligations, new \\leanchecked marker matching a real Lean declaration), it is genuinely-good work — bundle related files (e.g., a Lean theorem + its paper-side \\leanchecked marker) into one commit with subject `auto-heal: 回收滞留工作 <brief description>` and a 1-2 sentence body explaining what was recovered.

2. If the change is a deletion or partial-revert (a `\\input{...}` line removed without the chapter file also being removed, a `\\newcommand{\\<X>Up}{...}` removed without the chapter file referencing it being removed), it is debris from a half-finished revert. Either complete the revert (delete the chapter file too if it's no longer referenced anywhere) OR restore the deleted line (`git checkout HEAD -- <file>`).

3. If the change is a marker `\\leanchecked{<X>}` whose `<X>` does not resolve to a real Lean declaration in `lean4/BEDC/`, the marker is stale — `git checkout HEAD -- <file>`.

4. For any file you cannot triage with confidence in under 5 minutes, run `git checkout HEAD -- <file>` to revert. The daemon will pick the work back up via normal pipeline rounds if it was real.

**Verification before commit**:

- `python3 lean4/scripts/bedc_ci.py audit` must pass (if you committed paper-side changes)
- `cd lean4 && python3 scripts/lake_gate.py build` must pass (if you committed Lean-side changes)
- After all decisions, `git status --porcelain` must be EMPTY (no tracked modifications). Untracked `??` files are tolerated.

Branch: codex-auto-dev. Do NOT push (the heal daemon handles push). Make one or more commits with the `auto-heal: 回收滞留工作` subject prefix; multiple commits are fine if the dirt naturally splits into multiple coherent groups.

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
    under `auto-heal: 回收滞留工作` subjects. Returns True iff codex made
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
    signature = "stuck dirt " + _short_hash(porcelain_str)
    if _recurring_fix_loop(signature, "stuck dirt", {"blocking": blocking[:10]}):
        return False
    prompt = _with_fix_signature(prompt, signature)
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


def _tail_text(text: str, limit: int = 500) -> str:
    if isinstance(text, bytes):
        text = text.decode("utf-8", errors="ignore")
    text = text.strip()
    return text[-limit:] if len(text) > limit else text


def verify_local_ci() -> tuple[bool, str | None]:
    """Run quick local CI suite before pushing a heal commit.

    Returns (False, error_tail) on the first failed step and (True, None)
    when all checks pass.
    """
    checks = [
        ("papers/bedc make check", ["make", "check"], REPO_ROOT / "papers" / "bedc", 600),
        ("lean4 lake build", ["lake", "build"], REPO_ROOT / "lean4", 600),
        (
            "bedc_ci audit",
            ["python3", "lean4/scripts/bedc_ci.py", "audit"],
            REPO_ROOT,
            180,
        ),
        (
            "bedc_ci axiom-purity --strict",
            ["python3", "lean4/scripts/bedc_ci.py", "axiom-purity", "--strict"],
            REPO_ROOT,
            240,
        ),
    ]
    for name, cmd, cwd, timeout in checks:
        print(f"[heal] verify_local_ci: running {name}", flush=True)
        try:
            res = run(cmd, cwd=cwd, check=False, capture=True, timeout=timeout)
        except subprocess.TimeoutExpired as exc:
            stdout = exc.stdout or ""
            stderr = exc.stderr or ""
            if isinstance(stdout, bytes):
                stdout = stdout.decode("utf-8", errors="ignore")
            if isinstance(stderr, bytes):
                stderr = stderr.decode("utf-8", errors="ignore")
            out = stdout + stderr
            return False, f"{name} timed out after {timeout}s\n{_tail_text(out)}"
        except Exception as exc:
            return False, f"{name} failed to run: {exc}"
        if res.returncode != 0:
            out = (res.stdout or "") + (res.stderr or "")
            return False, f"{name} failed rc={res.returncode}\n{_tail_text(out)}"
    return True, None


def recent_fix_signature_seen(
    signature: str,
    hours: int = 6,
    threshold: int = 2,
) -> bool:
    """Return True when recent commit subjects contain signature often enough."""
    if not signature:
        return False
    try:
        res = git(
            "log",
            f"--since={hours} hours ago",
            "--format=%s",
            "HEAD",
            f"origin/{BASE_BRANCH}",
            check=False,
            capture=True,
            timeout=30,
        )
    except Exception as exc:
        print(f"[heal] recent_fix_signature_seen failed: {exc}", file=sys.stderr)
        return False
    if res.returncode != 0:
        print(f"[heal] git log for recent fix signatures failed: {res.stderr}",
              file=sys.stderr)
        return False
    hits = sum(1 for line in (res.stdout or "").splitlines() if signature in line)
    if hits >= threshold:
        print(
            f"[heal] recent_fix_signature_seen: signature={signature!r} "
            f"hits={hits}/{threshold}",
            file=sys.stderr,
        )
        return True
    return False


def _recurring_fix_loop(signature: str, phase: str, details: dict) -> bool:
    if not recent_fix_signature_seen(signature, hours=6, threshold=2):
        return False
    payload = dict(details)
    payload["signature"] = signature
    payload["phase"] = phase
    log_heal_alert(
        category="RECURRING_FIX_LOOP",
        details=payload,
        cooldown_count=0,
        note="近 6 小时内同一修复签名已多次出现，停止派发 codex 并转交人工分诊",
    )
    return True


def _with_fix_signature(prompt: str, signature: str) -> str:
    return (
        prompt
        + "\n\n## Heal dedup signature\n\n"
        + f"Your commit subject MUST contain this exact substring: `{signature}`.\n"
        + "If you cannot make a correct fix, do not commit.\n"
        + _HEAL_VERIFY_FOOTER
    )


def _ci_fix_signature(log_tail: str, failure: dict) -> str:
    patterns = [
        (r"Undefined control sequence\.\s*(?:.*\n){0,3}.*?(\\[A-Za-z@]+)", "missing macro"),
        (r"Command\s+(\\[A-Za-z@]+)\s+already defined", "duplicate macro"),
        (r"LaTeX Error:\s*Command\s+(\\[A-Za-z@]+)\s+already defined", "duplicate macro"),
        (r"error:\s*unknown identifier\s+['`]?([A-Za-z_][A-Za-z0-9_'.]*)", "unknown identifier"),
        (r"unresolved Lean marker\s+([A-Za-z_][A-Za-z0-9_'.]*)", "unresolved marker"),
        (r"STALE MARKER\s+([A-Za-z_][A-Za-z0-9_'.]*)", "stale marker"),
        (r"([A-Za-z_][A-Za-z0-9_'.]*)\s+->\s+(propext|Classical\.choice|Quot\.sound)", "axiom leak"),
    ]
    for pattern, prefix in patterns:
        m = re.search(pattern, log_tail, re.IGNORECASE)
        if not m:
            continue
        if prefix == "axiom leak" and len(m.groups()) >= 2:
            return f"CI heal {prefix} {m.group(1)} {m.group(2)}"
        return f"CI heal {prefix} {m.group(1)}"
    fallback = _short_hash(log_tail[-2000:])
    return f"CI heal {failure.get('workflow', '?')} {fallback}"


def verify_then_push(phase: str) -> bool:
    ok, err = verify_local_ci()
    if ok:
        if push_to_origin():
            print(f"[heal] codex committed + pushed ({phase})", flush=True)
            return True
        print(f"[heal] codex committed but push failed ({phase}; retry next tick)",
              flush=True)
        return False
    err = err or "unknown local CI failure"
    print(
        f"[heal] codex committed but local CI failed; NOT pushing. "
        f"Error tail: {err[:200]}",
        file=sys.stderr,
        flush=True,
    )
    log_heal_alert(
        category="LOCAL_CI_FAILED_AFTER_HEAL",
        details={"phase": phase, "error_tail": err[:500]},
        cooldown_count=0,
        note="codex 的 heal 提交破坏了本地 CI，已阻止 push 并尝试回退",
    )
    try:
        git("reset", "--hard", "HEAD^", check=False, capture=True)
        print("[heal] reverted heal commit (verify failed)", flush=True)
    except Exception as exc:
        print(f"[heal] revert failed: {exc}", file=sys.stderr, flush=True)
    return False


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
COOLDOWN_ALERT_LOG = Path("/tmp/.bedc_heal_alerts.log")
COOLDOWN_STATE_FILE = Path("/tmp/.bedc_heal_cooldown_state.json")
COOLDOWN_WINDOW_MINUTES = 60
COOLDOWN_THRESHOLD = 3
COOLDOWN_CONTEXT_MINUTES = 5
COOLDOWN_FIX_DEDUP_MINUTES = 60
COOLDOWN_STATE_KEEP_HOURS = 24
HOT_FIXABLE_CATEGORIES = {
    "NO_BEDC_TOUCHPOINT_NARROW",
    "SHALLOW_GROWTH_REPEATED",
    "LAKE_BUILD_STUCK_DUP",
}
KNOWN_BEDC_CONCEPTS = (
    "Faithful",
    "Carrier",
    "TasteGate",
    "NameCert",
    "BHist",
    "BMark",
    "ProbeBundle",
    "SigRel",
    "AskSetup",
    "PackageSetup",
    "DomainSetup",
    "SemanticNameCert",
    "Reflection",
    "Digest",
    "Seal",
    "Bundle",
)

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

_PROPEXT_VERIFY_OUTPUT: str | None = None


def _reset_act_verify_cache() -> None:
    global _PROPEXT_VERIFY_OUTPUT
    _PROPEXT_VERIFY_OUTPUT = None


def _act_verify_skip(signature: str) -> None:
    print(
        f"[heal] act-verify: {signature} no longer present in current state; "
        "skipping dispatch",
        file=sys.stderr,
    )


def _combined_output(res: subprocess.CompletedProcess[str]) -> str:
    return (res.stdout or "") + (res.stderr or "")


def _run_phase_d_lint_current() -> subprocess.CompletedProcess[str]:
    return run(
        [
            "python3",
            "lean4/scripts/phase_d_lint.py",
            "--worktree",
            str(REPO_ROOT),
            "--base-branch",
            BASE_BRANCH,
            "--include-shallow",
        ],
        check=False,
        capture=True,
        timeout=180,
    )


def verify_propext_still_impure(theorem_fqn: str) -> bool:
    """Return True iff axiom-purity still lists theorem_fqn as impure."""
    global _PROPEXT_VERIFY_OUTPUT
    if _PROPEXT_VERIFY_OUTPUT is None:
        try:
            res = run(
                [
                    "python3",
                    "lean4/scripts/bedc_ci.py",
                    "axiom-purity",
                    "--strict",
                    "--verbose",
                ],
                check=False,
                capture=True,
                timeout=600,
            )
            _PROPEXT_VERIFY_OUTPUT = _combined_output(res)
        except subprocess.TimeoutExpired as exc:
            stdout = exc.stdout or ""
            stderr = exc.stderr or ""
            if isinstance(stdout, bytes):
                stdout = stdout.decode("utf-8", errors="ignore")
            if isinstance(stderr, bytes):
                stderr = stderr.decode("utf-8", errors="ignore")
            _PROPEXT_VERIFY_OUTPUT = stdout + stderr
        except Exception as exc:
            print(f"[heal] act-verify propext failed: {exc}", file=sys.stderr)
            _PROPEXT_VERIFY_OUTPUT = ""
    needle = theorem_fqn.strip()
    if not needle:
        return False
    for line in _PROPEXT_VERIFY_OUTPUT.splitlines():
        if needle not in line:
            continue
        if any(tok in line for tok in ("propext", "Classical.choice", "Quot.sound", "forbidden")):
            return True
    return False


def _phase_d_lint_output_matches(gate_name: str, target_file: object, out: str) -> bool:
    gate = gate_name.upper()
    target = target_file if isinstance(target_file, dict) else {}
    if "NO_BEDC_TOUCHPOINT" in gate or "NO BEDC TOUCHPOINT" in gate:
        decl = str(target.get("decl", "")).strip()
        return (
            "Derived theorem missing" in out
            or "NO BEDC TOUCHPOINT" in out
            or bool(decl and decl in out)
        )
    if "SHALLOW_GROWTH" in gate or "SHALLOW GROWTH" in gate:
        chapter = str(target.get("chapter", "")).strip()
        return "SHALLOW GROWTH PATTERN" in out and (not chapter or chapter in out)
    return False


def verify_push_lock_starvation_recent() -> bool:
    """Return True iff a push-lock timeout appears in the last five minutes."""
    cutoff = datetime.now() - timedelta(minutes=5)
    pat = re.compile(r"push lock for branch.*held for more than 600s")
    for path in (LEAN_ORCH_LOG, PAPER_ORCH_LOG):
        for ts, line in _read_log_tail(path):
            if ts >= cutoff and pat.search(line):
                return True
    return False


def verify_phase_d_lint_still_rejects(cooldown_target: dict) -> bool:
    category = cooldown_target.get("category", "")
    details = cooldown_target.get("details", {})
    if category == "LAKE_BUILD_STUCK_DUP":
        try:
            res = run(["lake", "build"], cwd=REPO_ROOT / "lean4",
                      check=False, capture=True, timeout=600)
        except Exception:
            return False
        out = _combined_output(res)
        if res.returncode == 0:
            return False
        symbol = str(details.get("symbol", "")).strip()
        dup = re.search(
            r"already declared|duplicate declaration|has multiple definitions",
            out,
            re.IGNORECASE,
        )
        return bool(dup and (not symbol or symbol in out))
    try:
        res = _run_phase_d_lint_current()
    except Exception:
        return False
    if res.returncode == 0:
        return False
    return _phase_d_lint_output_matches(category, details, _combined_output(res))


def verify_gate_still_failing(gate_name: str, target_file: object) -> bool:
    gate = gate_name or ""
    if "axiom-purity" in gate:
        if isinstance(target_file, str) and target_file:
            return verify_propext_still_impure(target_file)
        return any(verify_propext_still_impure(v) for v in detect_propext_violations_from_log()[:5])
    if any(tok in gate for tok in ("NO BEDC TOUCHPOINT", "SHALLOW GROWTH PATTERN")):
        try:
            res = _run_phase_d_lint_current()
        except Exception:
            return False
        if res.returncode == 0:
            return False
        return _phase_d_lint_output_matches(gate, target_file, _combined_output(res))
    if "lake build" in gate:
        try:
            res = run(["lake", "build"], cwd=REPO_ROOT / "lean4",
                      check=False, capture=True, timeout=600)
        except Exception:
            return False
        return res.returncode != 0
    if "audit" in gate or "bedc_ci.py audit" in gate:
        try:
            res = run(["python3", "lean4/scripts/bedc_ci.py", "audit"],
                      check=False, capture=True, timeout=180)
        except Exception:
            return False
        return res.returncode != 0
    if "OVERSIZED .TEX" in gate:
        for tex in (REPO_ROOT / "papers" / "bedc" / "parts").rglob("*.tex"):
            try:
                if sum(1 for _ in tex.open("r", encoding="utf-8", errors="ignore")) > 800:
                    return True
            except Exception:
                continue
    return False


HEAL_PROPEXT_PROMPT = """You are healing a `propext`-axiom dependency in a BEDC Lean theorem on the codex-auto-dev branch.

`bedc_ci.py axiom-purity --strict` reports that the following theorem depends on `propext`, which is forbidden by BEDC's 0-axiom rule (constructive CIC only, no LEM / Quot.sound / propext):

```
__THEOREM__ -> propext
```

This is the **propext trap**: typeclass projection equality (e.g. `BHistCarrier.fromEventFlow X = Y`) and similar typeclass field accesses unfold via `propext` when the instance is resolved at use-site. The pattern that triggers it is referencing `<TypeClass>.<field>` from another theorem's proof body without first concretising the resolution.

Your task: rewrite the offending theorem (or its dependencies) so the proof uses concrete defs / explicit instance bodies instead of typeclass projections.

**Recipe**:

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
Run `python3 lean4/scripts/bedc_ci.py axiom-purity --strict` and confirm the target theorem is absent from the impure list; if the theorem still appears, your fix did not work — keep iterating in this session.

6. Also verify lake build: `cd lean4 && python3 scripts/lake_gate.py build` exits 0.

7. Commit with subject `auto-heal: propext heal <theorem>` and a short body identifying which typeclass projection was concretised. The commit subject MUST contain the dedup signature supplied by the daemon.

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
   Run `python3 lean4/scripts/bedc_ci.py axiom-purity --strict` AND `python3 lean4/scripts/bedc_ci.py audit`; both must exit 0 before commit.

4. Commit with subject `auto-heal: CI 修复 <one-line failure>` and a 1-line
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
    """Query GitHub Actions for recently-failed workflow runs on BASE_BRANCH
    AND the sibling `auto-dev` branch (which receives every codex-auto-dev
    sync from sync_with_auto_dev.py — CI primarily runs there because
    `auto-dev` is the durable upstream branch with cache + permissions).

    Returns a list of {run_id, workflow, name, created_at, branch} dicts
    ordered newest-first. Empty if `gh` CLI is unavailable, no runs in
    the window failed, or any query error occurred (auto_heal stays
    passive).
    """
    if not shutil.which("gh"):
        return []
    # Probe both branches: codex-auto-dev (integration) + auto-dev (CI host).
    # bidirectional sync means a fix on codex-auto-dev reaches auto-dev
    # within 10 min, so healing either side is equivalent.
    branches_to_probe = [BASE_BRANCH, "auto-dev"]
    failures: list[dict] = []
    cutoff = time.time() - window_minutes * 60
    for branch in branches_to_probe:
        try:
            r = run([
                "gh", "run", "list",
                "--branch", branch,
                "--limit", "20",
                "--json", "status,conclusion,name,workflowName,databaseId,createdAt",
            ], check=False, capture=True, timeout=60)
        except Exception:
            continue
        if r.returncode != 0:
            continue
        try:
            rows = json.loads(r.stdout or "[]")
        except Exception:
            continue
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
                "branch": branch,
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
    signature = _ci_fix_signature(log_tail, failure)
    if _recurring_fix_loop(signature, "CI fix", failure):
        _mark_ci_seen(run_id)
        return False
    prompt = _with_fix_signature(prompt, signature)
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
        signature = f"propext heal {thm}"
        if not verify_propext_still_impure(thm):
            _act_verify_skip(f"propext {thm}")
            continue
        if _recurring_fix_loop(signature, "propext", {"theorem": thm}):
            continue
        prompt = _with_fix_signature(
            HEAL_PROPEXT_PROMPT.replace("__THEOREM__", thm),
            signature,
        )
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
    signature = f"gate-storm {storm['gate']}"
    if not verify_gate_still_failing(storm["gate"], storm):
        _act_verify_skip(signature)
        return False
    if _recurring_fix_loop(signature, "gate storm", storm):
        return False
    prompt = _with_fix_signature(prompt, signature)
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
    signature = f"dup label {dups[0][0]}"
    if _recurring_fix_loop(
        signature,
        "dup labels",
        {"labels": [label for label, _ in dups[:10]]},
    ):
        return False
    prompt = _with_fix_signature(
        HEAL_DUP_LABELS_PROMPT.format(dups="\n".join(dump_lines)),
        signature,
    )
    rc = call_codex(prompt, timeout=1800)
    head_after = git("rev-parse", "HEAD", capture=True).stdout.strip()
    if head_before == head_after:
        print(f"[heal] codex did not commit (rc={rc})", file=sys.stderr)
        return False
    return True


def _parse_log_timestamp(line: str) -> datetime | None:
    """Best-effort parser for orchestrator log timestamps."""
    raw = line[:23]
    for fmt, n in (("%Y-%m-%d %H:%M:%S,%f", 23),
                   ("%Y-%m-%d %H:%M:%S.%f", 23),
                   ("%Y-%m-%d %H:%M:%S", 19)):
        try:
            return datetime.strptime(raw[:n], fmt)
        except ValueError:
            continue
    return None


def _read_log_tail(path: Path, mb: int = 8) -> list[tuple[datetime, str]]:
    if not path.exists():
        return []
    try:
        size = path.stat().st_size
        with path.open("rb") as f:
            if size > mb * 1024 * 1024:
                f.seek(size - mb * 1024 * 1024)
            text = f.read().decode("utf-8", errors="ignore")
    except Exception:
        return []
    out: list[tuple[datetime, str]] = []
    last_ts: datetime | None = None
    for line in text.splitlines():
        ts = _parse_log_timestamp(line)
        if ts is not None:
            last_ts = ts
        if last_ts is not None:
            out.append((last_ts, line))
    return out


def _extract_round_id(line: str) -> str:
    m = re.search(r"\[(R\d+|P\d+)\]|\b(R\d+|P\d+)\b", line)
    if not m:
        return "?"
    return next(g for g in m.groups() if g)


def _extract_error_before_failed(
    context: list[tuple[datetime, str]],
    failed_index: int,
) -> str:
    start = max(0, failed_index - 30)
    window = context[start:failed_index]
    semantic_re = re.compile(
        r"NO BEDC TOUCHPOINT|SHALLOW GROWTH PATTERN|"
        r"Pre-merge hard gate failed: lake build|already declared|"
        r"duplicate declaration|function: .* has multiple definitions|"
        r"push lock for branch.*held for more than \d+s|"
        r"Codex exec completed in \d+(?:\.\d+)?s \(rc=1\)|"
        r"Selected model is at capacity",
        re.IGNORECASE,
    )
    for _, line in reversed(window):
        if semantic_re.search(line):
            return line.strip()[:500]
    for _, line in reversed(window):
        if "[ERROR]" in line or "ERROR:" in line or "Rejecting" in line:
            return line.strip()[:500]
    return context[failed_index][1].strip()[:500]


def _preceding_failures(context: list[tuple[datetime, str]]) -> list[dict]:
    failures: list[dict] = []
    for idx, (_, line) in enumerate(context):
        if "Round FAILED" not in line:
            continue
        rid = _extract_round_id(line)
        snippet = _extract_error_before_failed(context, idx)
        failures.append({"round_id": rid, "snippet": snippet})
    return failures[-3:]


def _detect_cooldowns_in_rows(
    rows: list[tuple[datetime, str]],
    *,
    side: str,
    log_path: str,
    window_minutes: int,
) -> list[dict]:
    cooldown_re = re.compile(
        r"\[WARNING\]\s+\[MainThread\]\s+\[cooldown\]\s+3 "
        r"(?:consecutive )?failures"
    )
    cutoff = datetime.now() - timedelta(minutes=window_minutes)
    cooldowns: list[dict] = []
    for ts, line in rows:
        if ts < cutoff or not cooldown_re.search(line):
            continue
        context_start = ts - timedelta(minutes=COOLDOWN_CONTEXT_MINUTES)
        context = [(t, s) for t, s in rows if context_start <= t <= ts]
        failures = _preceding_failures(context)
        cooldowns.append({
            "side": side,
            "log_path": log_path,
            "timestamp": ts.isoformat(sep=" "),
            "line": line.strip(),
            "failures": failures,
            "context": [s for _, s in context[-120:]],
        })
    return cooldowns


def detect_recent_cooldowns(window_minutes: int = COOLDOWN_WINDOW_MINUTES) -> list[dict]:
    """Find recent cooldown events and attach preceding same-log context."""
    cooldowns: list[dict] = []
    for side, path in (("R", LEAN_ORCH_LOG), ("P", PAPER_ORCH_LOG)):
        rows = _read_log_tail(path)
        if not rows:
            continue
        cooldowns.extend(_detect_cooldowns_in_rows(
            rows,
            side=side,
            log_path=str(path),
            window_minutes=window_minutes,
        ))
    cooldowns.sort(key=lambda c: c["timestamp"])
    return cooldowns


def detect_recent_cooldowns_from_text(
    text: str,
    *,
    window_minutes: int = COOLDOWN_WINDOW_MINUTES,
    side: str = "R",
) -> list[dict]:
    """Parse cooldowns from stdin text for dry-run validation."""
    rows: list[tuple[datetime, str]] = []
    last_ts: datetime | None = None
    for line in text.splitlines():
        ts = _parse_log_timestamp(line)
        if ts is not None:
            last_ts = ts
        if last_ts is not None:
            rows.append((last_ts, line))
    cooldowns = _detect_cooldowns_in_rows(
        rows,
        side=side,
        log_path="<stdin>",
        window_minutes=window_minutes,
    )
    cooldowns.sort(key=lambda c: c["timestamp"])
    return cooldowns


def _all_cooldown_text(cooldown: dict) -> str:
    parts = [cooldown.get("line", "")]
    parts.extend(f.get("snippet", "") for f in cooldown.get("failures", []))
    parts.extend(cooldown.get("context", []))
    return "\n".join(parts)


def _extract_decl_name(text: str) -> str:
    patterns = [
        r"NO BEDC TOUCHPOINT:\s*([A-Za-z_][A-Za-z0-9_'.]*)",
        r"\b(?:declaration|decl|theorem|lemma|def|class|structure)\s+`?([A-Za-z_][A-Za-z0-9_'.]*)`?",
        r"`([A-Za-z_][A-Za-z0-9_'.]*(?:Up|Faithful|Carrier|TasteGate|NameCert)[A-Za-z0-9_'.]*)`",
    ]
    for pat in patterns:
        m = re.search(pat, text)
        if m:
            return m.group(1).rstrip(".,;:")
    return ""


def _extract_file_path(text: str) -> str:
    m = re.search(r"(lean4/BEDC/[A-Za-z0-9_./'-]+\.lean)", text)
    if m:
        return m.group(1)
    m = re.search(r"([A-Za-z0-9_./'-]+\.lean)", text)
    return m.group(1) if m else ""


def _extract_shallow_chapter(snippet: str) -> str:
    m = re.search(r"SHALLOW GROWTH PATTERN:\s*([^:\n]+?\.lean)", snippet)
    if m:
        return m.group(1).strip()
    m = re.search(r"(lean4/BEDC/[A-Za-z0-9_./'-]+\.lean)", snippet)
    if m:
        return m.group(1)
    m = re.search(r"BEDC\.Derived\.([A-Za-z0-9_'.]+)", snippet)
    return m.group(1) if m else "unknown"


def _extract_duplicate_symbol(text: str) -> str:
    patterns = [
        r"already declared(?: as)?\s+['`]?([A-Za-z_][A-Za-z0-9_'.]*)",
        r"duplicate declaration\s+['`]?([A-Za-z_][A-Za-z0-9_'.]*)",
        r"function:\s*([A-Za-z_][A-Za-z0-9_'.]*)\s+has multiple definitions",
        r"declaration '[^']*\.([A-Za-z_][A-Za-z0-9_'.]*)' has already been declared",
    ]
    for pat in patterns:
        m = re.search(pat, text, re.IGNORECASE)
        if m:
            return m.group(1).rstrip(".,;:")
    return ""


def _short_hash(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8", errors="ignore")).hexdigest()[:16]


def _details_hash(category: str, details: dict) -> str:
    if category == "NO_BEDC_TOUCHPOINT_NARROW":
        key = f"{details.get('decl','')}|{details.get('file','')}"
    elif category == "SHALLOW_GROWTH_REPEATED":
        key = str(details.get("chapter", ""))
    elif category == "LAKE_BUILD_STUCK_DUP":
        key = f"{details.get('symbol','')}|{details.get('file','')}"
    else:
        key = json.dumps(details, sort_keys=True, ensure_ascii=False)[:4000]
    return _short_hash(f"{category}|{key}")


def classify_cooldown_cause(cooldown: dict) -> tuple[str, dict]:
    """Classify a cooldown event by its preceding failures."""
    failures = cooldown.get("failures", [])
    snippets = [f.get("snippet", "") for f in failures]
    text = _all_cooldown_text(cooldown)

    # 1. NO_BEDC_TOUCHPOINT_NARROW
    no_touch = [s for s in snippets if "NO BEDC TOUCHPOINT" in s]
    if no_touch:
        snippet = no_touch[-1]
        decl = _extract_decl_name(snippet) or _extract_decl_name(text)
        file_path = _extract_file_path(snippet) or _extract_file_path(text)
        bedc_named = decl.endswith("Up") or any(c in decl for c in KNOWN_BEDC_CONCEPTS)
        if bedc_named:
            return "NO_BEDC_TOUCHPOINT_NARROW", {
                "decl": decl,
                "file": file_path,
                "symbol": next((c for c in KNOWN_BEDC_CONCEPTS if c in decl), decl),
                "snippet": snippet,
                "preceding_fails": failures,
            }

    # 2. SHALLOW_GROWTH_REPEATED
    shallow_chapters: dict[str, list[str]] = {}
    for snippet in snippets:
        if "SHALLOW GROWTH PATTERN" not in snippet:
            continue
        chapter = _extract_shallow_chapter(snippet)
        shallow_chapters.setdefault(chapter, []).append(snippet)
    for chapter, chapter_snippets in shallow_chapters.items():
        if len(chapter_snippets) >= 2:
            return "SHALLOW_GROWTH_REPEATED", {
                "chapter": chapter,
                "snippets": chapter_snippets,
                "preceding_fails": failures,
            }

    # 3. LAKE_BUILD_STUCK_DUP
    if "Pre-merge hard gate failed: lake build" in text and re.search(
        r"already declared|duplicate declaration|function: .* has multiple definitions",
        text,
        re.IGNORECASE,
    ):
        return "LAKE_BUILD_STUCK_DUP", {
            "symbol": _extract_duplicate_symbol(text),
            "file": _extract_file_path(text),
            "snippet": "\n".join(snippets[-3:]) or text[-1200:],
            "preceding_fails": failures,
        }

    # 4. PUSH_LOCK_STARVATION
    m = re.search(r"push lock for branch.*held for more than \d+s", text)
    if m:
        return "PUSH_LOCK_STARVATION", {
            "snippet": m.group(0),
            "preceding_fails": failures,
            "suggested_action": (
                "降低 tools/auto_tune_concurrency.py 里的 LEAN_MAX 或 PAPER_MAX，"
                "或调整 push lock 拓扑"
            ),
        }

    # 5. CODEX_API_FAILURE
    if re.search(r"Codex exec completed in \d+(?:\.\d+)?s \(rc=1\)", text):
        if re.search(r"at capacity|Selected model is at capacity|stdout/stderr empty|empty stdout|empty stderr",
                     text, re.IGNORECASE):
            return "CODEX_API_FAILURE", {
                "snippet": "\n".join(snippets[-3:]) or text[-1200:],
                "preceding_fails": failures,
            }

    # 6. UNKNOWN
    return "UNKNOWN", {
        "raw_error_snippets": snippets,
        "preceding_fails": failures,
    }


def _load_cooldown_state() -> dict:
    try:
        data = json.loads(COOLDOWN_STATE_FILE.read_text())
    except Exception:
        data = {}
    now = datetime.now()
    kept = []
    for row in data.get("recent_fixes", []):
        try:
            attempted_at = datetime.fromisoformat(row.get("attempted_at", ""))
        except ValueError:
            continue
        if now - attempted_at < timedelta(hours=COOLDOWN_STATE_KEEP_HOURS):
            kept.append(row)
    return {"recent_fixes": kept}


def _write_cooldown_state(state: dict) -> None:
    try:
        COOLDOWN_STATE_FILE.write_text(
            json.dumps(state, ensure_ascii=False, indent=2, sort_keys=True)
        )
    except Exception as exc:
        print(f"[heal] cooldown state write failed: {exc}", file=sys.stderr)


def hot_fix_recently_attempted(category: str, details: dict) -> bool:
    state = _load_cooldown_state()
    wanted = _details_hash(category, details)
    now = datetime.now()
    for row in state.get("recent_fixes", []):
        if row.get("category") != category or row.get("details_hash") != wanted:
            continue
        try:
            attempted_at = datetime.fromisoformat(row.get("attempted_at", ""))
        except ValueError:
            continue
        if now - attempted_at < timedelta(minutes=COOLDOWN_FIX_DEDUP_MINUTES):
            return True
    return False


def _mark_hot_fix_attempt(category: str, details: dict, commit_sha: str = "") -> None:
    state = _load_cooldown_state()
    state.setdefault("recent_fixes", []).append({
        "category": category,
        "details_hash": _details_hash(category, details),
        "attempted_at": datetime.now().isoformat(timespec="seconds"),
        "commit_sha": commit_sha,
    })
    _write_cooldown_state(state)


def _format_preceding_fails(details: dict) -> list[str]:
    rows = details.get("preceding_fails", [])
    if not rows and details.get("raw_error_snippets"):
        rows = [{"round_id": "?", "snippet": s} for s in details["raw_error_snippets"]]
    out = []
    for row in rows[:3]:
        out.append(f"{row.get('round_id','?')}: {row.get('snippet','')[:240]}")
    return out or ["?: no preceding failure snippet captured"]


def format_heal_alert(category: str, details: dict, *, cooldown_count: int, note: str = "") -> str:
    ts = time.strftime("%Y-%m-%d %H:%M:%S")
    lines = [
        f"[{ts}] HEAL ALERT category={category}",
        f"  cooldown_count_1h={cooldown_count}",
        "  preceding_fails:",
    ]
    for item in _format_preceding_fails(details):
        lines.append(f"    - {item}")
    suggested = details.get("suggested_action") or {
        "CODEX_API_FAILURE": "等待模型容量恢复，或降低并发 codex 派发量",
        "UNKNOWN": "检查捕获到的 cooldown 时间点附近的 orchestrator 日志",
        "PUSH_LOCK_STARVATION": (
            "降低 tools/auto_tune_concurrency.py 里的 LEAN_MAX 或 PAPER_MAX，"
            "或调整 push lock 拓扑"
        ),
        "LOCAL_CI_FAILED_AFTER_HEAL": "保留 alert，人工查看本地 CI 尾部并重新设计 heal",
        "RECURRING_FIX_LOOP": "停止重复派发 codex，人工检查近期 git log 与失败签名",
    }.get(category, "需要人工分诊")
    lines.append(f"  suggested_action: {suggested}")
    if note:
        lines.append(f"  note: {note}")
    return "\n".join(lines) + "\n"


def log_heal_info(message: str) -> None:
    print(message, file=sys.stderr)


def log_heal_alert(
    category: str,
    details: dict,
    *,
    cooldown_count: int,
    note: str = "",
    dry_run: bool = False,
) -> None:
    entry = format_heal_alert(category, details, cooldown_count=cooldown_count, note=note)
    if dry_run:
        print("[heal] dry-run alert entry:", file=sys.stderr)
        print(entry.rstrip(), file=sys.stderr)
        return
    try:
        with COOLDOWN_ALERT_LOG.open("a", encoding="utf-8") as f:
            f.write(entry)
    except Exception as exc:
        print(f"[heal] alert log write failed: {exc}", file=sys.stderr)
    for line in entry.rstrip().splitlines():
        print(f"[heal] {line}", file=sys.stderr)


def _slug_for_commit(text: str) -> str:
    slug = re.sub(r"[^A-Za-z0-9_]+", "_", text).strip("_").lower()
    return slug[:60] or "unknown"


def _build_hot_fix_prompt(category: str, details: dict) -> str:
    if category == "NO_BEDC_TOUCHPOINT_NARROW":
        symbol = details.get("symbol") or details.get("decl") or "BEDC"
        return COOLDOWN_NO_TOUCHPOINT_PROMPT.format(
            decl=details.get("decl", "?"),
            file=details.get("file", "?"),
            symbol=symbol,
            snippet=details.get("snippet", ""),
        )
    if category == "SHALLOW_GROWTH_REPEATED":
        chapter = details.get("chapter", "unknown")
        return COOLDOWN_SHALLOW_PROMPT.format(
            chapter=chapter,
            slug=_slug_for_commit(chapter),
            snippet="\n".join(details.get("snippets", [])),
        )
    if category == "LAKE_BUILD_STUCK_DUP":
        symbol = details.get("symbol") or "unknown"
        return COOLDOWN_LAKE_DUP_PROMPT.format(
            symbol=symbol,
            snippet=details.get("snippet", ""),
        )
    raise ValueError(f"unsupported hot-fix category: {category}")


def attempt_hot_fix(category: str, details: dict, *, dry_run: bool = False) -> str:
    prompt = _build_hot_fix_prompt(category, details)
    if dry_run:
        print(f"[heal] dry-run would dispatch cooldown hot-fix: {category}", file=sys.stderr)
        print(prompt[:1200], file=sys.stderr)
        return ""
    signature = f"cooldown {category} {_details_hash(category, details)}"
    if _recurring_fix_loop(signature, "cooldown hot-fix", details):
        return ""
    prompt = _with_fix_signature(prompt, signature)
    head_before = git("rev-parse", "HEAD", capture=True).stdout.strip()
    _mark_hot_fix_attempt(category, details, "")
    rc = call_codex(prompt, timeout=1800)
    head_after = git("rev-parse", "HEAD", capture=True).stdout.strip()
    if head_after == head_before:
        print(f"[heal] cooldown hot-fix made no commit (category={category}, rc={rc})",
              file=sys.stderr)
        return ""
    _mark_hot_fix_attempt(category, details, head_after)
    return head_after


def cooldown_analysis_phase(
    *,
    dry_run: bool = False,
    cooldowns_override: list[dict] | None = None,
) -> bool:
    """Analyze recent cooldowns. Returns True iff a hot-fix commit was made."""
    cooldowns = (
        cooldowns_override
        if cooldowns_override is not None
        else detect_recent_cooldowns(window_minutes=COOLDOWN_WINDOW_MINUTES)
    )
    if len(cooldowns) < COOLDOWN_THRESHOLD:
        if dry_run:
            print(f"[heal] dry-run cooldowns below threshold: {len(cooldowns)}/"
                  f"{COOLDOWN_THRESHOLD}", file=sys.stderr)
        return False

    made_commit = False
    seen_buckets: set[str] = set()
    for cooldown in cooldowns:
        category, details = classify_cooldown_cause(cooldown)
        details["cooldown_timestamp"] = cooldown.get("timestamp", "")
        bucket = _details_hash(category, details)
        if bucket in seen_buckets:
            continue
        seen_buckets.add(bucket)
        if not dry_run and category == "PUSH_LOCK_STARVATION" and not verify_push_lock_starvation_recent():
            _act_verify_skip(f"cooldown {category} {bucket}")
            continue
        if not dry_run and category in HOT_FIXABLE_CATEGORIES and not verify_phase_d_lint_still_rejects(
            {"category": category, "details": details}
        ):
            _act_verify_skip(f"cooldown {category} {bucket}")
            continue
        if hot_fix_recently_attempted(category, details):
            log_heal_alert(
                category,
                details,
                cooldown_count=len(cooldowns),
                note="近 60 分钟内已尝试同类 hot-fix，转交外部监控",
                dry_run=dry_run,
            )
            continue
        if category in HOT_FIXABLE_CATEGORIES:
            commit_sha = attempt_hot_fix(category, details, dry_run=dry_run)
            if commit_sha:
                log_heal_info(f"[heal] cooldown hot-fix applied: {category} -> {commit_sha}")
                made_commit = True
                break
            if dry_run:
                continue
            log_heal_alert(
                category,
                details,
                cooldown_count=len(cooldowns),
                note="hot-fix 未产生提交，转交外部监控",
            )
        else:
            log_heal_alert(category, details, cooldown_count=len(cooldowns), dry_run=dry_run)
    return made_commit


def run_cooldown_self_test() -> int:
    cases = [
        ("NO_BEDC_TOUCHPOINT_NARROW", {
            "line": "[cooldown] 3 failures",
            "failures": [{"round_id": "R1", "snippet":
                          "[ERROR] [R1] NO BEDC TOUCHPOINT: FieldFaithful_bridge in lean4/BEDC/Derived/FooUp.lean"}],
            "context": [],
        }),
        ("SHALLOW_GROWTH_REPEATED", {
            "line": "[cooldown] 3 failures",
            "failures": [
                {"round_id": "R2", "snippet":
                 "[ERROR] [R2] SHALLOW GROWTH PATTERN: lean4/BEDC/Derived/Foo.lean duplicate theorem conclusion"},
                {"round_id": "R3", "snippet":
                 "[ERROR] [R3] SHALLOW GROWTH PATTERN: lean4/BEDC/Derived/Foo.lean duplicate theorem conclusion"},
            ],
            "context": [],
        }),
        ("LAKE_BUILD_STUCK_DUP", {
            "line": "[cooldown] 3 failures",
            "failures": [{"round_id": "R4", "snippet":
                          "[ERROR] [R4] Pre-merge hard gate failed: lake build\nerror: already declared Foo.bar"}],
            "context": ["error: already declared Foo.bar"],
        }),
        ("PUSH_LOCK_STARVATION", {
            "line": "[cooldown] 3 failures",
            "failures": [{"round_id": "P5", "snippet":
                          "[ERROR] push lock for branch 'codex-auto-dev' held for more than 600s"}],
            "context": [],
        }),
        ("CODEX_API_FAILURE", {
            "line": "[cooldown] 3 failures",
            "failures": [{"round_id": "R6", "snippet":
                          "Codex exec completed in 42s (rc=1): Selected model is at capacity"}],
            "context": [],
        }),
        ("UNKNOWN", {
            "line": "[cooldown] 3 failures",
            "failures": [{"round_id": "R7", "snippet": "[ERROR] unclassified failure"}],
            "context": [],
        }),
    ]
    ok = True
    for expected, cooldown in cases:
        actual, details = classify_cooldown_cause(cooldown)
        print(f"[heal] self-test {expected}: got {actual}", file=sys.stderr)
        if actual != expected:
            ok = False
        if expected == "PUSH_LOCK_STARVATION" and actual in HOT_FIXABLE_CATEGORIES:
            ok = False
        if expected == "CODEX_API_FAILURE" and actual in HOT_FIXABLE_CATEGORIES:
            ok = False
        if expected == "UNKNOWN" and actual in HOT_FIXABLE_CATEGORIES:
            ok = False
        if expected == "UNKNOWN":
            print(format_heal_alert(actual, details, cooldown_count=3).rstrip(),
                  file=sys.stderr)
    return 0 if ok else 1


def run_verify_only() -> int:
    """Print act-verify results for currently detected log symptoms."""
    _reset_act_verify_cache()
    propext_v = detect_propext_violations_from_log()
    if not propext_v:
        print("[heal] verify-only propext: no detected symptoms", file=sys.stderr)
    for thm in propext_v[:5]:
        ok = verify_propext_still_impure(thm)
        print(f"[heal] verify-only propext {thm}: {ok}", file=sys.stderr)

    storms = detect_gate_storms()
    if not storms:
        print("[heal] verify-only gate-storm: no detected symptoms", file=sys.stderr)
    for storm in storms[:5]:
        target: object = storm
        if "axiom-purity" in storm.get("gate", ""):
            target = propext_v[0] if propext_v else ""
        ok = verify_gate_still_failing(storm.get("gate", ""), target)
        print(
            f"[heal] verify-only gate-storm {storm.get('gate','?')}: {ok}",
            file=sys.stderr,
        )

    cooldowns = detect_recent_cooldowns(window_minutes=COOLDOWN_WINDOW_MINUTES)
    if not cooldowns:
        print("[heal] verify-only cooldown: no detected symptoms", file=sys.stderr)
    seen_buckets: set[str] = set()
    for cooldown in cooldowns:
        category, details = classify_cooldown_cause(cooldown)
        details["cooldown_timestamp"] = cooldown.get("timestamp", "")
        bucket = _details_hash(category, details)
        if bucket in seen_buckets:
            continue
        seen_buckets.add(bucket)
        if category == "PUSH_LOCK_STARVATION":
            ok = verify_push_lock_starvation_recent()
        elif category in HOT_FIXABLE_CATEGORIES:
            ok = verify_phase_d_lint_still_rejects({"category": category, "details": details})
        else:
            ok = True
        print(f"[heal] verify-only cooldown {category} {bucket}: {ok}", file=sys.stderr)
    return 0


def push_to_origin() -> bool:
    res = run(["git", "push", "origin", BASE_BRANCH],
              check=False, capture=True, timeout=60)
    if res.returncode != 0:
        print(f"[heal] push failed: {res.stderr}", file=sys.stderr)
        return False
    return True


def cycle() -> None:
    """One healing cycle: fetch, audit, heal if needed, push."""
    _reset_act_verify_cache()
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
    # Cooldown cause analysis runs FIRST, observation-only / alert-only.
    # Previously this was at end of cycle but never reached because
    # every prior heal phase (dup labels / CI / propext / gate-storm)
    # ends with `return  # one heal per cycle is enough`. Running it
    # first means alerts + (optionally) one cooldown hot-fix get
    # dispatched even when later heal phases also fire. Hot-fix
    # dispatch returns its own commit which the cycle then pushes;
    # other phases run on next cycle.
    try:
        if cooldown_analysis_phase():
            verify_then_push("cooldown hot-fix")
            return  # one cooldown hot-fix this cycle
    except Exception as exc:
        print(f"[heal] cooldown_analysis_phase crashed: {exc}",
              file=sys.stderr)
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
                verify_then_push("stuck dirt")
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
            verify_then_push("dup labels")
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
                verify_then_push("CI fix")
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
            verify_then_push("propext")
            return  # one heal per cycle is enough
    else:
        print("[heal] no propext violation in log tail", flush=True)

    # Detect generic gate-failure storms in orchestrator logs.
    storms = detect_gate_storms()
    if not storms:
        print("[heal] no gate-failure storm in last 30min", flush=True)
    else:
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
            verify_then_push(f"gate storm: {top['gate']}")
            return

    # Cooldown analysis already ran at top of cycle (alerts written + at most
    # one hot-fix dispatched). Nothing more to do here.


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--interval", type=int, default=DEFAULT_INTERVAL,
                    help="Cycle interval seconds (default 900)")
    p.add_argument("--once", action="store_true",
                    help="Run a single cycle and exit (for testing)")
    p.add_argument("--dry-run", action="store_true",
                    help="Run cooldown detection/classification only; no codex, no alert writes")
    p.add_argument("--self-test", action="store_true",
                    help="Run cooldown classifier self-tests and exit")
    p.add_argument("--verify-only", action="store_true",
                    help="Detect log symptoms, verify current state, and exit without dispatch")
    args = p.parse_args()

    if args.self_test:
        return run_cooldown_self_test()

    if args.verify_only:
        return run_verify_only()

    if args.dry_run:
        print("[heal] dry-run helpers available: verify_local_ci, recent_fix_signature_seen",
              file=sys.stderr)
        stdin_text = ""
        if not sys.stdin.isatty():
            stdin_text = sys.stdin.read()
        cooldowns = None
        if stdin_text.strip():
            cooldowns = detect_recent_cooldowns_from_text(stdin_text)
            print(f"[heal] dry-run parsed {len(cooldowns)} cooldown(s) from stdin",
                  file=sys.stderr)
        cooldown_analysis_phase(dry_run=True, cooldowns_override=cooldowns)
        return 0

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
