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
    # Skip if working tree has TRACKED modifications (don't fight a human
    # edit). Untracked files (`?? path`) are tolerated — `_mcp_snippet_*`
    # temp files and similar tooling debris accumulate in the main checkout
    # and would otherwise lock the daemon out forever.
    # `.pipeline_parallel.json` is also tolerated because the autotune
    # daemon rewrites it every 300s — racing isn't a corruption risk for
    # the heal flow (codex never touches that file).
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
        print(f"[heal] working tree has {len(blocking)} tracked modification(s); skipping cycle",
              file=sys.stderr)
        for b in blocking[:3]:
            print(f"[heal]   {b}", file=sys.stderr)
        return
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
    # prompt fix actually drained the top storm).
    top = storms[0]
    print(f"[heal] healing top storm: {top['gate']} ({top['count']} rounds)",
          flush=True)
    if heal_gate_storm(top):
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
