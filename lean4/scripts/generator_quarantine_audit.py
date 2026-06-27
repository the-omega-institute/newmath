#!/usr/bin/env python3
"""Generator-bulk quarantine audit for BEDC.

Adversarial consensus (prosecutor + GPT-pro round-2): the `tools/*_reality`
generators periodically dump large bulk commits (e.g. "BioReality cycle: 138
file(s)") that inflate file/line counts but often carry no new reproducible
mathematical result (one cycle had claim_states passed=148 yet bio_X executed=2,
passed_this_cycle=0 -- registry/namecert churn, not math growth). Such cycles
should be QUARANTINED: not counted toward math-quality KPIs unless the cycle
added a real Lean theorem / artifact pointer.

This audit scans a recent git window for reality-cycle commits and classifies
each as math-bearing (added a Lean theorem/lemma) vs registry-churn (only
paper/namecert/json/registry files), so churn cycles can be excluded from
quality measurement. Git-log based (fast). Informational (exit 0).
"""
import argparse
import json
import re
import subprocess

CYCLE_SUBJECT_RE = re.compile(
    r"\b(?:BioReality|CellstateReality|FibonacciReality|[A-Za-z]*Reality)\s+cycle\b"
    r"|reality[_-]?cycle|reality contact cycle",
    re.IGNORECASE,
)
LEAN_THM_ADD_RE = re.compile(r"^\+\s*(?:theorem|lemma)\s+\w+", re.MULTILINE)


def sh(args, timeout=60):
    try:
        return subprocess.run(args, capture_output=True, text=True,
                              timeout=timeout, cwd="/Users/chronoai/newmath").stdout
    except (subprocess.SubprocessError, OSError):
        return ""


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--since", default="3 days ago")
    ap.add_argument("--branch", default="origin/codex-auto-dev")
    args = ap.parse_args()

    log = sh(["git", "log", "--no-merges", "--since", args.since,
              "--pretty=%H%x09%s", args.branch], timeout=60)
    cycles = []
    for line in log.splitlines():
        if "\t" not in line:
            continue
        sha, subj = line.split("\t", 1)
        if not CYCLE_SUBJECT_RE.search(subj):
            continue
        # files + churn size
        stat = sh(["git", "show", "--stat", "--oneline", sha], timeout=60)
        mfile = re.search(r"(\d+)\s+files?\s+changed", stat)
        files_changed = int(mfile.group(1)) if mfile else 0
        # did it add a Lean theorem? (real math signal)
        leandiff = sh(["git", "show", sha, "--", "lean4/BEDC/"], timeout=60)
        added_thm = len(LEAN_THM_ADD_RE.findall(leandiff))
        verdict = "math_bearing" if added_thm > 0 else "registry_churn"
        cycles.append({
            "sha": sha[:10], "files_changed": files_changed,
            "added_lean_theorems": added_thm, "verdict": verdict,
            "subject": subj[:80],
        })
    churn = [c for c in cycles if c["verdict"] == "registry_churn"]
    out = {
        "window_since": args.since,
        "reality_cycle_commits": len(cycles),
        "math_bearing": len(cycles) - len(churn),
        "registry_churn_to_quarantine": len(churn),
        "churn_files_total": sum(c["files_changed"] for c in churn),
        "cycles": cycles[:40],
        "_note": (
            "registry_churn cycles (no added Lean theorem) should be excluded from "
            "math-quality KPIs -- they are namecert/registry/paper-surface bulk, not "
            "math growth. A cycle counts as math growth only if it adds a Lean "
            "theorem (or, in a fuller version, a reproducible artifact pointer with "
            "tolerance / a passed_this_cycle>0 experiment). Informational."
        ),
    }
    print(json.dumps(out, ensure_ascii=False, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
