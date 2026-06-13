#!/usr/bin/env python3
"""Window6<->codon-Q6 bridge daemon supervisor (lean engine).

One cycle:
  1. load bridge registries (claims + experiments)
  2. for each open/needs_rerun claim: run its derivation experiment -> verdict
       certified / refuted / coincidence / needs_derivation
  3. write back registries (atomic) + append to bridge_ledger.jsonl
  4. commit changed files on this branch (lean keep lane), then sleep

Verdict discipline (anti-numerology): a numeric match alone is 'coincidence', never
'certified'. 'certified' requires the experiment to assert a structural forcing argument.

Flags: --once (single cycle, no sleep), --interval-seconds N.
Stop sentinel: tools/window_codon_bridge/.stop
"""
from __future__ import annotations
import argparse, json, os, subprocess, sys, tempfile, time
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent           # tools/window_codon_bridge
REPO_ROOT = SCRIPT_DIR.parents[1]                       # bridge worktree root
CLAIMS = SCRIPT_DIR / "registries" / "claims.json"
EXPS = SCRIPT_DIR / "registries" / "experiments.json"
SYNC_MANIFEST = SCRIPT_DIR / "registries" / "sync_manifest.json"
SYNCED_DIR = SCRIPT_DIR / "synced"
LEDGER = REPO_ROOT / "papers" / "window_codon_bridge" / "bridge_ledger.jsonl"
STOP = SCRIPT_DIR / ".stop"
DEFAULT_INTERVAL = 600.0

sys.path.insert(0, str(SCRIPT_DIR))
import runner  # noqa: E402


def now_iso() -> str:
    return subprocess.run(["date", "-u", "+%Y-%m-%dT%H:%M:%S+00:00"], capture_output=True, text=True).stdout.strip()


def load(path):
    return json.loads(path.read_text(encoding="utf-8"))


def atomic_write(path: Path, obj):
    fd, tmp = tempfile.mkstemp(dir=str(path.parent), suffix=".tmp")
    with os.fdopen(fd, "w", encoding="utf-8") as fh:
        json.dump(obj, fh, indent=1, ensure_ascii=False)
        fh.write("\n")
    os.replace(tmp, str(path))


def append_ledger(entry: dict):
    LEDGER.parent.mkdir(parents=True, exist_ok=True)
    with open(LEDGER, "a", encoding="utf-8") as fh:
        fh.write(json.dumps(entry, ensure_ascii=False) + "\n")


def git(*args) -> subprocess.CompletedProcess:
    return subprocess.run(["git", "-C", str(REPO_ROOT), *args], capture_output=True, text=True)


def git_busy() -> bool:
    return subprocess.run(["pgrep", "-x", "git"], capture_output=True).returncode == 0


def sync_lane() -> dict:
    if git_busy():
        print("[sync] skipped (git busy)", flush=True)
        return {"skipped": "git_busy"}

    manifest = load(SYNC_MANIFEST)
    fetch_branches = [str(b) for b in manifest.get("fetch_branches", [])]
    summary = {"fetched": False, "materialized": [], "pending": [], "fetch_error": False}

    if fetch_branches:
        r = git("fetch", "origin", *fetch_branches)
        summary["fetched"] = r.returncode == 0
        if r.returncode != 0:
            summary["fetch_error"] = True
            print(f"[sync] fetch failed: {((r.stderr or r.stdout) or '').strip()[-300:]}", flush=True)

    for item in manifest.get("materialize", []):
        branch = str(item.get("branch") or "")
        src = str(item.get("src") or "")
        dest = str(item.get("dest") or "")
        if not branch or not src or not dest:
            continue
        r = git("show", f"origin/{branch}:{src}")
        if r.returncode != 0:
            summary["pending"].append(dest)
            print(f"[sync] pending: {branch}:{src}", flush=True)
            continue
        out = r.stdout or ""
        target = SYNCED_DIR / dest
        old = target.read_text(encoding="utf-8") if target.exists() else None
        if old != out:
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text(out, encoding="utf-8")
            summary["materialized"].append(dest)
            print(f"[sync] materialized {dest}", flush=True)
    return summary


def publish_lane() -> dict:
    if git_busy():
        print("[publish] skipped (git busy)", flush=True)
        return {"skipped": "git_busy"}

    manifest = load(SYNC_MANIFEST)
    publish_branch = str(manifest.get("publish_branch") or "")
    if not publish_branch:
        return {"pushed": False, "reason": "no_publish_branch"}

    rev = git("rev-parse", "--verify", f"origin/{publish_branch}")
    if rev.returncode != 0:
        count = git("rev-list", "--count", "HEAD")
        ahead = int((count.stdout or "1").strip() or "1") if count.returncode == 0 else 1
    else:
        count = git("rev-list", "--count", f"origin/{publish_branch}..HEAD")
        if count.returncode != 0:
            return {"pushed": False, "error": (count.stderr or count.stdout)[-200:]}
        ahead = int((count.stdout or "0").strip() or "0")
    if ahead <= 0:
        return {"pushed": False, "ahead": 0}

    r = git("push", "origin", f"HEAD:{publish_branch}")
    if r.returncode != 0:
        print(f"[publish] push failed, merging origin/{publish_branch}: {((r.stderr or r.stdout) or '').strip()[-300:]}", flush=True)
        git("fetch", "origin", publish_branch)
        merge = git("merge", "--no-edit", f"origin/{publish_branch}")
        if merge.returncode != 0:
            print(f"[publish] merge failed: {((merge.stderr or merge.stdout) or '').strip()[-300:]}", flush=True)
            return {"pushed": False, "ahead": ahead, "merge_error": True}
        r = git("push", "origin", f"HEAD:{publish_branch}")
    if r.returncode != 0:
        print(f"[publish] push failed: {((r.stderr or r.stdout) or '').strip()[-300:]}", flush=True)
        return {"pushed": False, "ahead": ahead, "push_error": True}
    print(f"[publish] pushed {ahead} commits to origin/{publish_branch}", flush=True)
    return {"pushed": True, "ahead": ahead}


def run_cycle() -> dict:
    cdoc = load(CLAIMS)
    edoc = load(EXPS)
    exp_by_id = {e.get("experiment_id"): e for e in edoc.get("experiments", []) if e.get("experiment_id")}
    summary = {"ts": now_iso(), "executed": 0, "verdicts": {}}
    changed = False
    for claim in cdoc.get("claims", []):
        status = str(claim.get("status") or "open")
        if status not in ("open", "needs_rerun"):
            continue
        spec = exp_by_id.get(str(claim.get("experiment_id") or ""))
        if spec is None:
            continue
        result = runner.run_experiment(spec, REPO_ROOT, int(spec.get("timeout_seconds") or 600))
        verdict = result.get("status", "needs_derivation")
        summary["executed"] += 1
        summary["verdicts"][claim.get("claim_id")] = verdict
        if claim.get("status") != verdict:
            changed = True
        claim["status"] = verdict
        claim.setdefault("history", []).append({
            "ts": summary["ts"], "status": verdict,
            "reason": result.get("reason") or result.get("note") or "derivation verdict",
        })
        append_ledger({
            "id": claim.get("claim_id"), "direction": "bridge->verdict", "item": claim.get("statement", ""),
            "status": verdict, "linked_certificate": None,
            "note": (result.get("reason") or result.get("note") or "")[:500], "ts": summary["ts"],
        })
    if changed:
        atomic_write(CLAIMS, cdoc)
    return summary


def keep_lane():
    """Lean commit lane: commit changed bridge files on this branch."""
    st = git("status", "--porcelain", "tools/window_codon_bridge", "papers/window_codon_bridge").stdout.strip()
    if not st:
        return {"committed": False}
    git("add", "tools/window_codon_bridge", "papers/window_codon_bridge")
    r = git("commit", "-m", f"Bridge cycle {now_iso()}: derivation verdicts + ledger")
    return {"committed": r.returncode == 0, "out": (r.stdout or r.stderr)[-200:]}


def should_stop() -> bool:
    return STOP.exists()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--once", action="store_true")
    ap.add_argument("--interval-seconds", type=float, default=DEFAULT_INTERVAL)
    ap.add_argument("--no-commit", action="store_true")
    args = ap.parse_args()
    while not should_stop():
        sync = sync_lane()
        summary = run_cycle()
        keep = {} if args.no_commit else keep_lane()
        publish = {} if args.no_commit else publish_lane()
        print(f"[{summary['ts']}] bridge cycle executed={summary['executed']} verdicts={summary['verdicts']} sync={sync} keep={keep} publish={publish}", flush=True)
        if args.once:
            break
        time.sleep(max(1.0, float(args.interval_seconds)))


if __name__ == "__main__":
    main()
