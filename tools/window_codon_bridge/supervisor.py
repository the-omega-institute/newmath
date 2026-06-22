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
import argparse, fnmatch, json, os, subprocess, sys, tempfile, time
import fcntl
import importlib
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent           # tools/window_codon_bridge
REPO_ROOT = SCRIPT_DIR.parents[1]                       # bridge worktree root
CLAIMS = SCRIPT_DIR / "registries" / "claims.json"
EXPS = SCRIPT_DIR / "registries" / "experiments.json"
SYNC_MANIFEST = SCRIPT_DIR / "registries" / "sync_manifest.json"
SYNCED_DIR = SCRIPT_DIR / "synced"
LEDGER = REPO_ROOT / "papers" / "window_codon_bridge" / "bridge_ledger.jsonl"
STOP = SCRIPT_DIR / ".stop"
STATE_DIR = SCRIPT_DIR / "state"
LOCK = STATE_DIR / "supervisor.lock"
DEFAULT_INTERVAL = 600.0

sys.path.insert(0, str(SCRIPT_DIR))
import runner  # noqa: E402
import oracle_lane  # noqa: E402
import derivation_lane  # noqa: E402


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


def glob_prefix(pattern: str) -> str:
    wildcard_positions = [pos for token in "*?[" if (pos := pattern.find(token)) >= 0]
    if not wildcard_positions:
        return pattern
    prefix = pattern[: min(wildcard_positions)]
    if "/" in prefix:
        return prefix.rsplit("/", 1)[0]
    return "."


def ls_matching(branch: str, pattern: str) -> subprocess.CompletedProcess:
    prefix = glob_prefix(pattern)
    listing = git("ls-tree", "-r", "--name-only", f"origin/{branch}", "--", prefix)
    if listing.returncode != 0:
        return listing
    paths = sorted(p for p in (listing.stdout or "").splitlines() if p and fnmatch.fnmatch(p, pattern))
    listing.stdout = "\n".join(paths) + ("\n" if paths else "")
    return listing


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

    # Bridge intake sometimes needs a visible surface, not every source body.
    # These optional manifest keys are additive: existing single-file entries
    # keep their behavior, while glob materialization and inventories let the
    # daemon watch compact cross-branch surfaces without changing registries.
    for item in manifest.get("materialize_globs", []):
        branch = str(item.get("branch") or "")
        src_glob = str(item.get("src_glob") or "")
        dest_dir = str(item.get("dest_dir") or "")
        strip_prefix = str(item.get("strip_prefix") or "")
        if not branch or not src_glob or not dest_dir:
            continue
        listing = ls_matching(branch, src_glob)
        if listing.returncode != 0:
            summary["pending"].append(dest_dir)
            print(f"[sync] pending glob: {branch}:{src_glob}", flush=True)
            continue
        paths = sorted(p for p in (listing.stdout or "").splitlines() if p)
        for src_path in paths:
            rel = src_path
            if strip_prefix and src_path.startswith(strip_prefix.rstrip("/") + "/"):
                rel = src_path[len(strip_prefix.rstrip("/") + "/") :]
            dest = str(Path(dest_dir) / rel)
            r = git("show", f"origin/{branch}:{src_path}")
            if r.returncode != 0:
                summary["pending"].append(dest)
                print(f"[sync] pending: {branch}:{src_path}", flush=True)
                continue
            out = r.stdout or ""
            target = SYNCED_DIR / dest
            old = target.read_text(encoding="utf-8") if target.exists() else None
            if old != out:
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_text(out, encoding="utf-8")
                summary["materialized"].append(dest)
                print(f"[sync] materialized {dest}", flush=True)

    for item in manifest.get("materialize_inventories", []):
        branch = str(item.get("branch") or "")
        src_glob = str(item.get("src_glob") or "")
        dest = str(item.get("dest") or "")
        if not branch or not src_glob or not dest:
            continue
        listing = ls_matching(branch, src_glob)
        if listing.returncode != 0:
            summary["pending"].append(dest)
            print(f"[sync] pending inventory: {branch}:{src_glob}", flush=True)
            continue
        paths = sorted(p for p in (listing.stdout or "").splitlines() if p)
        out = json.dumps(
            {
                "branch": branch,
                "src_glob": src_glob,
                "paths": paths,
            },
            indent=2,
            sort_keys=True,
        ) + "\n"
        target = SYNCED_DIR / dest
        old = target.read_text(encoding="utf-8") if target.exists() else None
        if old != out:
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text(out, encoding="utf-8")
            summary["materialized"].append(dest)
            print(f"[sync] materialized {dest}", flush=True)
    return summary


def _concordance_row_key(row: dict) -> str:
    parts = [
        row.get("source", ""),
        row.get("kind", ""),
        row.get("path", ""),
        row.get("experiment_id", ""),
        row.get("claim_id", ""),
        row.get("topic_key", ""),
    ]
    return "\0".join(str(part) for part in parts)


def _concordance_homeless_key(row: dict) -> str:
    parts = [
        _concordance_row_key(row),
        row.get("bridge_class", ""),
        row.get("crosswalk_relation", ""),
    ]
    return "\0".join(str(part) for part in parts)


def _concordance_watch_set(payload: dict) -> set[str]:
    rows = payload.get("rows", [])
    if not isinstance(rows, list):
        return set()
    watched = set()
    for row in rows:
        if not isinstance(row, dict):
            continue
        if row.get("bridge_class") in {"bio_only", "math_stub", "needs_derivation"}:
            watched.add(_concordance_homeless_key(row))
    return watched


def _concordance_reopening_set(payload: dict) -> set[str]:
    rows = payload.get("rows", [])
    if not isinstance(rows, list):
        return set()
    return {
        _concordance_row_key(row)
        for row in rows
        if isinstance(row, dict) and row.get("bridge_class") == "reopening_candidate"
    }


def _concordance_summary(payload: dict) -> dict:
    counts = payload.get("counts", {}) if isinstance(payload, dict) else {}
    relation_counts = counts.get("by_crosswalk_relation", {}) if isinstance(counts, dict) else {}
    return {
        "status": "generated",
        "n_fibonacci_bstarq6": counts.get("n_fibonacci_bstarq6", 0),
        "n_bio_bstarq6": counts.get("n_bio_bstarq6", 0),
        "n_duplicate": counts.get("n_duplicate", 0),
        "n_param_divergence": relation_counts.get("param_divergence", 0),
        "n_fibonacci_only": relation_counts.get("fibonacci_only", 0),
        "n_reopening_candidate": counts.get("n_reopening_candidate", 0),
        "n_homeless": counts.get("n_homeless", 0),
    }


def _load_worktree_coverage() -> dict:
    path = REPO_ROOT / "papers" / "window_codon_bridge" / "intake_coverage.json"
    return json.loads(path.read_text(encoding="utf-8"))


def _run_coverage_generator() -> tuple[dict, str]:
    try:
        module = importlib.import_module("intake_coverage")
        if hasattr(module, "generate"):
            return module.generate(), "import"
        if hasattr(module, "main"):
            module.main()
            return _load_worktree_coverage().get("summary", {}), "import"
    except ImportError:
        pass
    proc = subprocess.run(
        [sys.executable, "tools/window_codon_bridge/intake_coverage.py"],
        cwd=str(REPO_ROOT),
        capture_output=True,
        text=True,
    )
    if proc.returncode != 0:
        raise RuntimeError(((proc.stderr or proc.stdout) or "").strip()[-500:])
    parsed = None
    for line in reversed((proc.stdout or "").strip().splitlines()):
        if not line.strip().startswith("{"):
            continue
        parsed = json.loads(line)
        break
    if parsed is None:
        parsed = _load_worktree_coverage().get("summary", {})
    return parsed, "subprocess"


def coverage_lane() -> dict:
    try:
        summary, mode = _run_coverage_generator()
        result = {"ran": True, "mode": mode, "summary": summary}
        print(f"[coverage] ran mode={mode} summary={summary}", flush=True)
        return result
    except Exception as exc:
        error = str(exc)
        print(f"[coverage] skipped: {error}", flush=True)
        return {"ran": False, "error": error}


def _load_committed_concordance() -> dict | None:
    rel = "papers/window_codon_bridge/cross_branch_concordance.json"
    proc = git("show", f"HEAD:{rel}")
    if proc.returncode != 0:
        return None
    return json.loads(proc.stdout)


def _load_worktree_concordance() -> dict:
    path = REPO_ROOT / "papers" / "window_codon_bridge" / "cross_branch_concordance.json"
    return json.loads(path.read_text(encoding="utf-8"))


def _run_concordance_generator() -> tuple[dict, str]:
    try:
        module = importlib.import_module("cross_branch_concordance")
        if hasattr(module, "generate"):
            return module.generate(), "import"
        if hasattr(module, "main"):
            module.main()
            return _concordance_summary(_load_worktree_concordance()), "import"
    except ImportError:
        pass
    proc = subprocess.run(
        [sys.executable, "tools/window_codon_bridge/cross_branch_concordance.py"],
        cwd=str(REPO_ROOT),
        capture_output=True,
        text=True,
    )
    if proc.returncode != 0:
        raise RuntimeError(((proc.stderr or proc.stdout) or "").strip()[-500:])
    parsed = None
    for line in reversed((proc.stdout or "").strip().splitlines()):
        if not line.strip().startswith("{"):
            continue
        parsed = json.loads(line)
        break
    if parsed is None:
        parsed = _concordance_summary(_load_worktree_concordance())
    return parsed, "subprocess"


def concordance_lane() -> dict:
    try:
        previous = _load_committed_concordance()
        generated_summary, mode = _run_concordance_generator()
        current = _load_worktree_concordance()
        summary = _concordance_summary(current)
        if isinstance(generated_summary, dict):
            summary.update(generated_summary)
        changed = []
        new_reopening_candidates = 0

        if previous is None:
            changed.append("baseline_missing")
        else:
            prev_counts = _concordance_summary(previous)
            curr_counts = _concordance_summary(current)
            for key in ("n_duplicate", "n_param_divergence", "n_fibonacci_only"):
                if prev_counts.get(key) != curr_counts.get(key):
                    changed.append(key)
            prev_reopening = _concordance_reopening_set(previous)
            curr_reopening = _concordance_reopening_set(current)
            new_reopening_candidates = len(curr_reopening - prev_reopening)
            if new_reopening_candidates:
                changed.append("new_reopening_candidate")
            if _concordance_watch_set(previous) != _concordance_watch_set(current):
                changed.append("homeless_needs_derivation_set")

        drift = bool(changed)
        result = {
            "ran": True,
            "mode": mode,
            "drift": drift,
            "new_reopening_candidates": new_reopening_candidates,
            "changed": changed,
            "summary": summary,
        }
        if drift:
            print(f"[concordance] drift: changed={changed} summary={summary}", flush=True)
            if new_reopening_candidates:
                print(f"[concordance] ALERT: {new_reopening_candidates} new reopening_candidate item(s)", flush=True)
        else:
            print(f"[concordance] ran mode={mode} drift=False summary={summary}", flush=True)
        return result
    except Exception as exc:
        error = str(exc)
        print(f"[concordance] skipped: {error}", flush=True)
        return {"ran": False, "error": error}


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


def paper_lane() -> dict:
    paper_dir = REPO_ROOT / "papers" / "window_codon_bridge"
    env = os.environ.copy()
    env["PATH"] = ":".join([
        "/Library/TeX/texbin",
        "/opt/homebrew/bin",
        "/usr/local/bin",
        env.get("PATH", "/usr/bin:/bin:/usr/sbin:/sbin"),
    ])
    build = subprocess.run(
        ["make"],
        cwd=str(paper_dir),
        env=env,
        capture_output=True,
        text=True,
    )
    ok = build.returncode == 0
    result = {
        "generated": ok,
        "gate_ok": ok,
        "pdf_ok": ok,
    }
    if not ok:
        result["build_error"] = ((build.stderr or build.stdout) or "")[-500:]
    print(
        f"[paper] generated={result['generated']} gate_ok={result['gate_ok']} pdf_ok={result['pdf_ok']}",
        flush=True,
    )
    return result


def assimilation_lane() -> dict:
    proc = subprocess.run(
        [sys.executable, str(SCRIPT_DIR / "oracle_assimilator.py")],
        cwd=str(REPO_ROOT),
        capture_output=True,
        text=True,
    )
    result = {"ran": proc.returncode == 0}
    parsed = None
    for line in reversed((proc.stdout or "").strip().splitlines()):
        if not line.strip().startswith("{"):
            continue
        try:
            parsed = json.loads(line)
            break
        except json.JSONDecodeError:
            continue
    if parsed:
        result.update(parsed)
    if proc.returncode != 0:
        result["error"] = ((proc.stderr or proc.stdout) or "")[-300:]
    print(f"[assimilation] {result}", flush=True)
    return result


def keep_lane():
    """Lean commit lane: commit changed bridge files on this branch.

    Only commits when there is a real SCIENCE content delta (new/changed claim
    verdicts, registered experiments, ledger entries, or oracle plans). PDF/aux
    rebuild churn and oracle-session timestamps never trigger a commit on their
    own -- a no-output cycle must not push (that would be pollution).
    """
    # Science content whose change is a real research output.
    # NOTE: state/oracle_assimilation is intentionally EXCLUDED -- the assimilation
    # lane rewrites latest_*_plan.{json,md} every cycle with only a generated_ts
    # timestamp bump (identical content), which is pure churn. New oracle content
    # is already captured by oracle_inbox/candidates.jsonl (only appended on an
    # actual oracle query), so the timestamp rewrite must not trigger a commit.
    science_paths = (
        "tools/window_codon_bridge/registries/claims.json",
        "tools/window_codon_bridge/registries/experiments.json",
        "tools/window_codon_bridge/oracle_inbox/candidates.jsonl",
        "papers/window_codon_bridge/bridge_ledger.jsonl",
        "papers/window_codon_bridge/intake_coverage.json",
        "papers/window_codon_bridge/cross_branch_concordance.json",
    )
    # Everything committed alongside when (and only when) science changed; the
    # rebuilt PDF then reflects the new science. These paths alone are churn.
    tracked_paths = (
        "tools/window_codon_bridge/registries",
        "tools/window_codon_bridge/experiments",
        "tools/window_codon_bridge/oracle_inbox",
        "tools/window_codon_bridge/state/oracle_assimilation",
        "tools/window_codon_bridge/state/oracle_sessions",
        "papers/window_codon_bridge",
    )
    science_delta = git("status", "--porcelain", *science_paths).stdout.strip()
    if not science_delta:
        return {"committed": False, "reason": "no_science_delta"}
    git("add", *tracked_paths)
    r = git("commit", "-m", f"Bridge cycle {now_iso()}: derivation verdicts + ledger")
    return {"committed": r.returncode == 0, "out": (r.stdout or r.stderr)[-200:]}


def should_stop() -> bool:
    return STOP.exists()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--once", action="store_true")
    ap.add_argument("--interval-seconds", type=float, default=DEFAULT_INTERVAL)
    ap.add_argument("--no-commit", action="store_true")
    ap.add_argument("--no-oracle", action="store_true")
    ap.add_argument("--no-derive", action="store_true")
    ap.add_argument("--no-concordance", action="store_true")
    ap.add_argument("--no-coverage", action="store_true")
    args = ap.parse_args()
    STATE_DIR.mkdir(parents=True, exist_ok=True)
    with LOCK.open("w", encoding="utf-8") as lock_fh:
        try:
            fcntl.flock(lock_fh.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            print("[supervisor] another window-codon bridge supervisor is running", flush=True)
            return
        lock_fh.write(str(os.getpid()))
        lock_fh.flush()
        while not should_stop():
            sync = sync_lane()
            coverage = {"ran": False, "reason": "disabled_by_flag"} if args.no_coverage else coverage_lane()
            concordance = {"ran": False, "reason": "disabled_by_flag"} if args.no_concordance else concordance_lane()
            summary = run_cycle()
            oracle = {"ran": False, "reason": "disabled_by_flag"} if args.no_oracle else oracle_lane.run_oracle_lane()
            assimilation = assimilation_lane()
            derivation = {"ran": False, "reason": "disabled_by_flag"} if args.no_derive else derivation_lane.run_derivation_lane()
            paper = paper_lane()
            keep = {} if args.no_commit else keep_lane()
            publish = {} if args.no_commit else publish_lane()
            print(f"[{summary['ts']}] bridge cycle executed={summary['executed']} verdicts={summary['verdicts']} sync={sync} coverage={coverage} concordance={concordance} oracle={oracle} assimilation={assimilation} derivation={derivation} paper={paper} keep={keep} publish={publish}", flush=True)
            if args.once:
                break
            time.sleep(max(1.0, float(args.interval_seconds)))


if __name__ == "__main__":
    main()
