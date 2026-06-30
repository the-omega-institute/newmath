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
PIPELINE_CONFIG = SCRIPT_DIR / "pipeline_config.json"
DEV_ROLLUP_STATE = STATE_DIR / "dev_rollup_state.json"
DEFAULT_INTERVAL = 600.0
DEV_BASE_BRANCH = "dev"
PUBLISH_CHURN_PREFIXES = (
    "papers/window_codon_bridge/intake_coverage.json",
    "papers/window_codon_bridge/intake_coverage.md",
    "papers/window_codon_bridge/cross_branch_concordance.json",
    "papers/window_codon_bridge/cross_branch_concordance.md",
    "tools/window_codon_bridge/state/oracle_assimilation/",
)
PUBLISH_SCIENCE_CONFLICT_PATHS = (
    "tools/window_codon_bridge/registries/claims.json",
    "tools/window_codon_bridge/registries/experiments.json",
    "tools/window_codon_bridge/oracle_inbox/candidates.jsonl",
    "papers/window_codon_bridge/bridge_ledger.jsonl",
)

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


def _publish_path(path: str) -> str:
    normalized = path.strip().replace(os.sep, "/")
    while normalized.startswith("./"):
        normalized = normalized[2:]
    return normalized


def _is_publish_churn_path(path: str) -> bool:
    normalized = _publish_path(path)
    for prefix in PUBLISH_CHURN_PREFIXES:
        if prefix.endswith("/"):
            if normalized.startswith(prefix):
                return True
        elif normalized == prefix:
            return True
    return False


def classify_publish_conflicts(files: list[str]) -> tuple[list[str], list[str]]:
    churn = []
    non_churn = []
    for path in files:
        normalized = _publish_path(path)
        if not normalized:
            continue
        if _is_publish_churn_path(normalized):
            churn.append(normalized)
        else:
            non_churn.append(normalized)
    return churn, non_churn


def _merge_head_present() -> bool:
    return git("rev-parse", "-q", "--verify", "MERGE_HEAD").returncode == 0


def _abort_merge_safely() -> bool:
    if not _merge_head_present():
        return True
    git("merge", "--abort")
    if not _merge_head_present():
        return True
    git("reset", "--merge")
    return not _merge_head_present()


def _publish_after_merge_conflict(publish_branch: str, ahead: int) -> dict:
    conflicted = git("diff", "--name-only", "--diff-filter=U")
    if conflicted.returncode != 0:
        _abort_merge_safely()
        return {"pushed": False, "ahead": ahead, "merge_error": True, "conflict_list_error": True}

    files = [_publish_path(line) for line in (conflicted.stdout or "").splitlines() if line.strip()]
    churn, non_churn = classify_publish_conflicts(files)
    if non_churn or not files:
        _abort_merge_safely()
        shown = sorted(non_churn or files)
        print(
            f"[publish] deferred: science conflict on {shown}; left clean local HEAD, will retry next cycle",
            flush=True,
        )
        return {"pushed": False, "deferred": "science_conflict", "files": shown}

    for path in churn:
        checkout = git("checkout", "--ours", "--", path)
        if checkout.returncode != 0:
            _abort_merge_safely()
            return {
                "pushed": False,
                "ahead": ahead,
                "merge_error": True,
                "auto_resolve_error": path,
            }
        add = git("add", "--", path)
        if add.returncode != 0:
            _abort_merge_safely()
            return {
                "pushed": False,
                "ahead": ahead,
                "merge_error": True,
                "auto_resolve_error": path,
            }

    commit = git("commit", "--no-edit")
    if commit.returncode != 0:
        _abort_merge_safely()
        return {"pushed": False, "ahead": ahead, "merge_error": True, "merge_commit_error": True}

    pushed = git("push", "origin", f"HEAD:{publish_branch}")
    if pushed.returncode != 0:
        _abort_merge_safely()
        print(f"[publish] push failed: {((pushed.stderr or pushed.stdout) or '').strip()[-300:]}", flush=True)
        return {"pushed": False, "ahead": ahead, "push_error": True}

    print(f"[publish] auto-resolved {len(churn)} churn conflict(s), pushed", flush=True)
    return {"pushed": True, "ahead": ahead, "auto_resolved": len(churn)}


def _publish_reconcile_after_push_reject(publish_branch: str, ahead: int) -> dict:
    fetched = git("fetch", "origin", publish_branch)
    if fetched.returncode != 0:
        return {"pushed": False, "ahead": ahead, "fetch_error": True}

    merge = git("merge", "--no-edit", f"origin/{publish_branch}")
    if merge.returncode == 0:
        pushed = git("push", "origin", f"HEAD:{publish_branch}")
        if pushed.returncode == 0:
            return {"pushed": True, "ahead": ahead}
        print(f"[publish] push failed: {((pushed.stderr or pushed.stdout) or '').strip()[-300:]}", flush=True)
        return {"pushed": False, "ahead": ahead, "push_error": True}

    print(f"[publish] merge failed: {((merge.stderr or merge.stdout) or '').strip()[-300:]}", flush=True)
    try:
        return _publish_after_merge_conflict(publish_branch, ahead)
    except Exception as exc:
        _abort_merge_safely()
        print(f"[publish] merge handling failed: {str(exc)[-300:]}", flush=True)
        return {"pushed": False, "ahead": ahead, "merge_error": True, "error": str(exc)[-200:]}


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


def dev_sync_lane() -> dict:
    """Reverse sync: merge origin/dev into the bridge feat branch each cycle.

    The bridge couples Window6 math to codon/bio reality; it must work on top of
    the full repo (fibonacci_reality + bio_reality + bedc + lean4) that all
    pipelines roll up into dev, not an isolated old snapshot. Path isolation
    (the bridge owns only tools/window_codon_bridge/* + papers/window_codon_bridge/*)
    makes dev->feat merges conflict-free in practice; any conflict aborts safely
    rather than wedging the daemon. The resulting merge commit is pushed to
    origin/<publish_branch> by the publish lane.
    """
    if git_busy():
        return {"ran": False, "skipped": "git_busy"}
    if _merge_head_present() and not _abort_merge_safely():
        return {"ran": False, "skipped": "stale_merge"}
    base = str(load(SYNC_MANIFEST).get("dev_base_branch") or DEV_BASE_BRANCH)
    fetched = git("fetch", "origin", base)
    if fetched.returncode != 0:
        return {"ran": False, "fetch_error": ((fetched.stderr or fetched.stdout) or "").strip()[-200:]}
    behind = git("rev-list", "--count", f"HEAD..origin/{base}")
    if behind.returncode != 0:
        return {"ran": False, "error": ((behind.stderr or behind.stdout) or "").strip()[-200:]}
    n_behind = int((behind.stdout or "0").strip() or "0")
    if n_behind <= 0:
        return {"ran": True, "behind": 0, "merged": False}
    merge = git("merge", "--no-edit", "--no-ff", f"origin/{base}")
    if merge.returncode != 0:
        conflicted = ((git("diff", "--name-only", "--diff-filter=U").stdout) or "").strip()
        _abort_merge_safely()
        print(f"[dev-sync] merge conflict ({n_behind} behind), aborted: {conflicted[:300]}", flush=True)
        return {"ran": True, "behind": n_behind, "merged": False, "conflict": conflicted.splitlines()[:10]}
    print(f"[dev-sync] merged origin/{base} ({n_behind} commits) into bridge feat", flush=True)
    return {"ran": True, "behind": n_behind, "merged": True}


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
    try:
        return _publish_lane_impl()
    except Exception as exc:
        _abort_merge_safely()
        print(f"[publish] failed: {str(exc)[-300:]}", flush=True)
        return {"pushed": False, "publish_error": True, "error": str(exc)[-200:]}


def _publish_lane_impl() -> dict:
    if git_busy():
        print("[publish] skipped (git busy)", flush=True)
        return {"skipped": "git_busy"}

    if _merge_head_present():
        print("[publish] aborting stale merge state before publish", flush=True)
        if not _abort_merge_safely():
            return {"pushed": False, "merge_error": True, "abort_error": True}

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
        return _publish_reconcile_after_push_reject(publish_branch, ahead)
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


def _write_dev_rollup_state() -> None:
    DEV_ROLLUP_STATE.parent.mkdir(parents=True, exist_ok=True)
    DEV_ROLLUP_STATE.write_text(json.dumps({"last_run_ts": time.time()}), encoding="utf-8")


def dev_rollup_lane() -> dict:
    """Forward rollup: feat->dev via Loning's managed-rollup tools/sync_with_auto_dev.py.

    Mirrors the bio-D lane. The script builds an isolated worktree from origin/dev,
    merges our feat branch in (codex-resolving conflicts, regenerating
    lean4/BEDC.lean), pushes a separate rollup-<head>-to-<base> branch, maintains
    one PR into dev, and auto-merges once green and mergeable -- the bridge's
    research output (claims, ledger, paper) thus reaches the shared dev mainline
    every other pipeline rolls into. Content-delta gated on the three-dot diff: a
    feat that is only commit-count ahead via dev-sync merge commits has no content
    diff, and rolling it up produces an empty-diff PR that triggers no CI, never
    goes green, and blocks the script from rebuilding (deadlock). The reverse
    dev->feat direction is dev_sync_lane.
    """
    if not PIPELINE_CONFIG.exists():
        return {"ran": False, "skipped": "no_config"}
    try:
        cfg = load(PIPELINE_CONFIG).get("dev_rollup") or {}
    except (OSError, json.JSONDecodeError) as exc:
        return {"ran": False, "error": f"config_error: {exc}"}
    if not cfg.get("enabled", False):
        return {"ran": False, "skipped": "disabled"}
    # No global git_busy() guard here: the managed-rollup script operates in its
    # own isolated worktree and acquires the shared git common lock itself, so it
    # is designed to run concurrently with other pipelines. Gating on the global
    # `pgrep -x git` would starve the lane on a busy multi-daemon machine (it
    # never clears), which is why bio-D omits it.
    if _merge_head_present():
        return {"ran": False, "skipped": "merge_in_progress"}
    remote = str(cfg.get("remote") or "origin")
    source = str(cfg.get("head_branch") or "feat/window-codon-bridge")
    target = str(cfg.get("base_branch") or DEV_BASE_BRANCH)
    min_seconds = float(cfg.get("min_seconds_between") or 600)
    try:
        last_ts = float(json.loads(DEV_ROLLUP_STATE.read_text(encoding="utf-8")).get("last_run_ts") or 0.0)
    except (OSError, json.JSONDecodeError, ValueError, TypeError):
        last_ts = 0.0
    if time.time() - last_ts < min_seconds:
        return {"ran": False, "skipped": "throttled"}
    script = REPO_ROOT / "tools" / "sync_with_auto_dev.py"
    if not script.exists():
        return {"ran": False, "error": "sync_script_missing"}
    if subprocess.run(["gh", "--version"], capture_output=True).returncode != 0:
        return {"ran": False, "skipped": "gh_unavailable"}
    git("fetch", remote, source, target)
    delta = git("diff", "--name-only", f"{remote}/{target}...{remote}/{source}")
    if not (delta.stdout or "").strip():
        _write_dev_rollup_state()
        return {"ran": False, "skipped": "no_content_delta"}
    try:
        result = subprocess.run(
            ["python3", str(script), "--source-branch", source, "--target-branch", target],
            cwd=str(REPO_ROOT), capture_output=True, text=True, timeout=1800,
        )
    except subprocess.TimeoutExpired:
        _write_dev_rollup_state()
        return {"ran": True, "error": "sync_timeout"}
    _write_dev_rollup_state()
    out = (result.stdout or "") + (result.stderr or "")
    rollup_lines = [ln for ln in out.splitlines() if "[sync] rollup" in ln]
    tail = (rollup_lines or out.splitlines())[-4:]
    if result.returncode != 0:
        print(f"[dev-rollup] sync failed: {tail}", flush=True)
        return {"ran": True, "error": "sync_failed", "tail": tail}
    merged = any(("merging into" in ln) or ("green and mergeable" in ln) for ln in rollup_lines)
    print(f"[dev-rollup] ran sync feat->dev (merged={merged})", flush=True)
    return {"ran": True, "source": source, "target": target,
            "rollup_branch": f"rollup-{source.replace('/', '-')}-to-{target.replace('/', '-')}",
            "merged": merged, "tail": tail}


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
            dev_sync = dev_sync_lane()
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
            rollup = {} if args.no_commit else dev_rollup_lane()
            print(f"[{summary['ts']}] bridge cycle executed={summary['executed']} verdicts={summary['verdicts']} dev_sync={dev_sync} sync={sync} coverage={coverage} concordance={concordance} oracle={oracle} assimilation={assimilation} derivation={derivation} paper={paper} keep={keep} publish={publish} rollup={rollup}", flush=True)
            if args.once:
                break
            time.sleep(max(1.0, float(args.interval_seconds)))


if __name__ == "__main__":
    main()
