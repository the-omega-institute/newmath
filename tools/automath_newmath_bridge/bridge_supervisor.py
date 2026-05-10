#!/usr/bin/env python3
"""Periodic supervisor for the Automath-NewMath bridge.

The supervisor mirrors the local distillation/oracle pipeline style:

- require the expected branch;
- honor a stop file;
- fetch the latest refs for both repos;
- optionally merge the NewMath bridge branch with origin/auto-dev;
- run the bridge discovery pipeline;
- run deterministic gates;
- optionally hand gate-passed Automath-to-NewMath candidates to BEDC
  `board_spawn`;
- optionally merge the gated bridge branch back to the configured BEDC branch
  when explicitly requested;
- optionally write local review packets;
- keep runtime artifacts local-only and ignored by Git.

It never pushes, sends, publishes, submits, or directly edits paper/Lean files.
BEDC paper/Lean writes remain owned by the BEDC board/supervisor pipeline.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
import time
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

try:
    from bridge_gates import gate_records, read_jsonl, write_jsonl
except ModuleNotFoundError:  # pragma: no cover
    from tools.automath_newmath_bridge.bridge_gates import gate_records, read_jsonl, write_jsonl


SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parent.parent
DEFAULT_CONFIG = SCRIPT_DIR / "bridge_pipeline_config.json"
STOP_FILE = SCRIPT_DIR / ".bridge_supervisor.stop"
LOG_DIR = SCRIPT_DIR / "logs"
PACKET_DIR = SCRIPT_DIR / "inbox" / "writeback_packets"


def _now_iso() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).strftime("%Y-%m-%dT%H:%M:%SZ")


def _log(message: str) -> None:
    LOG_DIR.mkdir(parents=True, exist_ok=True)
    line = f"[{_now_iso()}] {message}"
    print(line, flush=True)
    with (LOG_DIR / "bridge_supervisor.log").open("a", encoding="utf-8") as handle:
        handle.write(line + "\n")


def _git(repo: Path, args: list[str], *, timeout: int = 180) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        ["git", *args],
        cwd=str(repo),
        capture_output=True,
        text=True,
        timeout=timeout,
        check=False,
    )


def _git_stdout(repo: Path, args: list[str], *, timeout: int = 120) -> str:
    result = _git(repo, args, timeout=timeout)
    if result.returncode != 0:
        raise RuntimeError((result.stderr or result.stdout or "git command failed").strip())
    return result.stdout.strip()


def _git_quiet(repo: Path, args: list[str], *, timeout: int = 120) -> None:
    _git(repo, args, timeout=timeout)


def current_branch(repo: Path) -> str:
    return _git_stdout(repo, ["branch", "--show-current"], timeout=30)


def ensure_branch(expected: str, *, allow_current_branch: bool = False) -> None:
    branch = current_branch(REPO_ROOT)
    if branch != expected:
        if allow_current_branch:
            _log(f"branch guard bypassed for local audit branch {branch!r}; configured production branch is {expected!r}")
            return
        raise RuntimeError(
            f"Refusing to run on branch {branch!r}; expected {expected!r}. "
            "The bridge supervisor never checks out dev or outreach branches."
        )


def expected_branch_from_config(config_path: Path, fallback: str) -> str:
    try:
        config = _load_config(config_path)
    except Exception:
        return fallback
    return str(config.get("required_branch") or fallback)


def tracked_dirty_lines(repo: Path) -> list[str]:
    output = _git_stdout(repo, ["status", "--porcelain", "--untracked-files=no"], timeout=30)
    return [line for line in output.splitlines() if line.strip()]


def worktree_dirty_lines(repo: Path) -> list[str]:
    output = _git_stdout(repo, ["status", "--porcelain"], timeout=30)
    return [line for line in output.splitlines() if line.strip() and not line.startswith("!!")]


def _load_config(path: Path) -> dict[str, Any]:
    data = json.loads(path.read_text(encoding="utf-8-sig"))
    if not isinstance(data, dict):
        raise ValueError(f"Expected object JSON in {path}")
    return data


def _resolve_repo_path(raw: str, config_path: Path) -> Path:
    path = Path(raw)
    if not path.is_absolute():
        path = (config_path.parent / path).resolve()
        if not (path / ".git").exists():
            path = (REPO_ROOT / raw).resolve()
    return path


def fetch_repo(repo_key: str, repo_cfg: dict[str, Any], config_path: Path) -> dict[str, Any]:
    repo_path = _resolve_repo_path(str(repo_cfg.get("local_path", "")), config_path)
    before = _git_stdout(repo_path, ["rev-parse", str(repo_cfg.get("default_ref") or "HEAD")], timeout=30)
    result = _git(repo_path, ["fetch", "origin"], timeout=300)
    if result.returncode != 0:
        return {
            "repo_key": repo_key,
            "status": "fetch_failed",
            "reason": (result.stderr or result.stdout).strip(),
        }
    after = _git_stdout(repo_path, ["rev-parse", str(repo_cfg.get("default_ref") or "HEAD")], timeout=30)
    return {
        "repo_key": repo_key,
        "status": "fetched",
        "repo": repo_cfg.get("repo"),
        "default_ref": repo_cfg.get("default_ref"),
        "before": before,
        "after": after,
        "changed": before != after,
    }


def fetch_repositories(config_path: Path) -> list[dict[str, Any]]:
    config = _load_config(config_path)
    repos = config.get("repositories")
    if not isinstance(repos, dict):
        raise ValueError("config.repositories must be an object")
    results = []
    for repo_key, repo_cfg in repos.items():
        if isinstance(repo_cfg, dict):
            results.append(fetch_repo(str(repo_key), repo_cfg, config_path))
    return results


def sync_bridge_from_auto_dev(config: dict[str, Any], *, allow_current_branch: bool = False) -> dict[str, Any]:
    """Merge origin/auto-dev into this bridge branch before scanning.

    This mirrors the NewMath BEDC supervisor habit of syncing from the
    integration branch before generating new work. It never pushes. Conflicts
    are surfaced as a hard stop so gates do not run on a half-merged worktree.
    """
    cfg = config.get("sync_from_auto_dev")
    if not isinstance(cfg, dict) or not cfg.get("enabled", False):
        return {"status": "disabled"}

    source_ref = str(cfg.get("source_ref") or "origin/auto-dev")
    before = _git_stdout(REPO_ROOT, ["rev-parse", "HEAD"], timeout=30)
    current_branch_name = current_branch(REPO_ROOT)
    expected = str(config.get("required_branch") or current_branch_name)
    if current_branch_name != expected:
        if allow_current_branch:
            _log(
                f"sync_from_auto_dev branch guard bypassed for local audit branch {current_branch_name!r}; "
                f"configured production branch is {expected!r}"
            )
        else:
            raise RuntimeError(f"sync_from_auto_dev expected branch {expected!r}, got {current_branch_name!r}")

    merge_base = _git_stdout(REPO_ROOT, ["merge-base", "HEAD", source_ref], timeout=30)
    source_commit = _git_stdout(REPO_ROOT, ["rev-parse", source_ref], timeout=30)
    if before == source_commit or merge_base == source_commit:
        return {
            "status": "up_to_date",
            "source_ref": source_ref,
            "before": before,
            "after": before,
        }

    merge_args = [str(item) for item in cfg.get("merge_args", ["--no-edit"]) if isinstance(item, str)]
    result = _git(REPO_ROOT, ["merge", *merge_args, source_ref], timeout=1200)
    if result.returncode != 0:
        raise RuntimeError(
            "sync_from_auto_dev merge failed; resolve conflicts manually before rerunning. "
            + (result.stderr or result.stdout).strip()
        )
    after = _git_stdout(REPO_ROOT, ["rev-parse", "HEAD"], timeout=30)
    return {
        "status": "merged",
        "source_ref": source_ref,
        "before": before,
        "after": after,
        "stdout": result.stdout.strip()[:500],
    }


def run_command(args: list[str], *, timeout: int = 600) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        args,
        cwd=str(REPO_ROOT),
        capture_output=True,
        text=True,
        timeout=timeout,
        check=False,
    )


def run_pipeline(
    config_path: Path,
    *,
    include_unchanged: bool,
    update_state: bool,
    limit_per_rule: int,
    scan_limit_per_rule: int,
    no_synthesis: bool,
) -> None:
    config = _load_config(config_path)
    queue_path = REPO_ROOT / str(config.get("agent_queue_path") or "tools/automath_newmath_bridge/out/bridge_agent_queue.jsonl")
    event_log_path = REPO_ROOT / str(config.get("event_log_path") or "tools/automath_newmath_bridge/state/bridge_events.jsonl")
    cmd = [
        sys.executable,
        str(SCRIPT_DIR / "run_bridge_pipeline.py"),
        "--config",
        str(config_path),
        "--limit-per-rule",
        str(limit_per_rule),
        "--queue",
        str(queue_path),
        "--event-log",
        str(event_log_path),
    ]
    if include_unchanged:
        cmd.append("--include-unchanged")
    if update_state:
        cmd.append("--update-state")
    if no_synthesis:
        cmd.append("--no-synthesis")
    if scan_limit_per_rule > 0:
        cmd.extend(["--scan-limit-per-rule", str(scan_limit_per_rule)])
    result = run_command(cmd)
    if result.stdout.strip():
        _log(result.stdout.strip())
    if result.returncode != 0:
        raise RuntimeError((result.stderr or result.stdout or "bridge pipeline failed").strip())


def run_synthesis_report(config_path: Path) -> None:
    config = _load_config(config_path)
    inbox = REPO_ROOT / str(config.get("inbox_path"))
    output = SCRIPT_DIR / "out" / "bridge_synthesis.jsonl"
    report = REPO_ROOT / str(config.get("synthesis_report_path") or "tools/automath_newmath_bridge/out/bridge_synthesis_report.md")
    cmd = [
        sys.executable,
        str(SCRIPT_DIR / "bridge_synthesis.py"),
        "--config",
        str(config_path),
        "--input",
        str(inbox),
        "--output",
        str(output),
        "--report",
        str(report),
    ]
    result = run_command(cmd)
    if result.stdout.strip():
        _log(result.stdout.strip())
    if result.returncode != 0:
        raise RuntimeError((result.stderr or result.stdout or "bridge synthesis failed").strip())


def run_gates(config_path: Path, *, allow_publication_risk: bool) -> list[dict[str, Any]]:
    config = _load_config(config_path)
    inbox = REPO_ROOT / str(config.get("inbox_path"))
    bedc_cfg = config.get("bedc_board_ingest")
    gate_results_path = ""
    if isinstance(bedc_cfg, dict):
        gate_results_path = str(bedc_cfg.get("gate_results_path") or "")
    output = REPO_ROOT / (gate_results_path or "tools/automath_newmath_bridge/out/bridge_gate_results.jsonl")
    records = read_jsonl(inbox)
    results = gate_records(records, allow_publication_risk=allow_publication_risk)
    write_jsonl(output, results)
    passed = sum(1 for item in results if item.get("gate_status") == "gate_passed")
    blocked = len(results) - passed
    _log(f"gates: passed={passed} blocked={blocked} output={output}")
    return results


def ingest_to_bedc_board(config: dict[str, Any], *, apply: bool) -> dict[str, Any]:
    cfg = config.get("bedc_board_ingest")
    if not isinstance(cfg, dict) or not cfg.get("enabled", False):
        return {"status": "disabled"}

    cmd = [
        sys.executable,
        str(SCRIPT_DIR / "bridge_to_bedc_board.py"),
        "--gate-results",
        str(REPO_ROOT / str(cfg.get("gate_results_path") or "tools/automath_newmath_bridge/out/bridge_gate_results.jsonl")),
        "--packet-dir",
        str(REPO_ROOT / str(cfg.get("review_packet_dir") or "tools/automath_newmath_bridge/review_packets")),
        "--limit",
        str(int(cfg.get("max_candidates_per_pass") or 3)),
        "--fit-threshold",
        str(int(cfg.get("fit_threshold") or 7)),
        "--novelty-threshold",
        str(int(cfg.get("novelty_threshold") or 6)),
    ]
    if apply:
        cmd.append("--apply")
    result = run_command(cmd, timeout=900 if apply else 120)
    payload = result.stdout.strip()
    if result.returncode != 0:
        return {
            "status": "failed",
            "apply": apply,
            "reason": (result.stderr or result.stdout).strip()[:1000],
        }
    try:
        data = json.loads(payload) if payload else {}
    except json.JSONDecodeError:
        data = {"raw": payload[:1000]}
    return {
        "status": "applied" if apply else "dry_run",
        "apply": apply,
        **data,
    }


def merge_back_to_bedc(config: dict[str, Any], gate_results: list[dict[str, Any]], config_path: Path) -> dict[str, Any]:
    """Merge the gated bridge branch back to the configured BEDC branch.

    This is local-only and conservative. It only runs after all bridge gates
    pass, the target worktree is on the expected branch, and the target worktree
    has no tracked or untracked changes. Runtime artifacts remain ignored and
    are not pushed.
    """
    cfg = config.get("merge_back_after_gates")
    if not isinstance(cfg, dict) or not cfg.get("enabled", False):
        return {"status": "disabled"}
    if any(item.get("gate_status") != "gate_passed" for item in gate_results):
        return {"status": "skipped_gate_blocked"}

    target_raw = str(cfg.get("target_worktree") or "")
    if not target_raw:
        raise RuntimeError("merge_back_after_gates.target_worktree is required")
    target = _resolve_repo_path(target_raw, config_path)
    target_branch = str(cfg.get("target_branch") or "bedc-claim-packet-pipeline")
    source_ref = str(cfg.get("source_ref") or current_branch(REPO_ROOT))

    actual_branch = current_branch(target)
    if actual_branch != target_branch:
        return {
            "status": "skipped_wrong_branch",
            "target_worktree": str(target),
            "expected_branch": target_branch,
            "actual_branch": actual_branch,
        }
    dirty = worktree_dirty_lines(target)
    if dirty:
        return {
            "status": "skipped_dirty_target",
            "target_worktree": str(target),
            "dirty_count": len(dirty),
            "sample": dirty[:10],
        }

    before = _git_stdout(target, ["rev-parse", "HEAD"], timeout=30)
    source_commit = _git_stdout(REPO_ROOT, ["rev-parse", source_ref], timeout=30)
    result = _git(target, ["merge", "--no-edit", source_commit], timeout=1200)
    if result.returncode != 0:
        _git_quiet(target, ["merge", "--abort"], timeout=120)
        return {
            "status": "merge_failed",
            "target_worktree": str(target),
            "source_ref": source_ref,
            "source_commit": source_commit,
            "reason": (result.stderr or result.stdout).strip()[:1000],
        }
    after = _git_stdout(target, ["rev-parse", "HEAD"], timeout=30)
    return {
        "status": "merged" if before != after else "up_to_date",
        "target_worktree": str(target),
        "target_branch": target_branch,
        "source_ref": source_ref,
        "source_commit": source_commit,
        "before": before,
        "after": after,
        "pushed": False,
    }


def _packet_name(result: dict[str, Any]) -> str:
    raw = str(result.get("id") or result.get("artifact_key") or result.get("source_path") or "packet")
    safe = "".join(ch if ch.isalnum() or ch in "._-" else "_" for ch in raw)
    return safe[:180] + ".json"


def write_local_packets(gate_results: list[dict[str, Any]], *, limit: int) -> list[Path]:
    PACKET_DIR.mkdir(parents=True, exist_ok=True)
    written: list[Path] = []
    for result in gate_results:
        if len(written) >= limit:
            break
        if result.get("gate_status") != "gate_passed":
            continue
        if not result.get("packet_write_allowed"):
            continue
        packet = {
            "schema_version": "automath-newmath-bridge-writeback-packet-v1",
            "created_at": _now_iso(),
            "status": "needs_operator_review",
            "durable_write_allowed": False,
            "reason": "Local bridge packet generated after deterministic gates. Durable writes require accepted/consumed manifest entry.",
            "gate_result": result,
            "non_actions": [
                "no push",
                "no publication",
                "no external send",
                "no paper write",
                "no Lean write",
                "no automatic acceptance",
            ],
        }
        path = PACKET_DIR / _packet_name(result)
        path.write_text(json.dumps(packet, ensure_ascii=False, indent=2, sort_keys=True) + "\n", encoding="utf-8")
        written.append(path)
    return written


def supervisor_pass(args: argparse.Namespace) -> bool:
    config_path = Path(args.config).resolve()
    config = _load_config(config_path)
    ensure_branch(expected_branch_from_config(config_path, args.branch), allow_current_branch=args.allow_current_branch)
    if tracked_dirty_lines(REPO_ROOT) and not args.allow_dirty:
        raise RuntimeError("Tracked worktree changes present; pass --allow-dirty only for local runtime/debug work")

    if not args.no_fetch:
        fetch_results = fetch_repositories(config_path)
        for item in fetch_results:
            _log(f"fetch: {item}")
        if any(item.get("status") == "fetch_failed" for item in fetch_results):
            return False

    if not args.no_auto_dev_sync:
        sync_result = sync_bridge_from_auto_dev(config, allow_current_branch=args.allow_current_branch)
        _log(f"sync_from_auto_dev: {sync_result}")

    run_pipeline(
        config_path,
        include_unchanged=args.include_unchanged,
        update_state=args.update_state,
        limit_per_rule=args.limit_per_rule,
        scan_limit_per_rule=args.scan_limit_per_rule,
        no_synthesis=args.no_synthesis,
    )
    if args.no_synthesis:
        _log("bridge_synthesis: skipped by --no-synthesis")
    else:
        run_synthesis_report(config_path)
    gate_results = run_gates(config_path, allow_publication_risk=args.allow_publication_risk)

    board_apply = bool(args.apply_bedc_board_ingest or config.get("bedc_board_ingest", {}).get("apply_by_default", False))
    if not args.no_bedc_board_ingest:
        board_result = ingest_to_bedc_board(config, apply=board_apply)
        _log(f"bedc_board_ingest: {board_result}")
    else:
        _log("bedc_board_ingest: disabled by --no-bedc-board-ingest")

    merge_config = dict(config)
    if args.merge_back_after_gates:
        merge_cfg = dict(config.get("merge_back_after_gates") or {})
        merge_cfg["enabled"] = True
        merge_config["merge_back_after_gates"] = merge_cfg

    if not args.no_merge_back_after_gates:
        merge_back = merge_back_to_bedc(merge_config, gate_results, config_path)
        _log(f"merge_back_after_gates: {merge_back}")
    else:
        _log("merge_back_after_gates: disabled by --no-merge-back-after-gates")

    if args.apply_writeback_packets:
        written = write_local_packets(gate_results, limit=args.packet_limit)
        _log(f"local writeback packets: wrote={len(written)} dir={PACKET_DIR}")
    else:
        _log("local writeback packets: disabled; pass --apply-writeback-packets to write ignored review packets")
    return True


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Automath-NewMath bridge supervisor")
    parser.add_argument("--branch", default="bridge/newmath-automath-consumption", help="Required current branch fallback; config.required_branch wins")
    parser.add_argument("--config", default=str(DEFAULT_CONFIG), help="bridge pipeline config JSON")
    parser.add_argument("--once", action="store_true", help="Run one pass")
    parser.add_argument("--poll-interval", type=int, default=300, help="Seconds between passes")
    parser.add_argument("--no-fetch", action="store_true", help="Do not fetch origin for configured repos")
    parser.add_argument("--no-auto-dev-sync", action="store_true", help="Do not merge origin/auto-dev into the bridge branch before scanning")
    parser.add_argument("--include-unchanged", action="store_true", help="Emit already-seen artifacts")
    parser.add_argument("--update-state", action="store_true", help="Persist seen artifacts to ignored local state")
    parser.add_argument("--allow-dirty", action="store_true", help="Allow tracked dirty worktree before running")
    parser.add_argument(
        "--allow-current-branch",
        action="store_true",
        help="Allow running on the current local audit branch instead of the configured production bridge branch",
    )
    parser.add_argument("--allow-publication-risk", action="store_true", help="Suppress publication-risk gate warnings")
    parser.add_argument("--limit-per-rule", type=int, default=50)
    parser.add_argument("--scan-limit-per-rule", type=int, default=0, help="Limit matched path scans per discovery rule for fast local harness checks")
    parser.add_argument("--no-synthesis", action="store_true", help="Skip cross-repo readiness synthesis for a fast local harness check")
    parser.add_argument(
        "--apply-bedc-board-ingest",
        action="store_true",
        help="Run BEDC board_spawn for eligible Automath-to-NewMath bridge candidates",
    )
    parser.add_argument(
        "--no-bedc-board-ingest",
        action="store_true",
        help="Skip the NewMath-side BEDC BOARD bridge adapter",
    )
    parser.add_argument(
        "--apply-writeback-packets",
        action="store_true",
        help="Write local ignored review packets for gate-passed candidates",
    )
    parser.add_argument("--packet-limit", type=int, default=25)
    parser.add_argument(
        "--no-merge-back-after-gates",
        action="store_true",
        help="Do not merge this bridge branch into the configured local BEDC branch after gates pass",
    )
    parser.add_argument(
        "--merge-back-after-gates",
        action="store_true",
        help="Opt in to merging this bridge branch into the configured local BEDC branch after gates pass",
    )
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    while True:
        try:
            ok = supervisor_pass(args)
        except Exception as exc:
            _log(f"supervisor pass failed: {exc}")
            ok = False
        if args.once or STOP_FILE.exists():
            return 0 if ok else 1
        time.sleep(max(30, args.poll_interval))


if __name__ == "__main__":
    raise SystemExit(main())
