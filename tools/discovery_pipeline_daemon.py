#!/usr/bin/env python3
"""Run the BEDC discovery stages as one ordered daemon."""

from __future__ import annotations

import argparse
import contextlib
import fcntl
import json
import os
import sys
import time
import traceback
from datetime import datetime
from pathlib import Path
from typing import Any, Callable, Iterator

import discovery_adversarial_generator as generator
import discovery_gate_evolver as evolver
import discovery_radar_daemon as radar
import discovery_refutation_publisher as publisher
from structural_dna_build import ensure_structural_dna_build

REPO_ROOT = Path(__file__).resolve().parent.parent
LOG_DIR = REPO_ROOT / "tools" / "logs"
LOG_PATH = LOG_DIR / "discovery_pipeline_daemon.log"
PID_LOCK_PATH = Path("/tmp/.bedc_discovery_pipeline.pid")
DEFAULT_INTERVAL = 21600
INTERVAL_ENV = "DISCOVERY_PIPELINE_INTERVAL_SECONDS"


def now_iso() -> str:
    return datetime.now().isoformat(timespec="seconds")


def append_log(message: str) -> None:
    LOG_DIR.mkdir(parents=True, exist_ok=True)
    with LOG_PATH.open("a", encoding="utf-8") as handle:
        handle.write(f"{now_iso()} {message}\n")


@contextlib.contextmanager
def pid_lock() -> Iterator[None]:
    pid_fd = os.open(PID_LOCK_PATH, os.O_RDWR | os.O_CREAT, 0o644)
    try:
        try:
            fcntl.flock(pid_fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            sys.stderr.write(f"discovery pipeline daemon already running ({PID_LOCK_PATH})\n")
            sys.exit(1)
        os.ftruncate(pid_fd, 0)
        os.write(pid_fd, f"{os.getpid()}\n".encode())
        os.fsync(pid_fd)
        yield
    finally:
        try:
            fcntl.flock(pid_fd, fcntl.LOCK_UN)
        except Exception:
            pass
        os.close(pid_fd)


def interval_seconds(cli_interval: int | None) -> int:
    if cli_interval is not None:
        return max(1, int(cli_interval))
    raw = os.environ.get(INTERVAL_ENV, "")
    if not raw:
        return DEFAULT_INTERVAL
    try:
        return max(1, int(raw))
    except ValueError:
        append_log(f"[discovery-pipeline] invalid {INTERVAL_ENV}={raw!r}; using {DEFAULT_INTERVAL}")
        return DEFAULT_INTERVAL


def jsonl_count(path: str | Path) -> int:
    candidate = Path(path)
    if not candidate.exists():
        return 0
    with candidate.open("r", encoding="utf-8") as handle:
        return sum(1 for line in handle if line.strip())


def stage_ok(result: Any) -> bool:
    if result is None:
        return False
    if isinstance(result, bool):
        return result
    if isinstance(result, int):
        return result == 0
    if isinstance(result, dict):
        return str(result.get("status") or "").lower() not in {"error", "fail-closed"}
    return True


def compact_result(result: Any) -> dict[str, Any]:
    if isinstance(result, dict):
        keys = [
            "status",
            "scanned",
            "fingerprints",
            "candidate_count",
            "refuted",
            "assertion_eligible",
            "conjectured",
            "emitted",
            "bucket_count",
            "skipped_covered",
            "skipped_budget",
            "assertion_target",
            "output",
        ]
        return {key: result[key] for key in keys if key in result}
    if isinstance(result, bool):
        return {"ok": result}
    if isinstance(result, int):
        return {"exit_code": result}
    if result is None:
        return {"result": None}
    return {"result": repr(result)}


@contextlib.contextmanager
def structural_dna_already_checked(failure: str | None) -> Iterator[None]:
    def checked_for_radar() -> str | None:
        return failure

    def checked_for_stage(*_args: Any, **_kwargs: Any) -> str | None:
        return failure

    replacements: list[tuple[object, str, Callable[..., str | None]]] = [
        (radar, "ensure_structural_dna_build", checked_for_radar),
        (publisher, "ensure_structural_dna_build", checked_for_stage),
        (generator, "ensure_structural_dna_build", checked_for_stage),
    ]
    originals = [(module, name, getattr(module, name)) for module, name, _replacement in replacements]
    try:
        for module, name, replacement in replacements:
            setattr(module, name, replacement)
        yield
    finally:
        for module, name, original in originals:
            setattr(module, name, original)


def make_generator_args(args: argparse.Namespace) -> argparse.Namespace:
    stage_args = generator.parser().parse_args([])
    stage_args.output = args.proven_pseudos
    stage_args.classifier_cap = args.generator_classifier_cap
    stage_args.max_new_per_bucket = args.generator_max_new_per_bucket
    stage_args.max_records = args.generator_max_records
    return stage_args


def make_evolver_args(args: argparse.Namespace) -> argparse.Namespace:
    stage_args = evolver.parser().parse_args([])
    stage_args.no_push = bool(args.no_push)
    stage_args.input = args.proven_pseudos
    stage_args.worktree = args.evolver_worktree
    stage_args.base_ref = args.evolver_base_ref
    return stage_args


def run_stage(name: str, func: Callable[[], Any]) -> dict[str, Any]:
    started = time.time()
    append_log(f"[discovery-pipeline] stage={name} start")
    try:
        result = func()
        summary = {
            "stage": name,
            "ok": stage_ok(result),
            "seconds": round(time.time() - started, 3),
            "result": compact_result(result),
        }
        append_log(f"[discovery-pipeline] stage={name} done {json.dumps(summary, sort_keys=True)}")
        print(f"[discovery-pipeline] {name} {json.dumps(summary, ensure_ascii=False, sort_keys=True)}", flush=True)
        return summary
    except Exception as exc:
        summary = {
            "stage": name,
            "ok": False,
            "seconds": round(time.time() - started, 3),
            "error_type": type(exc).__name__,
            "error": str(exc),
        }
        append_log(f"[discovery-pipeline] stage={name} ERROR {type(exc).__name__}: {exc}")
        append_log(traceback.format_exc().rstrip())
        print(f"[discovery-pipeline] {name} {json.dumps(summary, ensure_ascii=False, sort_keys=True)}", flush=True)
        return summary


def run_cycle(args: argparse.Namespace) -> dict[str, Any]:
    cycle_started = now_iso()
    append_log(f"[discovery-pipeline] cycle start no_push={bool(args.no_push)}")
    structural_dna_failure = ensure_structural_dna_build(
        append_log=append_log,
        label="discovery-pipeline",
    )

    proven_before = jsonl_count(args.proven_pseudos)
    with structural_dna_already_checked(structural_dna_failure):
        radar_result: dict[str, Any] = {}

        def run_radar_stage() -> Any:
            result = radar.run_once()
            if isinstance(result, dict):
                radar_result.clear()
                radar_result.update(result)
            return result

        radar_stage = run_stage("radar", run_radar_stage)
        radar_payload = None
        if (
            radar_stage.get("ok")
            and not radar_result.get("degraded")
            and isinstance(radar_result.get("_radar_payload"), dict)
        ):
            radar_payload = radar_result["_radar_payload"]

        stages = [
            radar_stage,
            run_stage("publisher", lambda: publisher.run_once(no_push=bool(args.no_push), radar_payload=radar_payload)),
            run_stage("generator", lambda: generator.run_once(make_generator_args(args))),
        ]
        proven_after_generator = jsonl_count(args.proven_pseudos)
        stages.append(run_stage("evolver", lambda: evolver.run_once(make_evolver_args(args))))

    failed = [stage["stage"] for stage in stages if not stage.get("ok")]
    summary = {
        "cycle_started": cycle_started,
        "ok": structural_dna_failure is None and not failed,
        "structural_dna_ok": structural_dna_failure is None,
        "structural_dna_failure": structural_dna_failure,
        "proven_pseudos": {
            "path": args.proven_pseudos,
            "before": proven_before,
            "after_generator": proven_after_generator,
            "generator_delta": proven_after_generator - proven_before,
            "before_evolver": proven_after_generator,
        },
        "failed_stages": failed,
        "stages": stages,
    }
    append_log(f"[discovery-pipeline] cycle summary {json.dumps(summary, sort_keys=True)}")
    print(f"[discovery-pipeline] summary {json.dumps(summary, ensure_ascii=False, sort_keys=True)}", flush=True)
    return summary


def parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(description="Run the BEDC discovery pipeline daemon.")
    p.add_argument("--once", action="store_true", help="Run one ordered discovery cycle and exit")
    p.add_argument("--no-push", action="store_true", help="Pass no-push mode to publishing stages")
    p.add_argument("--interval", type=int, default=None, help=f"loop sleep seconds; default from {INTERVAL_ENV}")
    p.add_argument("--proven-pseudos", default=str(generator.DEFAULT_OUTPUT), help="JSONL path shared by generator and evolver")
    p.add_argument("--generator-classifier-cap", type=int, default=2000)
    p.add_argument("--generator-max-new-per-bucket", type=int, default=generator.DEFAULT_MAX_NEW_PER_BUCKET)
    p.add_argument("--generator-max-records", type=int, default=generator.DEFAULT_MAX_RECORDS_PER_CYCLE)
    p.add_argument("--evolver-worktree", default=str(evolver.DEFAULT_WORKTREE))
    p.add_argument("--evolver-base-ref", default="origin/" + evolver.BASE_BRANCH)
    return p


def main() -> int:
    args = parser().parse_args()
    with pid_lock():
        if args.once:
            run_cycle(args)
            return 0
        interval = interval_seconds(args.interval)
        append_log(f"[discovery-pipeline] daemon start interval={interval}s no_push={bool(args.no_push)}")
        while True:
            run_cycle(args)
            time.sleep(interval)


if __name__ == "__main__":
    raise SystemExit(main())
