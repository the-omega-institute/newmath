#!/usr/bin/env python3
"""Low-frequency discovery radar daemon.

Runs the full classifier-corpus discovery radar and surfaces the latest
counts as local runtime artifacts only. The daemon never commits, pushes,
or touches pipeline locks owned by other daemons.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
from datetime import datetime
from pathlib import Path
from typing import Any

from structural_dna_build import ensure_structural_dna_build as shared_ensure_structural_dna_build

REPO_ROOT = Path(__file__).resolve().parent.parent
LEAN_ROOT = REPO_ROOT / "lean4"
LOG_DIR = REPO_ROOT / "tools" / "logs"
LEDGER_PATH = LOG_DIR / "discovery_radar_ledger.json"
LOG_PATH = LOG_DIR / "discovery_radar.log"
DEFAULT_INTERVAL = 21600
COMMAND_TIMEOUT = 1200
STRUCTURAL_DNA_BUILD_TIMEOUT = 1200
STRUCTURAL_DNA_EXE = LEAN_ROOT / ".lake" / "build" / "bin" / "structural_dna"


def now_iso() -> str:
    return datetime.now().isoformat(timespec="seconds")


def append_log(message: str) -> None:
    LOG_DIR.mkdir(parents=True, exist_ok=True)
    with LOG_PATH.open("a", encoding="utf-8") as fh:
        fh.write(f"{now_iso()} {message}\n")


def run_bedc_ci(args: list[str]) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        ["python3", "lean4/scripts/bedc_ci.py", *args],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        timeout=COMMAND_TIMEOUT,
    )


def short_process_output(process: subprocess.CompletedProcess[str], limit: int = 1200) -> str:
    combined = ((process.stdout or "") + (process.stderr or "")).strip()
    if len(combined) <= limit:
        return combined
    return combined[-limit:]


def run_lake_build(target: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        ["lake", "build", target],
        cwd=LEAN_ROOT,
        capture_output=True,
        text=True,
        timeout=STRUCTURAL_DNA_BUILD_TIMEOUT,
    )


def structural_dna_probe() -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        ["lake", "env", str(STRUCTURAL_DNA_EXE)],
        cwd=LEAN_ROOT,
        input=json.dumps({"imports": ["BEDC"], "decls": []}),
        capture_output=True,
        text=True,
        timeout=COMMAND_TIMEOUT,
    )


def ensure_structural_dna_build() -> str | None:
    return shared_ensure_structural_dna_build(append_log=append_log, label="radar")


def parse_text_payload(output: str) -> dict[str, Any]:
    match = re.search(
        r"discovery-radar .*?"
        r"scanned=(?P<scanned>\d+).*?"
        r"fingerprints=(?P<fingerprints>\d+).*?"
        r"candidates=(?P<candidates>\d+).*?"
        r"refuted=(?P<refuted>\d+).*?"
        r"assertion_eligible=(?P<eligible>\d+).*?"
        r"conjectured=(?P<conjectured>\d+)",
        output,
        flags=re.S,
    )
    if not match:
        raise RuntimeError("could not parse discovery-radar text output")
    groups = {key: int(value) for key, value in match.groupdict().items()}
    return {
        "classifier_endpoint_count": groups["scanned"],
        "fingerprint_count": groups["fingerprints"],
        "candidate_count": groups["candidates"],
        "refuted_count": groups["refuted"],
        "assertion_eligible_count": groups["eligible"],
        "conjectured_count": groups["conjectured"],
    }


def discovery_radar_payload() -> dict[str, Any]:
    json_run = run_bedc_ci(["discovery-radar", "--json"])
    if json_run.returncode == 0:
        try:
            return json.loads(json_run.stdout)
        except json.JSONDecodeError as exc:
            raise RuntimeError(f"invalid discovery-radar JSON: {exc}") from exc

    combined = (json_run.stdout or "") + (json_run.stderr or "")
    if "--json" not in combined and "unrecognized arguments" not in combined:
        raise RuntimeError(f"discovery-radar --json failed:\n{combined}")

    text_run = run_bedc_ci(["discovery-radar"])
    if text_run.returncode != 0:
        combined_text = (text_run.stdout or "") + (text_run.stderr or "")
        raise RuntimeError(f"discovery-radar text fallback failed:\n{combined_text}")
    return parse_text_payload(text_run.stdout)


def summarize(payload: dict[str, Any]) -> dict[str, Any]:
    return {
        "timestamp": now_iso(),
        "scanned": int(payload.get("classifier_endpoint_count") or payload.get("scanned") or 0),
        "fingerprints": int(payload.get("fingerprint_count") or payload.get("fingerprints") or 0),
        "candidate_count": int(payload.get("candidate_count") or 0),
        "refuted": int(payload.get("refuted_count") or payload.get("refuted") or 0),
        "assertion_eligible": int(
            payload.get("assertion_eligible_count") or payload.get("assertion_eligible") or 0
        ),
        "conjectured": int(payload.get("conjectured_count") or payload.get("conjectured") or 0),
    }


def degraded_reason(summary: dict[str, Any], build_failure: str | None) -> str | None:
    if build_failure is not None:
        return build_failure
    fingerprints = int(summary["fingerprints"])
    if fingerprints > 0:
        return None
    scanned = int(summary["scanned"])
    candidate_counts = (
        int(summary["candidate_count"]),
        int(summary["refuted"]),
        int(summary["assertion_eligible"]),
        int(summary["conjectured"]),
    )
    if scanned > 0:
        return (
            "scanned>0 but fingerprints=0; suspected structural_dna executable unavailable, "
            "not built, or request failed"
        )
    if all(count == 0 for count in candidate_counts):
        return (
            "candidate counts are all zero with fingerprints=0; suspected structural_dna executable "
            "unavailable, not built, or request failed"
        )
    return None


def mark_degraded(summary: dict[str, Any], reason: str | None) -> dict[str, Any]:
    if reason is None:
        summary["degraded"] = False
        return summary
    summary["degraded"] = True
    summary["degraded_reason"] = reason
    append_log(
        f"[radar] [WARNING] degraded: {reason}"
        f" scanned={summary['scanned']}"
        f" fingerprints={summary['fingerprints']}"
        f" candidates={summary['candidate_count']}"
        f" refuted={summary['refuted']}"
    )
    return summary


def load_previous_counts() -> dict[str, int] | None:
    try:
        previous = json.loads(LEDGER_PATH.read_text(encoding="utf-8"))
    except FileNotFoundError:
        return None
    except Exception:
        return None
    keys = ("scanned", "fingerprints", "candidate_count", "refuted", "assertion_eligible", "conjectured")
    try:
        return {key: int(previous.get(key) or 0) for key in keys}
    except Exception:
        return None


def write_ledger(summary: dict[str, Any]) -> None:
    LOG_DIR.mkdir(parents=True, exist_ok=True)
    tmp = LEDGER_PATH.with_suffix(".json.tmp")
    tmp.write_text(json.dumps(summary, indent=2, ensure_ascii=False, sort_keys=True) + "\n", encoding="utf-8")
    tmp.replace(LEDGER_PATH)


def log_summary(summary: dict[str, Any], previous_counts: dict[str, int] | None) -> None:
    keys = ("scanned", "fingerprints", "candidate_count", "refuted", "assertion_eligible", "conjectured")
    current_counts = {key: int(summary[key]) for key in keys}
    changed = previous_counts is None or current_counts != previous_counts
    prefix = "DEGRADED" if summary.get("degraded") else ("CHANGED" if changed else "heartbeat")
    append_log(
        f"[radar] {prefix}"
        f" scanned={summary['scanned']}"
        f" fingerprints={summary['fingerprints']}"
        f" candidates={summary['candidate_count']}"
        f" refuted={summary['refuted']}"
        f" eligible={summary['assertion_eligible']}"
        f" conjectured={summary['conjectured']}"
    )


def run_once() -> dict[str, Any] | None:
    try:
        previous_counts = load_previous_counts()
        build_failure = ensure_structural_dna_build()
        payload: dict[str, Any] = {}
        try:
            payload = discovery_radar_payload()
        except Exception:
            if build_failure is None:
                raise
        summary = summarize(payload)
        summary = mark_degraded(summary, degraded_reason(summary, build_failure))
        write_ledger(summary)
        log_summary(summary, previous_counts)
        if sys.stdout.isatty():
            print(
                "[discovery-radar-daemon]"
                f" scanned={summary['scanned']}"
                f" fingerprints={summary['fingerprints']}"
                f" refuted={summary['refuted']}"
                f" eligible={summary['assertion_eligible']}"
                f" conjectured={summary['conjectured']}",
                flush=True,
            )
        summary["_radar_payload"] = payload
        return summary
    except Exception as exc:
        append_log(f"[radar] ERROR {type(exc).__name__}: {exc}")
        return None


def interval_seconds() -> int:
    raw = os.environ.get("DISCOVERY_RADAR_INTERVAL_SECONDS", "")
    if not raw:
        return DEFAULT_INTERVAL
    try:
        value = int(raw)
    except ValueError:
        append_log(f"[radar] invalid DISCOVERY_RADAR_INTERVAL_SECONDS={raw!r}; using {DEFAULT_INTERVAL}")
        return DEFAULT_INTERVAL
    return max(value, 1)


def main() -> int:
    parser = argparse.ArgumentParser(description="Run the BEDC discovery radar daemon.")
    parser.add_argument("--once", action="store_true", help="Run one full discovery-radar cycle and exit")
    args = parser.parse_args()

    if args.once:
        run_once()
        return 0
    sys.stderr.write("discovery radar daemon loop moved to tools/discovery_pipeline_daemon.py; use --once for debugging\n")
    return 2


if __name__ == "__main__":
    raise SystemExit(main())
