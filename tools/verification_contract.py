#!/usr/bin/env python3

from __future__ import annotations

import argparse
import json
import subprocess
import sys
import time
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Iterable


REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_LEDGER = REPO_ROOT / ".refactor-loop" / "verification-ledger.jsonl"
STATUSES = {"passed", "failed", "deferred"}


@dataclass(frozen=True)
class VerificationGate:
    name: str
    owner: str
    command: str
    worker_premerge: str
    ship: str


@dataclass(frozen=True)
class VerificationEnvelope:
    schema: int
    sha: str
    gate: str
    mode: str
    status: str
    owner: str
    command: str
    started_at: str
    finished_at: str
    elapsed_s: float | None
    artifact: str
    detail: str


GATES: dict[str, VerificationGate] = {
    "paper-precheck": VerificationGate(
        name="paper-precheck",
        owner="worker-premerge",
        command="cd papers/bedc && make precheck",
        worker_premerge="required",
        ship="required",
    ),
    "paper-full-make": VerificationGate(
        name="paper-full-make",
        owner="paper_builder_daemon",
        command="cd papers/bedc && make",
        worker_premerge="deferred",
        ship="required",
    ),
    "lean-full-build": VerificationGate(
        name="lean-full-build",
        owner="lean_builder",
        command="cd lean4 && lake build",
        worker_premerge="deferred",
        ship="required",
    ),
    "axiom-audit": VerificationGate(
        name="axiom-audit",
        owner="worker-premerge",
        command="python3 tools/check-axioms.py",
        worker_premerge="required",
        ship="required",
    ),
    "paper-lean-audit": VerificationGate(
        name="paper-lean-audit",
        owner="worker-premerge",
        command="python3 lean4/scripts/bedc_ci.py audit",
        worker_premerge="required",
        ship="required",
    ),
    "axiom-purity": VerificationGate(
        name="axiom-purity",
        owner="ship",
        command="python3 lean4/scripts/bedc_ci.py axiom-purity --strict",
        worker_premerge="deferred",
        ship="required",
    ),
}

MODES: dict[str, tuple[str, ...]] = {
    "dev": ("paper-precheck", "paper-lean-audit"),
    "worker-premerge": (
        "paper-precheck",
        "paper-full-make",
        "lean-full-build",
        "axiom-audit",
        "paper-lean-audit",
        "axiom-purity",
    ),
    "async-builder": ("paper-full-make", "lean-full-build"),
    "ship": (
        "paper-precheck",
        "paper-full-make",
        "lean-full-build",
        "axiom-audit",
        "paper-lean-audit",
        "axiom-purity",
    ),
}


def utc_now() -> str:
    return time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())


def current_sha(cwd: Path | None = None) -> str:
    result = subprocess.run(
        ["git", "rev-parse", "HEAD"],
        cwd=str(cwd or REPO_ROOT),
        capture_output=True,
        text=True,
        check=True,
    )
    return result.stdout.strip()


def mode_plan(mode: str) -> list[dict[str, str]]:
    if mode not in MODES:
        raise ValueError(f"unknown mode: {mode}")
    rows: list[dict[str, str]] = []
    for gate_name in MODES[mode]:
        gate = GATES[gate_name]
        rows.append(
            {
                "gate": gate.name,
                "owner": gate.owner,
                "command": gate.command,
                "disposition": getattr(gate, mode.replace("-", "_"), "required"),
            }
        )
    return rows


def validate_envelope(
    *,
    sha: str,
    gate: str,
    status: str,
    mode: str,
) -> None:
    if not sha or not all(c in "0123456789abcdefABCDEF" for c in sha):
        raise ValueError("sha must be a hexadecimal git object name")
    if gate not in GATES:
        raise ValueError(f"unknown gate: {gate}")
    if status not in STATUSES:
        raise ValueError(f"unknown status: {status}")
    if mode not in MODES:
        raise ValueError(f"unknown mode: {mode}")


def make_envelope(
    *,
    sha: str,
    gate: str,
    status: str,
    mode: str,
    owner: str | None = None,
    detail: str = "",
    started_at: str | None = None,
    finished_at: str | None = None,
    elapsed_s: float | None = None,
    artifact: str = "",
) -> VerificationEnvelope:
    validate_envelope(sha=sha, gate=gate, status=status, mode=mode)
    gate_def = GATES[gate]
    return VerificationEnvelope(
        schema=1,
        sha=sha,
        gate=gate,
        mode=mode,
        status=status,
        owner=owner or gate_def.owner,
        command=gate_def.command,
        started_at=started_at or utc_now(),
        finished_at=finished_at or utc_now(),
        elapsed_s=elapsed_s,
        artifact=artifact,
        detail=detail,
    )


def append_envelope(
    envelope: VerificationEnvelope,
    *,
    ledger_path: Path = DEFAULT_LEDGER,
) -> VerificationEnvelope:
    ledger_path.parent.mkdir(parents=True, exist_ok=True)
    with ledger_path.open("a", encoding="utf-8") as f:
        f.write(json.dumps(asdict(envelope), sort_keys=True) + "\n")
    return envelope


def record(
    *,
    sha: str,
    gate: str,
    status: str,
    mode: str,
    owner: str | None = None,
    detail: str = "",
    started_at: str | None = None,
    finished_at: str | None = None,
    elapsed_s: float | None = None,
    artifact: str = "",
    ledger_path: Path = DEFAULT_LEDGER,
) -> VerificationEnvelope:
    envelope = make_envelope(
        sha=sha,
        gate=gate,
        status=status,
        mode=mode,
        owner=owner,
        detail=detail,
        started_at=started_at,
        finished_at=finished_at,
        elapsed_s=elapsed_s,
        artifact=artifact,
    )
    return append_envelope(envelope, ledger_path=ledger_path)


def read_ledger(ledger_path: Path = DEFAULT_LEDGER) -> list[dict]:
    if not ledger_path.exists():
        return []
    rows: list[dict] = []
    for line in ledger_path.read_text(encoding="utf-8").splitlines():
        if not line.strip():
            continue
        try:
            item = json.loads(line)
        except json.JSONDecodeError:
            continue
        if isinstance(item, dict) and item.get("schema") == 1:
            rows.append(item)
    return rows


def latest_by_gate(rows: Iterable[dict], sha: str) -> dict[str, dict]:
    latest: dict[str, dict] = {}
    for row in rows:
        if row.get("sha") != sha:
            continue
        gate = row.get("gate")
        if isinstance(gate, str):
            latest[gate] = row
    return latest


def status_for(
    *,
    sha: str,
    mode: str,
    ledger_path: Path = DEFAULT_LEDGER,
) -> dict:
    if mode not in MODES:
        raise ValueError(f"unknown mode: {mode}")
    latest = latest_by_gate(read_ledger(ledger_path), sha)
    gate_rows = []
    overall = "passed"
    for gate_name in MODES[mode]:
        gate = GATES[gate_name]
        disposition = getattr(gate, mode.replace("-", "_"), "required")
        envelope = latest.get(gate_name)
        status = envelope.get("status") if envelope else None
        if status is None:
            status = "deferred" if disposition == "deferred" else "missing"
        if status == "failed":
            overall = "failed"
        elif status in {"missing", "deferred"} and overall != "failed":
            overall = "deferred"
        gate_rows.append(
            {
                "gate": gate_name,
                "owner": gate.owner,
                "command": gate.command,
                "disposition": disposition,
                "status": status,
                "envelope": envelope,
            }
        )
    return {"sha": sha, "mode": mode, "overall": overall, "gates": gate_rows}


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser()
    parser.add_argument("--ledger", default=str(DEFAULT_LEDGER))
    sub = parser.add_subparsers(dest="command_name", required=True)

    modes = sub.add_parser("modes")
    modes.add_argument("--json", action="store_true")

    plan = sub.add_parser("plan")
    plan.add_argument("mode", choices=sorted(MODES))
    plan.add_argument("--json", action="store_true")

    command = sub.add_parser("command")
    command.add_argument("gate", choices=sorted(GATES))

    record_parser = sub.add_parser("record")
    record_parser.add_argument("--sha", required=True)
    record_parser.add_argument("--gate", required=True, choices=sorted(GATES))
    record_parser.add_argument("--status", required=True, choices=sorted(STATUSES))
    record_parser.add_argument("--mode", required=True, choices=sorted(MODES))
    record_parser.add_argument("--owner")
    record_parser.add_argument("--detail", default="")
    record_parser.add_argument("--artifact", default="")
    record_parser.add_argument("--elapsed-s", type=float)
    record_parser.add_argument("--json", action="store_true")

    status = sub.add_parser("status")
    status.add_argument("--sha", required=True)
    status.add_argument("--mode", required=True, choices=sorted(MODES))
    status.add_argument("--json", action="store_true")
    return parser


def main(argv: list[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    ledger_path = Path(args.ledger)

    if args.command_name == "modes":
        data = sorted(MODES)
        print(json.dumps(data, indent=2) if args.json else "\n".join(data))
        return 0
    if args.command_name == "plan":
        data = mode_plan(args.mode)
        print(json.dumps(data, indent=2) if args.json else "\n".join(row["gate"] for row in data))
        return 0
    if args.command_name == "command":
        print(GATES[args.gate].command)
        return 0
    if args.command_name == "record":
        envelope = record(
            sha=args.sha,
            gate=args.gate,
            status=args.status,
            mode=args.mode,
            owner=args.owner,
            detail=args.detail,
            elapsed_s=args.elapsed_s,
            artifact=args.artifact,
            ledger_path=ledger_path,
        )
        if args.json:
            print(json.dumps(asdict(envelope), indent=2, sort_keys=True))
        return 0
    if args.command_name == "status":
        data = status_for(sha=args.sha, mode=args.mode, ledger_path=ledger_path)
        print(json.dumps(data, indent=2, sort_keys=True) if args.json else data["overall"])
        return 0
    parser.error("unreachable")
    return 2


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except ValueError as exc:
        sys.stderr.write(f"{exc}\n")
        raise SystemExit(2)
