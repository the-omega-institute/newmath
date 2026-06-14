#!/usr/bin/env python3
"""Adversarial-verification gate for the LeWM autoresearch loop.

The mechanical gates (determinism / anchor / criterion / overclaim / provenance)
are necessary but not sufficient: they certified a label-leakage artifact as
authoritative. This stage makes the FI-001 discipline structural -- a verified
finding becomes ``authoritative`` only after an independent adversarial review
records its hypothesis as sound. With no adversarial verdict yet, the finding is
held non-authoritative (fail-closed), never silently trusted.

Adversarial verdicts live in ``state/adversarial_verdicts.jsonl`` as records:
    {"hypothesis_id": str, "adversarial_verdict": "sound" | "sound-but-scoped"
     | "needs-more" | "artifact", "reason": str, "verified_by": str}
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any

try:
    from store import LeWMStore
except ModuleNotFoundError:  # pragma: no cover
    sys.path.insert(0, str(Path(__file__).resolve().parent))
    from store import LeWMStore


SOUND_VERDICTS = {"sound", "sound-but-scoped"}


def load_adversarial_verdicts(store: LeWMStore) -> dict[str, dict[str, Any]]:
    path = store.paths.root / "state" / "adversarial_verdicts.jsonl"
    out: dict[str, dict[str, Any]] = {}
    if not path.exists():
        return out
    for line in path.read_text(encoding="utf-8").splitlines():
        line = line.strip()
        if not line:
            continue
        record = json.loads(line)
        out[str(record.get("hypothesis_id"))] = record
    return out


def _hypothesis_of_finding(finding: dict[str, Any], experiments_by_id: dict[str, dict[str, Any]]) -> str:
    experiment = experiments_by_id.get(str(finding.get("experiment_ref") or ""))
    if experiment is not None:
        return str(experiment.get("hypothesis_ref") or "")
    verdict_id = str(finding.get("verdict_id") or "")
    if verdict_id.startswith("verdict.") and ".executed" in verdict_id:
        return verdict_id[len("verdict.") :].split(".executed", 1)[0]
    return ""


def apply_verification_gate(store: LeWMStore) -> dict[str, Any]:
    adversarial = load_adversarial_verdicts(store)
    experiments_by_id = {str(item.get("experiment_id")): item for item in store.load_experiments()}
    findings = store.load_verified_findings()
    authoritative = demoted = pending = artifact = 0
    for finding in findings:
        hid = _hypothesis_of_finding(finding, experiments_by_id)
        record = adversarial.get(hid)
        verdict = str(record.get("adversarial_verdict")) if record else "pending"
        finding["adversarial_verdict"] = verdict
        if record is not None:
            finding["adversarial_reason"] = str(record.get("reason") or "")
        mechanically_ok = (
            str(finding.get("gate_status")) == "gate_passed" and str(finding.get("provenance")) == "executed"
        )
        is_authoritative = mechanically_ok and verdict in SOUND_VERDICTS
        was_authoritative = finding.get("authoritative") is True
        finding["authoritative"] = is_authoritative
        if is_authoritative:
            authoritative += 1
        elif verdict == "artifact":
            artifact += 1
            if was_authoritative:
                demoted += 1
        elif mechanically_ok:
            pending += 1
            if was_authoritative:
                demoted += 1
    store.write_verified_findings(findings)
    return {
        "lane": "verification",
        "authoritative": authoritative,
        "demoted_from_mechanical": demoted,
        "pending_adversarial": pending,
        "artifact": artifact,
    }


def self_test() -> int:
    import tempfile

    from store import LeWMPaths

    with tempfile.TemporaryDirectory() as tmp:
        base = Path(tmp)
        paths = LeWMPaths(
            root=base,
            hypotheses=base / "state" / "hypotheses.jsonl",
            seed_hypotheses=base / "seed_hypotheses.jsonl",
            experiments=base / "state" / "experiments.jsonl",
            contacts=base / "state" / "reality_contacts.jsonl",
            verdicts=base / "state" / "verdicts.jsonl",
            gate_results=base / "state" / "gate_results.jsonl",
            verified_findings=base / "state" / "verified_findings.jsonl",
            events=base / "state" / "events.jsonl",
            agent_tasks=base / "state" / "agent_tasks.jsonl",
            dispatch_results=base / "state" / "dispatch_results.jsonl",
            dispatch_results_archive=base / "state" / "dispatch_results.archive.jsonl",
            lane_dashboard=base / "state" / "lane_dashboard.md",
            loop_state=base / "state" / "loop_state.json",
        )
        store = LeWMStore(paths)
        store.write_experiments(
            [
                {"experiment_id": "exp.sound", "hypothesis_ref": "fi.sound"},
                {"experiment_id": "exp.artifact", "hypothesis_ref": "fi.artifact"},
                {"experiment_id": "exp.pending", "hypothesis_ref": "fi.pending"},
            ]
        )
        store.write_verified_findings(
            [
                {"verdict_id": "v.sound", "experiment_ref": "exp.sound", "gate_status": "gate_passed", "provenance": "executed", "authoritative": True},
                {"verdict_id": "v.artifact", "experiment_ref": "exp.artifact", "gate_status": "gate_passed", "provenance": "executed", "authoritative": True},
                {"verdict_id": "v.pending", "experiment_ref": "exp.pending", "gate_status": "gate_passed", "provenance": "executed", "authoritative": True},
            ]
        )
        (base / "state").mkdir(parents=True, exist_ok=True)
        (base / "state" / "adversarial_verdicts.jsonl").write_text(
            "\n".join(
                json.dumps(rec)
                for rec in [
                    {"hypothesis_id": "fi.sound", "adversarial_verdict": "sound-but-scoped", "reason": "ok"},
                    {"hypothesis_id": "fi.artifact", "adversarial_verdict": "artifact", "reason": "leakage"},
                ]
            )
            + "\n",
            encoding="utf-8",
        )
        result = apply_verification_gate(store)
        findings = {str(f.get("verdict_id")): f for f in store.load_verified_findings()}
        if findings["v.sound"]["authoritative"] is not True:
            print(json.dumps(result, indent=2), file=sys.stderr)
            return 1
        if findings["v.artifact"]["authoritative"] is not False:
            print(json.dumps(result, indent=2), file=sys.stderr)
            return 1
        if findings["v.pending"]["authoritative"] is not False or findings["v.pending"]["adversarial_verdict"] != "pending":
            print(json.dumps(result, indent=2), file=sys.stderr)
            return 1
    print("[lewm-verification] self-test ok; sound=authoritative artifact=demoted pending=held")
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Apply the adversarial-verification gate to verified findings")
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args(argv)
    if args.self_test:
        return self_test()
    store = LeWMStore()
    result = apply_verification_gate(store)
    print(json.dumps(result, ensure_ascii=False, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
