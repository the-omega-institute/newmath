#!/usr/bin/env python3
"""Real experiment execution adapter for the LeWM autoresearch loop.

Each open hypothesis maps to a runner at ``autoresearch/runners/<hypothesis_id>.py``
that, given ``--out <path> --seed <n>``, deterministically writes one verdict
payload:

    {
      "hypothesis_id": str,
      "anchor": {"field": "anchor.<name>", "value": float},
      "metric": str,                 # == hypothesis.criterion.metric
      "metric_value": float,
      "ci": {"low": float, "high": float},
      "status": "fail-closed" | null,   # optional; fail-closed for single-class
      "measured_scope": [str, ...],
      "reported_claim": str
    }

The adapter runs the runner twice at a fixed seed, requires byte-identical
payloads (determinism), then emits two ``provenance: executed`` verdicts in one
replicate group so the existing anchor / reproducibility / criterion / overclaim
/ provenance gates decide acceptance. Nothing here invents numbers: every metric
comes from the runner's measured payload.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
import tempfile
import time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from typing import Any

try:
    from lanes import _compile_experiment, now_iso, run_gate_lane, run_writeback_lane, stable_id
    from store import LeWMStore, dedup_by_key
    from verification import apply_verification_gate
except ModuleNotFoundError:  # pragma: no cover
    sys.path.insert(0, str(Path(__file__).resolve().parent))
    from lanes import _compile_experiment, now_iso, run_gate_lane, run_writeback_lane, stable_id
    from store import LeWMStore, dedup_by_key
    from verification import apply_verification_gate


SCRIPT_DIR = Path(__file__).resolve().parent
SURVEY_DIR = SCRIPT_DIR.parent
RUNNERS_DIR = SCRIPT_DIR / "runners"
FIXED_SEED = 0


def _derive_status(criterion: dict[str, Any], low: float, high: float) -> str:
    kind = str(criterion.get("kind") or "")
    if kind in {"delta_ci_below_zero", "uer_ci_separation"}:
        if high < 0:
            return "positive"
        if low >= 0:
            return "negative"
        return "unidentifiable"
    if kind == "delta_ci_above_zero":
        if low > 0:
            return "positive"
        if high <= 0:
            return "negative"
        return "unidentifiable"
    if kind == "auroc_ci_separation":
        threshold = float(criterion.get("null", 0.5))
        if low > threshold:
            return "positive"
        if high <= threshold:
            return "negative"
        return "unidentifiable"
    return "unidentifiable"


def _run_runner_once(runner: Path, out_path: Path) -> tuple[int, str, float]:
    cmd = [sys.executable, str(runner), "--out", str(out_path), "--seed", str(FIXED_SEED)]
    start = time.time()
    proc = subprocess.run(cmd, capture_output=True, text=True, cwd=str(SURVEY_DIR))
    return proc.returncode, (proc.stderr or "")[-3000:], time.time() - start


def execute_one(hypothesis: dict[str, Any]) -> dict[str, Any]:
    """Run one hypothesis runner twice and return its two payloads + wall times.

    This is pure measurement; verdict assembly + persistence happens on the main
    thread in ``execute_and_record`` so concurrent runs never race on the store.
    """
    hid = str(hypothesis.get("hypothesis_id") or "unknown")
    runner = RUNNERS_DIR / f"{hid}.py"
    if not runner.exists():
        return {"hypothesis_id": hid, "outcome": "no_runner", "runner": str(runner)}
    payloads: list[dict[str, Any]] = []
    wall_times: list[float] = []
    for _ in range(2):
        handle = tempfile.NamedTemporaryFile(suffix=".json", delete=False)
        out_path = Path(handle.name)
        handle.close()
        rc, stderr, wall = _run_runner_once(runner, out_path)
        if rc != 0 or not out_path.exists():
            out_path.unlink(missing_ok=True)
            return {"hypothesis_id": hid, "outcome": "runner_failed", "returncode": rc, "stderr": stderr}
        try:
            payloads.append(json.loads(out_path.read_text(encoding="utf-8")))
        finally:
            out_path.unlink(missing_ok=True)
        wall_times.append(wall)
    if payloads[0] != payloads[1]:
        return {"hypothesis_id": hid, "outcome": "nondeterministic"}
    return {"hypothesis_id": hid, "outcome": "measured", "payload": payloads[0], "wall_times": wall_times}


def _verdicts_from_payload(hypothesis: dict[str, Any], payload: dict[str, Any], wall_times: list[float]) -> tuple[dict[str, Any], dict[str, Any], dict[str, Any], dict[str, Any]]:
    hid = str(hypothesis.get("hypothesis_id") or "unknown")
    criterion = hypothesis.get("criterion") if isinstance(hypothesis.get("criterion"), dict) else {}
    metric = str(payload["metric"])
    metric_value = float(payload["metric_value"])
    low = float(payload["ci"]["low"])
    high = float(payload["ci"]["high"])
    anchor_field = str(payload["anchor"]["field"])
    anchor_value = float(payload["anchor"]["value"])
    measured_scope = sorted({str(item) for item in payload.get("measured_scope", [metric])})
    runner_status = str(payload.get("status") or "")
    status = "fail-closed" if runner_status == "fail-closed" else _derive_status(criterion, low, high)
    claim = str(payload.get("reported_claim") or f"{metric} measured on {hypothesis.get('carrier')}")

    experiment = _compile_experiment(hypothesis)
    experiment["status"] = "executed"
    contact = {
        "contact_id": f"contact.{hid}.executed",
        "source_kind": "checkpoint-export",
        "checkpoint": str(hypothesis.get("carrier") or "unknown"),
        "export_ref": str(hypothesis.get("carrier") or "unknown"),
        "can_measure": sorted(set(measured_scope) | {metric}),
        "cannot_measure": ["real_robot_transfer", "paper_claim_strength"],
        "frozen_fields": {anchor_field: anchor_value},
        "notes": f"executed contact established from runner measurement for {hid}",
    }
    base = {
        "experiment_ref": experiment["experiment_id"],
        "contact_ref": contact["contact_id"],
        "status": status,
        "reported_claim": claim,
        "provenance": "executed",
        "acceptance": {"status": "pending"},
        "metrics": {anchor_field: anchor_value, metric: metric_value},
        "ci": {metric: {"low": low, "high": high}},
        "anchoring": {anchor_field: anchor_value},
        "replicate_group": f"rg.{hid}.executed",
        "run_fingerprint": stable_id("run", {"hypothesis": hid, "payload": payload}),
        "measured_scope": measured_scope,
    }
    first = dict(base, verdict_id=f"verdict.{hid}.executed.a", wall_time=float(wall_times[0]))
    second = dict(base, verdict_id=f"verdict.{hid}.executed.b", wall_time=float(wall_times[1]))
    return experiment, contact, first, second


def execute_and_record(store: LeWMStore, hypotheses: list[dict[str, Any]], *, max_workers: int = 1) -> list[dict[str, Any]]:
    runnable = [h for h in hypotheses if (RUNNERS_DIR / f"{str(h.get('hypothesis_id'))}.py").exists()]
    outcomes: list[dict[str, Any]]
    if max_workers > 1 and len(runnable) > 1:
        with ThreadPoolExecutor(max_workers=max_workers) as pool:
            outcomes = list(pool.map(execute_one, runnable))
    else:
        outcomes = [execute_one(h) for h in runnable]

    by_id = {str(h.get("hypothesis_id")): h for h in runnable}
    experiments = store.load_experiments()
    contacts = store.load_contacts()
    verdicts = store.load_verdicts()
    summaries: list[dict[str, Any]] = []
    for outcome in outcomes:
        hid = str(outcome.get("hypothesis_id"))
        if outcome.get("outcome") != "measured":
            summaries.append(outcome)
            continue
        experiment, contact, first, second = _verdicts_from_payload(by_id[hid], outcome["payload"], outcome["wall_times"])
        experiments.append(experiment)
        contacts.append(contact)
        verdicts.extend([first, second])
        summaries.append(
            {
                "hypothesis_id": hid,
                "outcome": "executed",
                "metric": first["measured_scope"],
                "metric_value": first["metrics"],
                "ci": first["ci"],
                "verdict_status": first["status"],
            }
        )
    store.write_experiments(dedup_by_key(experiments, "experiment_id"))
    store.write_contacts(dedup_by_key(contacts, "contact_id"))
    store.write_verdicts(dedup_by_key(verdicts, "verdict_id"))
    return summaries


def run_execution_lane(store: LeWMStore, *, max_workers: int = 1) -> dict[str, Any]:
    hypotheses = store.load_hypotheses() or store.load_seed_hypotheses()
    if not store.load_hypotheses():
        store.write_hypotheses(hypotheses)
    summaries = execute_and_record(store, hypotheses, max_workers=max_workers)
    gate = run_gate_lane(store)
    writeback = run_writeback_lane(store)
    verification = apply_verification_gate(store)
    executed = sum(1 for item in summaries if item.get("outcome") == "executed")
    return {
        "lane": "execution",
        "runners_executed": executed,
        "runner_outcomes": summaries,
        "gate": gate,
        "writeback": writeback,
        "verification": verification,
    }


def self_test() -> int:
    import textwrap

    with tempfile.TemporaryDirectory() as tmp:
        base = Path(tmp)
        runners = base / "runners"
        runners.mkdir(parents=True, exist_ok=True)
        # A deterministic synthetic runner that emits a clean positive payload.
        (runners / "fi-demo.selftest.py").write_text(
            textwrap.dedent(
                """
                import argparse, json
                p = argparse.ArgumentParser(); p.add_argument("--out"); p.add_argument("--seed", type=int, default=0)
                a = p.parse_args()
                payload = {
                    "hypothesis_id": "fi-demo.selftest",
                    "anchor": {"field": "anchor.identity_max_abs", "value": 0.0},
                    "metric": "demo_auroc",
                    "metric_value": 0.74,
                    "ci": {"low": 0.70, "high": 0.78},
                    "measured_scope": ["demo_auroc"],
                    "reported_claim": "demo_auroc CI strictly above 0.5 on synthetic fixture",
                }
                open(a.out, "w", encoding="utf-8").write(json.dumps(payload))
                """
            ).strip()
            + "\n",
            encoding="utf-8",
        )
        # Point the adapter + store at the temp tree.
        global RUNNERS_DIR, SURVEY_DIR
        RUNNERS_DIR = runners
        SURVEY_DIR = base
        from store import LeWMPaths

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
        store.write_hypotheses(
            [
                {
                    "hypothesis_id": "fi-demo.selftest",
                    "predicate": "demo",
                    "carrier": "synthetic.npz",
                    "criterion": {"kind": "auroc_ci_separation", "metric": "demo_auroc", "null": 0.5},
                    "reality_contact_refs": ["synthetic"],
                    "status": "open",
                }
            ]
        )
        # The adversarial-verification gate holds findings non-authoritative until
        # a review marks the hypothesis sound; seed that verdict for the fixture.
        (base / "state").mkdir(parents=True, exist_ok=True)
        (base / "state" / "adversarial_verdicts.jsonl").write_text(
            json.dumps({"hypothesis_id": "fi-demo.selftest", "adversarial_verdict": "sound", "reason": "synthetic fixture"}) + "\n",
            encoding="utf-8",
        )
        result = run_execution_lane(store, max_workers=1)
        findings = store.load_verified_findings()
        authoritative = [f for f in findings if f.get("authoritative") is True]
        if result["runners_executed"] != 1:
            print(json.dumps(result, indent=2), file=sys.stderr)
            return 1
        if not authoritative or authoritative[0].get("status") != "positive":
            print(json.dumps({"findings": findings, "result": result}, indent=2), file=sys.stderr)
            return 1
        # Idempotent re-run: no duplicate authoritative findings.
        run_execution_lane(store, max_workers=1)
        again = [f for f in store.load_verified_findings() if f.get("authoritative") is True]
        if len(again) != len(authoritative):
            print(json.dumps({"first": authoritative, "second": again}, indent=2), file=sys.stderr)
            return 1
    print("[lewm-executor] self-test ok; synthetic runner -> executed verdict -> authoritative finding")
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Execute LeWM autoresearch experiment runners")
    parser.add_argument("--max-workers", type=int, default=1, help="parallel runner processes")
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args(argv)
    if args.self_test:
        return self_test()
    store = LeWMStore()
    result = run_execution_lane(store, max_workers=args.max_workers)
    print(json.dumps(result, ensure_ascii=False, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
