#!/usr/bin/env python3
"""Minimal LeWM autoresearch lanes: hypothesis -> experiment -> gate -> writeback."""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
import tempfile
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

try:
    import gates
    from store import LeWMPaths, LeWMStore, dedup_by_key, read_jsonl, write_jsonl
except ModuleNotFoundError:  # pragma: no cover
    sys.path.insert(0, str(Path(__file__).resolve().parent))
    import gates
    from store import LeWMPaths, LeWMStore, dedup_by_key, read_jsonl, write_jsonl


SCRIPT_DIR = Path(__file__).resolve().parent


def now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def stable_id(prefix: str, payload: dict[str, Any]) -> str:
    material = json.dumps(payload, sort_keys=True, ensure_ascii=True)
    digest = hashlib.sha256(material.encode("utf-8")).hexdigest()[:16]
    return f"{prefix}.{digest}"


def _event(event_kind: str, source: str, subject_kind: str, subject_id: str, reason: str, payload: dict[str, Any]) -> dict[str, Any]:
    base = {
        "event_kind": event_kind,
        "source": source,
        "subject_kind": subject_kind,
        "subject_id": subject_id,
        "reason": reason,
        "payload": payload,
    }
    return {
        "event_id": stable_id("event", base),
        "created_at": now_iso(),
        "status": "open",
        **base,
    }


def _task_for_experiment(experiment: dict[str, Any], hypothesis: dict[str, Any]) -> dict[str, Any]:
    prompt = "\n".join(
        [
            "LeWM dry-run experiment dispatch.",
            f"Hypothesis: {hypothesis.get('hypothesis_id')}",
            f"Predicate: {hypothesis.get('predicate')}",
            f"Script: {experiment.get('script_name')}",
            f"Criterion: {json.dumps(experiment.get('criterion'), sort_keys=True)}",
            "Return a Verdict JSON object; do not edit repository files in this stub.",
        ]
    )
    payload = {"experiment_id": experiment.get("experiment_id"), "prompt": prompt}
    return {
        "task_id": stable_id("task", payload),
        "created_at": now_iso(),
        "agent_id": "lewm-experimentalist-stub",
        "lane": "experiment",
        "action": "dry_run_dispatch",
        "status": "queued",
        "priority": 80,
        "experiment_ref": experiment.get("experiment_id"),
        "hypothesis_ref": hypothesis.get("hypothesis_id"),
        "prompt": prompt,
        "stub_output": f"would dispatch: {prompt}",
    }


def _default_contact_for_hypothesis(hypothesis: dict[str, Any]) -> dict[str, Any]:
    refs = [str(item) for item in hypothesis.get("reality_contact_refs", []) if isinstance(item, str)]
    contact_id = refs[0] if refs else f"contact.{hypothesis.get('hypothesis_id')}"
    carrier = str(hypothesis.get("carrier") or "unknown checkpoint")
    criterion = hypothesis.get("criterion") if isinstance(hypothesis.get("criterion"), dict) else {}
    metric = str(criterion.get("metric") or "allocation_delta")
    return {
        "contact_id": contact_id,
        "source_kind": "checkpoint-export",
        "checkpoint": carrier,
        "export_ref": carrier,
        "can_measure": [metric, "uer", "auroc"],
        "cannot_measure": ["real_robot_transfer", "paper_claim_strength"],
        "frozen_fields": {"anchor.metric": 0.123456789},
        "notes": "stub contact seeded by LeWM autoresearch lane",
    }


def _compile_experiment(hypothesis: dict[str, Any]) -> dict[str, Any]:
    hypothesis_id = str(hypothesis.get("hypothesis_id") or "unknown")
    criterion = hypothesis.get("criterion") if isinstance(hypothesis.get("criterion"), dict) else {}
    script = str(hypothesis.get("suggested_script") or "_autoresearch_stub_experiment.py")
    return {
        "experiment_id": f"exp.{hypothesis_id}",
        "hypothesis_ref": hypothesis_id,
        "script_name": script,
        "input_data": [str(hypothesis.get("carrier") or "checkpoint export")],
        "criterion": criterion or {"kind": "delta_ci_below_zero", "metric": "allocation_delta"},
        "predeclared_thresholds": {"alpha": 0.05, "anchor_tolerance": 1e-9},
        "required_contacts": [str(item) for item in hypothesis.get("reality_contact_refs", []) if isinstance(item, str)],
        "status": "planned",
        "compiled_at": now_iso(),
    }


def _stub_verdict(experiment: dict[str, Any], contact: dict[str, Any]) -> dict[str, Any]:
    criterion = experiment.get("criterion") if isinstance(experiment.get("criterion"), dict) else {}
    metric = str(criterion.get("metric") or "allocation_delta")
    return {
        "verdict_id": f"verdict.{experiment.get('experiment_id')}.stub",
        "experiment_ref": experiment.get("experiment_id"),
        "contact_ref": contact.get("contact_id"),
        "status": "fail-closed",
        "reported_claim": f"stub dry-run for {metric}; no scientific claim",
        "provenance": "stub",
        "acceptance": {"status": "pending"},
        "metrics": {"anchor.metric": 0.123456789, metric: 0.0},
        "ci": {metric: {"low": -0.01, "high": 0.01}},
        "anchoring": {"anchor.metric": 0.123456789},
        "replicate_group": f"rg.{experiment.get('experiment_id')}.stub",
        "run_fingerprint": stable_id("run", {"experiment": experiment.get("experiment_id"), "kind": "stub"}),
        "measured_scope": [metric],
        "wall_time": 0.0,
    }


def bootstrap_seed_hypotheses(store: LeWMStore) -> dict[str, Any]:
    existing = store.load_hypotheses()
    if existing:
        return {"bootstrapped": False, "hypotheses": len(existing)}
    seeds = store.load_seed_hypotheses()
    store.write_hypotheses(seeds)
    events = store.load_events()
    events.append(_event("hypotheses_seeded", "hypothesis", "hypothesis_set", "seed", "state was empty; copied seed_hypotheses.jsonl", {"count": len(seeds)}))
    store.write_events(dedup_by_key(events, "event_id"))
    return {"bootstrapped": True, "hypotheses": len(seeds)}


def run_hypothesis_lane(store: LeWMStore) -> dict[str, Any]:
    bootstrap = bootstrap_seed_hypotheses(store)
    hypotheses = store.load_hypotheses()
    experiments = store.load_experiments()
    planned = {str(item.get("hypothesis_ref") or "") for item in experiments}
    next_item = next((item for item in hypotheses if str(item.get("hypothesis_id") or "") not in planned), None)
    events = store.load_events()
    if next_item is not None:
        events.append(
            _event(
                "hypothesis_ready",
                "hypothesis",
                "hypothesis",
                str(next_item.get("hypothesis_id")),
                "hypothesis has no compiled experiment",
                next_item,
            )
        )
        store.write_events(dedup_by_key(events, "event_id"))
    return {
        "lane": "hypothesis",
        **bootstrap,
        "ready_hypothesis": next_item.get("hypothesis_id") if next_item else "",
    }


def run_experiment_lane(store: LeWMStore) -> dict[str, Any]:
    hypotheses = store.load_hypotheses()
    experiments = store.load_experiments()
    contacts = store.load_contacts()
    tasks = store.load_agent_tasks()
    events = store.load_events()
    experiment_ids = {str(item.get("experiment_id") or "") for item in experiments}
    contact_ids = {str(item.get("contact_id") or "") for item in contacts}
    compiled = 0
    task_count = 0
    for hypothesis in hypotheses:
        experiment = _compile_experiment(hypothesis)
        if str(experiment["experiment_id"]) in experiment_ids:
            continue
        contact = _default_contact_for_hypothesis(hypothesis)
        if str(contact["contact_id"]) not in contact_ids:
            contacts.append(contact)
            contact_ids.add(str(contact["contact_id"]))
        experiments.append(experiment)
        experiment_ids.add(str(experiment["experiment_id"]))
        task = _task_for_experiment(experiment, hypothesis)
        tasks.append(task)
        task_count += 1
        compiled += 1
        events.append(
            _event(
                "experiment_compiled",
                "experiment",
                "experiment",
                str(experiment.get("experiment_id")),
                "compiled LeWM hypothesis to dry-run experiment spec",
                {"experiment": experiment, "task_id": task["task_id"]},
            )
        )
    store.write_contacts(dedup_by_key(contacts, "contact_id"))
    store.write_experiments(dedup_by_key(experiments, "experiment_id"))
    store.write_agent_tasks(dedup_by_key(tasks, "task_id"))
    store.write_events(dedup_by_key(events, "event_id"))
    dispatch_records = [
        {"task_id": task["task_id"], "status": "dry_run", "created_at": now_iso(), "output": task["stub_output"]}
        for task in tasks
        if str(task.get("status")) == "queued"
    ]
    store.append_dispatch_results(dispatch_records)
    return {"lane": "experiment", "compiled": compiled, "dry_run_tasks": task_count}


def run_stub_verdict_lane(store: LeWMStore) -> dict[str, Any]:
    experiments = store.load_experiments()
    contacts = store.load_contacts()
    contact_by_id = {str(item.get("contact_id")): item for item in contacts}
    verdicts = store.load_verdicts()
    migrated = 0
    for verdict in verdicts:
        verdict_id = str(verdict.get("verdict_id") or "")
        if "provenance" not in verdict and (verdict_id.endswith(".stub") or verdict_id.endswith(".stub.rep")):
            verdict["provenance"] = "stub"
            migrated += 1
    verdict_experiments = {str(item.get("experiment_ref") or "") for item in verdicts}
    written = 0
    for experiment in experiments:
        experiment_id = str(experiment.get("experiment_id") or "")
        if experiment_id in verdict_experiments:
            continue
        required = [str(item) for item in experiment.get("required_contacts", []) if isinstance(item, str)]
        contact = contact_by_id.get(required[0]) if required else next(iter(contact_by_id.values()), None)
        if contact is None:
            continue
        first = _stub_verdict(experiment, contact)
        second = dict(first)
        second["verdict_id"] = f"{first['verdict_id']}.rep"
        second["wall_time"] = 0.1
        verdicts.extend([first, second])
        written += 2
    store.write_verdicts(dedup_by_key(verdicts, "verdict_id"))
    return {"lane": "stub_verdict", "verdicts_written": written, "stub_verdicts_migrated": migrated}


def run_gate_lane(store: LeWMStore) -> dict[str, Any]:
    results = gates.gate_all(store.load_hypotheses(), store.load_experiments(), store.load_contacts(), store.load_verdicts())
    store.write_gate_results(results)
    passed = sum(1 for result in results if result.get("gate_status") == "gate_passed")
    blocked = len(results) - passed
    return {"lane": "gate", "gate_results": len(results), "passed": passed, "blocked": blocked}


def run_writeback_lane(store: LeWMStore) -> dict[str, Any]:
    verdicts = {str(item.get("verdict_id")): item for item in store.load_verdicts()}
    gate_results = store.load_gate_results()
    existing = store.load_verified_findings()
    for finding in existing:
        verdict = verdicts.get(str(finding.get("verdict_id") or ""))
        provenance = str(finding.get("provenance") or (verdict.get("provenance") if verdict else "") or "")
        if not provenance:
            provenance = "stub" if str(finding.get("reported_claim") or "").startswith("stub dry-run") else "unknown"
        finding["provenance"] = provenance
        finding["authoritative"] = provenance == "executed"
    existing_ids = {str(item.get("verdict_id") or "") for item in existing}
    additions: list[dict[str, Any]] = []
    authoritative_added = 0
    non_authoritative_added = 0
    for result in gate_results:
        verdict_id = str(result.get("verdict_id") or "")
        if verdict_id in existing_ids:
            continue
        verdict = verdicts.get(verdict_id)
        if verdict is None:
            continue
        provenance = str(verdict.get("provenance") or "unknown")
        authoritative = result.get("gate_status") == "gate_passed" and provenance == "executed"
        if result.get("gate_status") != "gate_passed" and provenance == "executed":
            continue
        if authoritative:
            authoritative_added += 1
        else:
            non_authoritative_added += 1
        additions.append(
            {
                "finding_id": stable_id("finding", {"verdict_id": verdict_id}),
                "written_at": now_iso(),
                "verdict_id": verdict_id,
                "experiment_ref": verdict.get("experiment_ref"),
                "status": verdict.get("status"),
                "reported_claim": verdict.get("reported_claim"),
                "provenance": provenance,
                "authoritative": authoritative,
                "gate_status": result.get("gate_status"),
            }
        )
    records = dedup_by_key(existing + additions, "finding_id")
    store.write_verified_findings(records)
    authoritative_total = sum(1 for item in records if item.get("authoritative") is True)
    return {
        "lane": "writeback",
        "verified_findings_added": len(additions),
        "authoritative_added": authoritative_added,
        "non_authoritative_added": non_authoritative_added,
        "verified_findings_total": len(records),
        "authoritative_total": authoritative_total,
    }


def write_dashboard(store: LeWMStore, summaries: list[dict[str, Any]]) -> None:
    lines = [
        "# LeWM Autoresearch Dashboard",
        "",
        f"Updated: {now_iso()}",
        "",
        "| Lane | Summary |",
        "| --- | --- |",
    ]
    for summary in summaries:
        lane = str(summary.get("lane") or "unknown")
        lines.append(f"| {lane} | `{json.dumps(summary, sort_keys=True)}` |")
    store.paths.lane_dashboard.parent.mkdir(parents=True, exist_ok=True)
    store.paths.lane_dashboard.write_text("\n".join(lines) + "\n", encoding="utf-8")


def run_all_lanes(store: LeWMStore) -> list[dict[str, Any]]:
    summaries = [
        run_hypothesis_lane(store),
        run_experiment_lane(store),
        run_stub_verdict_lane(store),
        run_gate_lane(store),
        run_writeback_lane(store),
    ]
    write_dashboard(store, summaries)
    return summaries


def self_test() -> int:
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
        write_jsonl(
            paths.seed_hypotheses,
            [
                {
                    "hypothesis_id": "fi-001.cvar-tail",
                    "predicate": "CVaR tail objective can reduce allocation_delta.",
                    "failure_surface": "allocation_delta",
                    "horizon": {"steps": [1, 4, 8]},
                    "perturbation_family": "tail-risk weighting",
                    "carrier": "pusht_latent_large.npz",
                    "criterion": {"kind": "delta_ci_below_zero", "metric": "allocation_delta"},
                    "reality_contact_refs": ["pusht.phase2c.export"],
                    "status": "open",
                }
            ],
        )
        store = LeWMStore(paths)
        summaries = run_all_lanes(store)
        if len(store.load_hypotheses()) != 1 or len(store.load_experiments()) != 1:
            print(json.dumps(summaries, indent=2), file=sys.stderr)
            return 1
        if not store.load_agent_tasks() or not store.load_gate_results() or not paths.lane_dashboard.exists():
            print(json.dumps(summaries, indent=2), file=sys.stderr)
            return 1
        findings = store.load_verified_findings()
        if not findings or any(item.get("authoritative") is not False for item in findings):
            print(json.dumps(findings, indent=2), file=sys.stderr)
            return 1
        first_dispatch_count = len(read_jsonl(paths.dispatch_results))
        run_all_lanes(store)
        second_dispatch_count = len(read_jsonl(paths.dispatch_results))
        if first_dispatch_count != second_dispatch_count:
            print(json.dumps({"first": first_dispatch_count, "second": second_dispatch_count}, indent=2), file=sys.stderr)
            return 1
    print("[lewm-lanes] self-test ok")
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Run LeWM autoresearch lanes")
    parser.add_argument("--lane", choices=["hypothesis", "experiment", "gate", "writeback", "all"], default="all")
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args(argv)
    if args.self_test:
        return self_test()
    store = LeWMStore()
    if args.lane == "hypothesis":
        summaries = [run_hypothesis_lane(store)]
    elif args.lane == "experiment":
        summaries = [run_experiment_lane(store), run_stub_verdict_lane(store)]
    elif args.lane == "gate":
        summaries = [run_gate_lane(store)]
    elif args.lane == "writeback":
        summaries = [run_writeback_lane(store)]
    else:
        summaries = run_all_lanes(store)
    write_dashboard(store, summaries)
    print(json.dumps(summaries, ensure_ascii=False, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
