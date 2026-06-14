#!/usr/bin/env python3
"""BEDC-JEPA research-deepening loop.

This loop is the BEDC-JEPA analogue of the BioReality deepening loop: it treats
experiments as evidence packets for research questions, not as the purpose of
the automation.  The output is a prioritized research queue over failure
semantics, evidence boundaries, calibration, allocation, and paper writeback.
"""

from __future__ import annotations

import argparse
import json
import sys
import tempfile
from pathlib import Path
from typing import Any

try:
    from gates import gate_all
    from lanes import now_iso, stable_id
    from store import LeWMPaths, LeWMStore, dedup_by_key, read_jsonl, write_jsonl
except ModuleNotFoundError:  # pragma: no cover
    sys.path.insert(0, str(Path(__file__).resolve().parent))
    from gates import gate_all
    from lanes import now_iso, stable_id
    from store import LeWMPaths, LeWMStore, dedup_by_key, read_jsonl, write_jsonl


SCRIPT_DIR = Path(__file__).resolve().parent
FINDINGS_DIR = SCRIPT_DIR / "findings"

RESEARCH_AXES = {
    "detection": "Can the ledger read future failure without label leakage?",
    "horizon": "Does the signal remain indexed by rollout horizon?",
    "selective": "Can the model abstain or admit claims under calibration?",
    "allocation": "Does the score improve budget allocation, not only detection?",
    "compute_value": "Does the model learn option-conditioned marginal compute value rather than failure probability alone?",
    "representation": "Does the objective reshape the carrier rather than only the head?",
    "ood": "Does the monitor fail closed under non-exchangeable shift?",
    "tail": "Does the objective target tail risk rather than mean error?",
    "paper": "Can a scoped paper claim be written without overclaim?",
}

FORBIDDEN_PAPER_SCOPES = {
    "real_robot_transfer",
    "paper_claim_strength",
    "universal_failure_reader",
    "full_planner",
    "complete_world_model",
}


def _ids(records: list[dict[str, Any]], key: str) -> set[str]:
    return {str(record.get(key)) for record in records if record.get(key)}


def _axis_from_hypothesis(hypothesis: dict[str, Any]) -> str:
    text = " ".join(
        str(hypothesis.get(key) or "")
        for key in ("hypothesis_id", "predicate", "failure_surface", "perturbation_family")
    ).lower()
    ordered = [
        ("compute_value", ("compute-value", "compute value", "marginal", "intervention", "option-conditioned", "mv(")),
        ("allocation", ("allocation", "budget", "ranking")),
        ("selective", ("selective", "conformal", "admission", "risk_margin")),
        ("representation", ("reencoder", "representation", "encoder")),
        ("ood", ("ood", "shift", "cross-env", "transfer")),
        ("tail", ("cvar", "tail")),
        ("horizon", ("horizon", "multi-horizon")),
        ("detection", ("auroc", "detection", "failure")),
    ]
    for axis, needles in ordered:
        if any(needle in text for needle in needles):
            return axis
    return "detection"


def _task(
    subject_kind: str,
    subject_id: str,
    task_kind: str,
    reason: str,
    priority: int,
    axis: str,
    payload: dict[str, Any] | None = None,
) -> dict[str, Any]:
    base = {
        "subject_kind": subject_kind,
        "subject_id": subject_id,
        "task_kind": task_kind,
        "reason": reason,
        "priority": int(priority),
        "axis": axis,
        "payload": payload or {},
    }
    return {
        "task_id": stable_id("research-task", base),
        "created_at": now_iso(),
        "status": "queued",
        **base,
    }


def _gate_by_verdict(gate_results: list[dict[str, Any]]) -> dict[str, dict[str, Any]]:
    return {
        str(result.get("verdict_id") or ""): result
        for result in gate_results
        if result.get("verdict_id")
    }


def _experiment_by_hypothesis(experiments: list[dict[str, Any]]) -> dict[str, list[dict[str, Any]]]:
    out: dict[str, list[dict[str, Any]]] = {}
    for experiment in experiments:
        out.setdefault(str(experiment.get("hypothesis_ref") or ""), []).append(experiment)
    return out


def _verdicts_by_experiment(verdicts: list[dict[str, Any]]) -> dict[str, list[dict[str, Any]]]:
    out: dict[str, list[dict[str, Any]]] = {}
    for verdict in verdicts:
        out.setdefault(str(verdict.get("experiment_ref") or ""), []).append(verdict)
    return out


def _finding_hypothesis_id(finding: dict[str, Any]) -> str:
    direct = str(finding.get("hypothesis_id") or "")
    if direct:
        return direct
    experiment_ref = str(finding.get("experiment_ref") or "")
    return experiment_ref.removeprefix("exp.") if experiment_ref.startswith("exp.") else ""


def _has_authoritative_finding(hypothesis_id: str, experiments: list[dict[str, Any]], findings: list[dict[str, Any]]) -> bool:
    experiment_ids = {
        str(experiment.get("experiment_id") or "")
        for experiment in experiments
        if str(experiment.get("hypothesis_ref") or "") == hypothesis_id
    }
    return any(
        finding.get("authoritative") is True
        and (str(finding.get("experiment_ref") or "") in experiment_ids or _finding_hypothesis_id(finding) == hypothesis_id)
        for finding in findings
    )


def load_research_findings(store: LeWMStore) -> list[dict[str, Any]]:
    state_findings = store.load_verified_findings()
    exported_findings = read_jsonl(FINDINGS_DIR / "verified_findings.jsonl")
    return dedup_by_key(state_findings + exported_findings, "finding_id")


def _paper_scope_issues(verdict: dict[str, Any], contact: dict[str, Any] | None) -> list[str]:
    claim = str(verdict.get("reported_claim") or "")
    issues = [f"reported_claim mentions forbidden scope: {scope}" for scope in sorted(FORBIDDEN_PAPER_SCOPES) if scope in claim]
    if contact is None:
        return issues
    cannot = {str(item) for item in contact.get("cannot_measure", []) if isinstance(item, str)}
    measured = {str(item) for item in verdict.get("measured_scope", []) if isinstance(item, str)}
    for scope in sorted(cannot & measured):
        issues.append(f"measured_scope enters cannot_measure: {scope}")
    return issues


def plan_deepening_tasks(
    hypotheses: list[dict[str, Any]],
    experiments: list[dict[str, Any]],
    contacts: list[dict[str, Any]],
    verdicts: list[dict[str, Any]],
    gate_results: list[dict[str, Any]],
    findings: list[dict[str, Any]],
) -> list[dict[str, Any]]:
    contact_ids = _ids(contacts, "contact_id")
    contacts_by_id = {str(contact.get("contact_id") or ""): contact for contact in contacts}
    experiments_for_hypothesis = _experiment_by_hypothesis(experiments)
    verdicts_for_experiment = _verdicts_by_experiment(verdicts)
    gate_for_verdict = _gate_by_verdict(gate_results)
    tasks: list[dict[str, Any]] = []

    for hypothesis in hypotheses:
        hypothesis_id = str(hypothesis.get("hypothesis_id") or "")
        axis = _axis_from_hypothesis(hypothesis)
        has_authority = _has_authoritative_finding(hypothesis_id, experiments, findings)
        if has_authority:
            tasks.append(_task("hypothesis", hypothesis_id, "ready_for_paper_boundary_review", "authoritative finding is available", 30, "paper"))
            continue
        refs = [str(item) for item in hypothesis.get("reality_contact_refs", []) if isinstance(item, str)]
        if not refs:
            tasks.append(_task("hypothesis", hypothesis_id, "needs_reality_contact", "hypothesis has no evidence contact", 95, axis))
        for ref in refs:
            if ref not in contact_ids:
                tasks.append(_task("hypothesis", hypothesis_id, "needs_reality_contact", f"missing evidence contact {ref}", 95, axis))

        linked_experiments = experiments_for_hypothesis.get(hypothesis_id, [])
        if not linked_experiments:
            tasks.append(_task("hypothesis", hypothesis_id, "needs_experiment_design", "hypothesis has no compiled experiment", 90, axis))
            continue

        linked_verdicts = [verdict for experiment in linked_experiments for verdict in verdicts_for_experiment.get(str(experiment.get("experiment_id") or ""), [])]
        if not linked_verdicts:
            tasks.append(_task("hypothesis", hypothesis_id, "needs_execution", "compiled experiment has no verdict", 88, axis))
        if not any(str(verdict.get("provenance") or "") == "executed" for verdict in linked_verdicts):
            tasks.append(_task("hypothesis", hypothesis_id, "needs_executed_evidence", "only stub or missing verdicts are present", 86, axis))

        if linked_verdicts and not _has_authoritative_finding(hypothesis_id, experiments, findings):
            blocked = [
                gate_for_verdict.get(str(verdict.get("verdict_id") or ""), {})
                for verdict in linked_verdicts
                if gate_for_verdict.get(str(verdict.get("verdict_id") or ""), {}).get("gate_status") == "gate_blocked"
            ]
            if blocked:
                reason = "; ".join(str(issue) for issue in blocked[0].get("issues", [])[:3]) or "gate blocked"
                tasks.append(_task("hypothesis", hypothesis_id, "needs_gate_repair_or_boundary_narrowing", reason, 92, axis, {"blocked_gate": blocked[0]}))
            else:
                tasks.append(_task("hypothesis", hypothesis_id, "needs_adversarial_review", "evidence exists but is not authoritative", 78, axis))

    for verdict in verdicts:
        verdict_id = str(verdict.get("verdict_id") or "")
        contact = contacts_by_id.get(str(verdict.get("contact_ref") or ""))
        scope_issues = _paper_scope_issues(verdict, contact)
        if scope_issues:
            tasks.append(_task("verdict", verdict_id, "blocked_overclaim", "; ".join(scope_issues[:3]), 100, "paper"))

    existing_kinds = {(task["subject_kind"], task["subject_id"], task["task_kind"]) for task in tasks}
    axis_with_authority = {
        _axis_from_hypothesis(hypothesis)
        for hypothesis in hypotheses
        if _has_authoritative_finding(str(hypothesis.get("hypothesis_id") or ""), experiments, findings)
    }
    for axis in ("detection", "selective", "allocation", "compute_value", "ood", "tail"):
        if axis not in axis_with_authority:
            key = ("research_axis", axis, "needs_axis_evidence")
            if key not in existing_kinds:
                tasks.append(_task("research_axis", axis, "needs_axis_evidence", RESEARCH_AXES[axis], 60, axis))

    tasks.sort(key=lambda item: (-int(item["priority"]), str(item["axis"]), str(item["subject_kind"]), str(item["subject_id"]), str(item["task_kind"])))
    return dedup_by_key(tasks, "task_id")


def plan_review_queue(gate_results: list[dict[str, Any]], tasks: list[dict[str, Any]]) -> list[dict[str, Any]]:
    blocked_subjects = {
        (str(task.get("subject_kind") or ""), str(task.get("subject_id") or ""))
        for task in tasks
        if str(task.get("task_kind") or "").startswith("blocked")
    }
    review: list[dict[str, Any]] = []
    for result in gate_results:
        verdict_id = str(result.get("verdict_id") or "")
        decision = "blocked" if ("verdict", verdict_id) in blocked_subjects else "needs_deepening"
        if result.get("gate_status") == "gate_passed" and decision != "blocked":
            decision = "review_ready"
        review.append(
            {
                "review_id": stable_id("review", {"verdict_id": verdict_id, "decision": decision}),
                "verdict_id": verdict_id,
                "experiment_ref": result.get("experiment_ref"),
                "gate_status": result.get("gate_status"),
                "review_decision": decision,
                "allowed_write": "paper_boundary_only" if decision == "review_ready" else "none",
            }
        )
    review.sort(key=lambda item: (str(item["review_decision"]), str(item["verdict_id"])))
    return review


def _event_from_task(task: dict[str, Any]) -> dict[str, Any]:
    base = {
        "event_kind": "research_deepening_needed",
        "source": "bedc-jepa-research-loop",
        "subject_kind": task.get("subject_kind"),
        "subject_id": task.get("subject_id"),
        "reason": task.get("reason"),
        "payload": task,
    }
    return {
        "event_id": stable_id("event", base),
        "created_at": now_iso(),
        "status": "open",
        **base,
    }


def _agent_for_task(task: dict[str, Any]) -> tuple[str, str]:
    kind = str(task.get("task_kind") or "")
    axis = str(task.get("axis") or "")
    if kind in {"needs_reality_contact", "needs_executed_evidence", "needs_execution"}:
        return "bedc-jepa-experimentalist", "materialize_or_run_evidence"
    if kind == "needs_experiment_design" or kind == "needs_axis_evidence":
        return "bedc-jepa-planner", "design_next_research_packet"
    if kind == "needs_gate_repair_or_boundary_narrowing":
        return "bedc-jepa-gate-curator", "repair_gate_or_narrow_claim"
    if kind == "needs_adversarial_review":
        return "bedc-jepa-reviewer", "adversarial_review"
    if kind == "ready_for_paper_boundary_review" or axis == "paper":
        return "bedc-jepa-writer", "write_scoped_paper_boundary"
    return "bedc-jepa-planner", "triage_research_task"


def render_agent_prompt(task: dict[str, Any]) -> str:
    agent_id, action = _agent_for_task(task)
    lines = [
        f"Agent: {agent_id}",
        f"Action: {action}",
        f"Subject: {task.get('subject_kind')}:{task.get('subject_id')}",
        f"Axis: {task.get('axis')}",
        f"Reason: {task.get('reason')}",
        "",
        "BEDC-JEPA constraints:",
        "- The goal is research deepening of failure-aware world-model semantics.",
        "- Do not treat any single experiment as the automation target.",
        "- Keep model claims scoped to executed evidence contacts and gate results.",
        "- Negative or bounded results must become explicit research pressure, not hidden failures.",
        "- Do not write or imply real_robot_transfer, universal_failure_reader, complete_world_model, or full_planner claims.",
    ]
    if action == "design_next_research_packet":
        lines.extend(
            [
                "- Produce the smallest next hypothesis/experiment/contact packet that attacks the named axis.",
                "- Prefer tests that separate objective, representation, calibration, and allocation effects.",
            ]
        )
        if str(task.get("axis") or "") == "compute_value":
            lines.extend(
                [
                    "- Treat failure probability and allocation value as different targets.",
                    "- Define candidate compute options b explicitly, such as rollout depths, refinement, or abstention.",
                    "- Require direct marginal-value labels MV(t,b) from option-level errors; do not derive the allocation head from a failure-score ranking.",
                    "- Report allocation_delta, MV rank correlation, detection AUROC, and selective risk as separate gates.",
                ]
            )
    elif action == "materialize_or_run_evidence":
        lines.extend(
            [
                "- Use existing runners or add a deterministic runner only if the hypothesis has an evidence contact.",
                "- A runner must emit a JSON verdict payload and must fail closed when artifacts are missing.",
            ]
        )
    elif action == "write_scoped_paper_boundary":
        lines.extend(
            [
                "- Write only claims supported by authoritative findings.",
                "- Include cannot-claim boundaries before promoting model evidence into prose.",
            ]
        )
    return "\n".join(lines)


def plan_agent_tasks(tasks: list[dict[str, Any]], existing: list[dict[str, Any]] | None = None) -> list[dict[str, Any]]:
    active = {
        (str(task.get("agent_id") or ""), str(task.get("action") or ""), str(task.get("source_task_id") or ""))
        for task in (existing or [])
        if str(task.get("status") or "queued") in {"queued", "in_flight"}
    }
    out: list[dict[str, Any]] = []
    for task in tasks:
        agent_id, action = _agent_for_task(task)
        key = (agent_id, action, str(task.get("task_id") or ""))
        if key in active:
            continue
        payload = {"agent_id": agent_id, "action": action, "source_task_id": task.get("task_id")}
        out.append(
            {
                "task_id": stable_id("agent-task", payload),
                "created_at": now_iso(),
                "status": "queued",
                "agent_id": agent_id,
                "lane": str(task.get("axis") or "research"),
                "action": action,
                "priority": int(task.get("priority") or 0),
                "source_task_id": task.get("task_id"),
                "prompt": render_agent_prompt(task),
            }
        )
    out.sort(key=lambda item: (-int(item.get("priority") or 0), str(item.get("agent_id") or ""), str(item.get("task_id") or "")))
    return out


def write_dashboard(store: LeWMStore, summary: dict[str, Any], tasks: list[dict[str, Any]]) -> None:
    by_axis: dict[str, int] = {}
    by_kind: dict[str, int] = {}
    for task in tasks:
        by_axis[str(task.get("axis") or "")] = by_axis.get(str(task.get("axis") or ""), 0) + 1
        by_kind[str(task.get("task_kind") or "")] = by_kind.get(str(task.get("task_kind") or ""), 0) + 1
    lines = [
        "# BEDC-JEPA Research Loop Dashboard",
        "",
        f"Updated: {now_iso()}",
        "",
        "## Counts",
        "",
        f"- Hypotheses: `{summary['hypotheses']}`",
        f"- Experiments: `{summary['experiments']}`",
        f"- Verdicts: `{summary['verdicts']}`",
        f"- Gate results: `{summary['gate_results']}`",
        f"- Deepening tasks: `{summary['tasks']}`",
        f"- Agent tasks: `{summary['agent_tasks']}`",
        "",
        "## Tasks By Axis",
        "",
    ]
    for axis, count in sorted(by_axis.items()):
        lines.append(f"- `{axis}`: `{count}`")
    lines.extend(["", "## Tasks By Kind", ""])
    for kind, count in sorted(by_kind.items()):
        lines.append(f"- `{kind}`: `{count}`")
    lines.extend(["", "## Highest Priority", ""])
    for task in tasks[:8]:
        lines.append(f"- `{task['priority']}` `{task['axis']}` `{task['task_kind']}` {task['subject_kind']}:{task['subject_id']}")
    store.paths.lane_dashboard.parent.mkdir(parents=True, exist_ok=True)
    store.paths.lane_dashboard.write_text("\n".join(lines) + "\n", encoding="utf-8")


def run_once(store: LeWMStore) -> dict[str, Any]:
    hypotheses = store.load_hypotheses() or store.load_seed_hypotheses()
    if hypotheses and not store.load_hypotheses():
        store.write_hypotheses(hypotheses)
    experiments = store.load_experiments()
    contacts = store.load_contacts()
    verdicts = store.load_verdicts()
    gate_results = gate_all(hypotheses, experiments, contacts, verdicts)
    store.write_gate_results(gate_results)
    findings = load_research_findings(store)
    tasks = plan_deepening_tasks(hypotheses, experiments, contacts, verdicts, gate_results, findings)
    review = plan_review_queue(gate_results, tasks)
    events = dedup_by_key(store.load_events() + [_event_from_task(task) for task in tasks], "event_id")
    agent_tasks = dedup_by_key(store.load_agent_tasks() + plan_agent_tasks(tasks, store.load_agent_tasks()), "task_id")
    store.write_deepening_tasks(tasks)
    store.write_review_queue(review)
    store.write_events(events)
    store.write_agent_tasks(agent_tasks)
    summary = {
        "hypotheses": len(hypotheses),
        "experiments": len(experiments),
        "contacts": len(contacts),
        "verdicts": len(verdicts),
        "gate_results": len(gate_results),
        "tasks": len(tasks),
        "review_items": len(review),
        "events": len(events),
        "agent_tasks": len(agent_tasks),
        "blocked_gates": sum(1 for result in gate_results if result.get("gate_status") == "gate_blocked"),
    }
    write_dashboard(store, summary, tasks)
    return summary


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
            deepening_tasks=base / "state" / "deepening_tasks.jsonl",
            review_queue=base / "state" / "review_queue.jsonl",
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
                    "hypothesis_id": "fi-test.allocation",
                    "predicate": "allocation score improves budget split",
                    "failure_surface": "allocation_delta",
                    "horizon": {"steps": [1, 3]},
                    "perturbation_family": "tail allocation",
                    "carrier": "fixture.npz",
                    "criterion": {"kind": "delta_ci_below_zero", "metric": "allocation_delta"},
                    "reality_contact_refs": ["fixture.contact"],
                    "status": "open",
                },
                {
                    "hypothesis_id": "fi-test.selective",
                    "predicate": "selective admission controls risk",
                    "failure_surface": "risk_margin",
                    "horizon": {"steps": [1]},
                    "perturbation_family": "selective calibration",
                    "carrier": "fixture.npz",
                    "criterion": {"kind": "delta_ci_above_zero", "metric": "risk_margin"},
                    "reality_contact_refs": ["fixture.contact"],
                    "status": "open",
                },
                {
                    "hypothesis_id": "fi-test.compute-value",
                    "predicate": "option-conditioned marginal compute value predicts useful rollout choices",
                    "failure_surface": "compute-value MV(t,b)",
                    "horizon": {"steps": [1, 3]},
                    "perturbation_family": "marginal intervention value",
                    "carrier": "fixture.npz",
                    "criterion": {"kind": "delta_ci_below_zero", "metric": "allocation_delta"},
                    "reality_contact_refs": ["fixture.contact"],
                    "status": "open",
                },
            ],
        )
        store = LeWMStore(paths)
        summary = run_once(store)
        tasks = store.load_deepening_tasks()
        agent_tasks = store.load_agent_tasks()
        if summary["tasks"] == 0 or not any(task.get("task_kind") == "needs_reality_contact" for task in tasks):
            print(json.dumps({"summary": summary, "tasks": tasks}, indent=2), file=sys.stderr)
            return 1
        if not any(task.get("agent_id") == "bedc-jepa-experimentalist" for task in agent_tasks):
            print(json.dumps(agent_tasks, indent=2), file=sys.stderr)
            return 1
        if not any(task.get("lane") == "compute_value" and "MV(t,b)" in str(task.get("prompt") or "") for task in agent_tasks):
            print(json.dumps(agent_tasks, indent=2), file=sys.stderr)
            return 1
        if not paths.lane_dashboard.exists():
            print("missing dashboard", file=sys.stderr)
            return 1
    print("[bedc-jepa-research-loop] self-test ok")
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Run one BEDC-JEPA research-deepening cycle")
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args(argv)
    if args.self_test:
        return self_test()
    summary = run_once(LeWMStore())
    print(
        "[bedc-jepa-research-loop] "
        f"hypotheses={summary['hypotheses']} experiments={summary['experiments']} "
        f"verdicts={summary['verdicts']} tasks={summary['tasks']} "
        f"agent_tasks={summary['agent_tasks']} blocked_gates={summary['blocked_gates']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
