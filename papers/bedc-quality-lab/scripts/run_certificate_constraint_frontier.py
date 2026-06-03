#!/usr/bin/env python3
"""Project certificate-guided records onto explicit constraint frontiers."""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import json
import math
from pathlib import Path
import sys
from typing import Any, Iterable, Sequence

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.claim_terms import FORBIDDEN_POSITIVE_CLAIM_TERMS


SOURCE_JSON_ARTIFACT = "reports/certificate_guided_training.json"
SOURCE_REPORT_ARTIFACT = "reports/certificate_guided_training.md"
JSON_ARTIFACT = "reports/certificate_constraint_frontier.json"
REPORT_ARTIFACT = "reports/certificate_constraint_frontier.md"
LOCAL_SCHEMA_ID = "bedc-quality-lab:certificate-constraint-frontier-sidecar"
PROJECTION_SCRIPT = "scripts/run_certificate_constraint_frontier.py"

REQUIRED_TOP_LEVEL_FIELDS = (
    "records",
    "deltas",
    "claim_gate",
    "hardgate",
    "paired_delta_ci",
    "arm_protocol",
)
REQUIRED_RECORD_FIELDS = (
    "arm",
    "role",
    "candidate_id",
    "performance",
    "unlogged_error_rate",
    "quality_benefit",
    "quality_debt",
    "quality_q",
)
NOT_CLAIMED = (
    "formal BEDC closure is not claimed by this sidecar",
    "global optimizer behavior is not claimed by this sidecar",
    "universal certificate-guided improvement is not claimed by this sidecar",
    "positive discovery is not claimed for a debt-down benefit-down tradeoff",
    "schema or canonical report status is not claimed by this sidecar",
)


def _mean(values: Iterable[float]) -> float:
    items = [float(value) for value in values]
    if not items:
        raise ValueError("cannot compute mean of an empty sequence")
    return float(math.fsum(items) / len(items))


def _quantile(values: Sequence[float], q: float) -> float:
    if not values:
        raise ValueError("cannot compute quantile of an empty sequence")
    ordered = sorted(float(value) for value in values)
    if len(ordered) == 1:
        return ordered[0]
    position = (len(ordered) - 1) * float(q)
    lo = math.floor(position)
    hi = math.ceil(position)
    if lo == hi:
        return ordered[int(position)]
    weight = position - lo
    return float(ordered[lo] * (1.0 - weight) + ordered[hi] * weight)


def _unique_thresholds(items: Iterable[dict[str, Any]]) -> list[dict[str, Any]]:
    seen: set[tuple[str, float]] = set()
    result: list[dict[str, Any]] = []
    for item in items:
        value = round(float(item["value"]), 12)
        key = (str(item["source"]), value)
        if key in seen:
            continue
        seen.add(key)
        result.append({**item, "value": value})
    return sorted(result, key=lambda item: (float(item["value"]), str(item["source"])))


def _load_source(root: Path) -> dict[str, Any]:
    path = root / SOURCE_JSON_ARTIFACT
    payload = json.loads(path.read_text(encoding="utf-8"))
    missing = [field for field in REQUIRED_TOP_LEVEL_FIELDS if field not in payload]
    if missing:
        raise ValueError(f"source payload missing required fields: {', '.join(missing)}")
    if not isinstance(payload["records"], list) or not payload["records"]:
        raise ValueError("source payload records must be a non-empty list")
    for index, record in enumerate(payload["records"]):
        missing_record_fields = [field for field in REQUIRED_RECORD_FIELDS if field not in record]
        if missing_record_fields:
            raise ValueError(
                f"source record {index} missing required fields: {', '.join(missing_record_fields)}"
            )
        performance = record["performance"]
        if not isinstance(performance, dict) or "task_loss" not in performance:
            raise ValueError(f"source record {index} missing performance.task_loss")
    return payload


def _arm_means(records: list[dict[str, Any]]) -> list[dict[str, Any]]:
    order: list[str] = []
    grouped: dict[str, list[dict[str, Any]]] = {}
    for record in records:
        arm = str(record["arm"])
        if arm not in grouped:
            order.append(arm)
            grouped[arm] = []
        grouped[arm].append(record)

    summaries = []
    for arm in order:
        rows = grouped[arm]
        first = rows[0]
        summaries.append(
            {
                "arm": arm,
                "role": str(first.get("role", "")),
                "candidate_id": str(first.get("candidate_id", "")),
                "record_count": len(rows),
                "task_loss": _mean(float(row["performance"]["task_loss"]) for row in rows),
                "unlogged_error_rate": _mean(float(row["unlogged_error_rate"]) for row in rows),
                "quality_benefit": _mean(float(row["quality_benefit"]) for row in rows),
                "quality_debt": _mean(float(row["quality_debt"]) for row in rows),
                "quality_q": _mean(float(row["quality_q"]) for row in rows),
            }
        )
    return summaries


def _baseline_arm(source: dict[str, Any], summaries: list[dict[str, Any]]) -> str:
    arm_protocol = source.get("arm_protocol", {})
    main_pair = arm_protocol.get("main_pair") if isinstance(arm_protocol, dict) else None
    if isinstance(main_pair, list) and main_pair:
        return str(main_pair[0])
    for summary in summaries:
        if summary["role"] in {"before", "baseline", "reference"} or summary["arm"] == "baseline":
            return str(summary["arm"])
    return str(summaries[0]["arm"])


def _threshold_grid(summaries: list[dict[str, Any]], baseline_arm: str) -> list[dict[str, Any]]:
    baseline = next(summary for summary in summaries if summary["arm"] == baseline_arm)
    candidates = [summary for summary in summaries if summary["arm"] != baseline_arm] or summaries
    uer_values = [float(summary["unlogged_error_rate"]) for summary in summaries]
    benefit_values = [float(summary["quality_benefit"]) for summary in candidates]
    debt_values = [float(summary["quality_debt"]) for summary in candidates]

    alpha_values = _unique_thresholds(
        {
            "axis": "alpha",
            "value": _quantile(uer_values, q),
            "source": f"observed_uer_quantile_{q:g}",
            "source_pointer": "$.records[*].unlogged_error_rate",
        }
        for q in (0.0, 0.25, 0.5, 0.75, 1.0)
    )
    beta_values = _unique_thresholds(
        [
            {
                "axis": "beta",
                "value": float(baseline["quality_benefit"]),
                "source": "baseline_mean_benefit",
                "source_pointer": "$.records[arm=baseline].quality_benefit",
            },
            {
                "axis": "beta",
                "value": min(benefit_values),
                "source": "candidate_min_mean_benefit",
                "source_pointer": "$.records[arm!=baseline].quality_benefit",
            },
            {
                "axis": "beta",
                "value": _quantile(benefit_values, 0.5),
                "source": "candidate_median_mean_benefit",
                "source_pointer": "$.records[arm!=baseline].quality_benefit",
            },
            {
                "axis": "beta",
                "value": max(benefit_values),
                "source": "candidate_max_mean_benefit",
                "source_pointer": "$.records[arm!=baseline].quality_benefit",
            },
        ]
    )
    gamma_values = _unique_thresholds(
        [
            {
                "axis": "gamma",
                "value": float(baseline["quality_debt"]),
                "source": "baseline_mean_debt",
                "source_pointer": "$.records[arm=baseline].quality_debt",
            },
            {
                "axis": "gamma",
                "value": min(debt_values),
                "source": "candidate_min_mean_debt",
                "source_pointer": "$.records[arm!=baseline].quality_debt",
            },
            {
                "axis": "gamma",
                "value": _quantile(debt_values, 0.5),
                "source": "candidate_median_mean_debt",
                "source_pointer": "$.records[arm!=baseline].quality_debt",
            },
            {
                "axis": "gamma",
                "value": max(debt_values),
                "source": "candidate_max_mean_debt",
                "source_pointer": "$.records[arm!=baseline].quality_debt",
            },
        ]
    )

    triples = []
    for index, alpha in enumerate(alpha_values):
        for beta in beta_values:
            for gamma in gamma_values:
                triples.append(
                    {
                        "threshold_id": f"ccf-{index:03d}-{len(triples):03d}",
                        "alpha": float(alpha["value"]),
                        "beta": float(beta["value"]),
                        "gamma": float(gamma["value"]),
                        "alpha_source": alpha,
                        "beta_source": beta,
                        "gamma_source": gamma,
                        "constraint": "min task_loss subject to UER<=alpha, Benefit>=beta, Debt<=gamma",
                    }
                )
    return triples


def _constraint_rows(
    summaries: list[dict[str, Any]],
    threshold_grid: list[dict[str, Any]],
) -> list[dict[str, Any]]:
    rows = []
    for threshold in threshold_grid:
        for summary in summaries:
            uer_ok = float(summary["unlogged_error_rate"]) <= float(threshold["alpha"])
            benefit_ok = float(summary["quality_benefit"]) >= float(threshold["beta"])
            debt_ok = float(summary["quality_debt"]) <= float(threshold["gamma"])
            feasible = uer_ok and benefit_ok and debt_ok
            rows.append(
                {
                    "threshold_id": threshold["threshold_id"],
                    "arm": summary["arm"],
                    "role": summary["role"],
                    "candidate_id": summary["candidate_id"],
                    "record_count": summary["record_count"],
                    "alpha": threshold["alpha"],
                    "beta": threshold["beta"],
                    "gamma": threshold["gamma"],
                    "unlogged_error_rate": summary["unlogged_error_rate"],
                    "quality_benefit": summary["quality_benefit"],
                    "quality_debt": summary["quality_debt"],
                    "quality_q": summary["quality_q"],
                    "uer_ok": bool(uer_ok),
                    "benefit_ok": bool(benefit_ok),
                    "debt_ok": bool(debt_ok),
                    "feasible": bool(feasible),
                    "task_loss": summary["task_loss"],
                    "evidence_status": (
                        "constraint-satisfied local candidate" if feasible else "non-positive"
                    ),
                    "positive": False,
                }
            )
    return rows


def _frontier(
    threshold_grid: list[dict[str, Any]],
    constraint_rows: list[dict[str, Any]],
    positive_pointer_allowed: bool,
) -> list[dict[str, Any]]:
    rows_by_threshold: dict[str, list[dict[str, Any]]] = {}
    for row in constraint_rows:
        rows_by_threshold.setdefault(str(row["threshold_id"]), []).append(row)
    cells = []
    for threshold in threshold_grid:
        threshold_id = str(threshold["threshold_id"])
        feasible = [row for row in rows_by_threshold.get(threshold_id, []) if row["feasible"]]
        if not feasible:
            cells.append(
                {
                    "threshold_id": threshold_id,
                    "alpha": threshold["alpha"],
                    "beta": threshold["beta"],
                    "gamma": threshold["gamma"],
                    "status": "infeasible",
                    "verdict": "rejected",
                    "discovery_level": "DN",
                    "positive": False,
                    "candidate": None,
                }
            )
            continue
        selected = min(feasible, key=lambda row: (float(row["task_loss"]), str(row["arm"])))
        cells.append(
            {
                "threshold_id": threshold_id,
                "alpha": threshold["alpha"],
                "beta": threshold["beta"],
                "gamma": threshold["gamma"],
                "status": "constraint-satisfied local candidate",
                "verdict": "accepted-local-candidate",
                "discovery_level": "D1" if positive_pointer_allowed else "DN",
                "positive": bool(positive_pointer_allowed),
                "candidate": {
                    "arm": selected["arm"],
                    "role": selected["role"],
                    "candidate_id": selected["candidate_id"],
                    "task_loss": selected["task_loss"],
                    "unlogged_error_rate": selected["unlogged_error_rate"],
                    "quality_benefit": selected["quality_benefit"],
                    "quality_debt": selected["quality_debt"],
                    "row_pointer": f"$.constraint_rows[threshold_id={threshold_id},arm={selected['arm']}]",
                },
                "tie_break": "minimum task_loss among feasible arms; arm name lexical order breaks equal task_loss",
            }
        )
    return cells


def _dominance(summaries: list[dict[str, Any]], baseline_arm: str) -> list[dict[str, Any]]:
    baseline = next(summary for summary in summaries if summary["arm"] == baseline_arm)
    rows = []
    for summary in summaries:
        rows.append(
            {
                "arm": summary["arm"],
                "role": summary["role"],
                "candidate_id": summary["candidate_id"],
                "baseline_arm": baseline_arm,
                "task_loss_delta": float(summary["task_loss"] - baseline["task_loss"]),
                "uer_delta": float(summary["unlogged_error_rate"] - baseline["unlogged_error_rate"]),
                "benefit_delta": float(summary["quality_benefit"] - baseline["quality_benefit"]),
                "debt_delta": float(summary["quality_debt"] - baseline["quality_debt"]),
                "quality_q_delta": float(summary["quality_q"] - baseline["quality_q"]),
                "debt_down": bool(summary["quality_debt"] < baseline["quality_debt"]),
                "benefit_down": bool(summary["quality_benefit"] < baseline["quality_benefit"]),
                "positive": False,
            }
        )
    return rows


def _ci_gate(source: dict[str, Any]) -> dict[str, Any]:
    paired = source.get("paired_delta_ci", {})
    after = paired.get("after_minus_before", {}) if isinstance(paired, dict) else {}
    quality = after.get("quality_q_delta", {}) if isinstance(after, dict) else {}
    status = quality.get("status")
    ci_low = quality.get("ci95_low")
    return {
        "paired_ci_status": status,
        "quality_q_ci95_low": ci_low,
        "paired_ci_pass": bool(status == "ok" and ci_low is not None and float(ci_low) > 0.0),
        "source_pointer": "$.paired_delta_ci.after_minus_before.quality_q_delta",
    }


def _positive_pointer_allowed(source: dict[str, Any]) -> tuple[bool, dict[str, Any]]:
    claim_gate = source.get("claim_gate", {})
    ci_gate = _ci_gate(source)
    training_positive = bool(
        isinstance(claim_gate, dict)
        and (
            claim_gate.get("positive_quality_improvement") is True
            or claim_gate.get("positive_discovery_four_gate") is True
        )
    )
    net_information = source.get("net_information")
    net_information_pass = bool(net_information is not None and float(net_information) > 0.0)
    allowed = bool(training_positive and ci_gate["paired_ci_pass"] and net_information_pass)
    return allowed, {
        "training_positive_gate": training_positive,
        "training_positive_gate_pointer": "$.claim_gate.positive_quality_improvement",
        "paired_ci_pass": ci_gate["paired_ci_pass"],
        "paired_ci_pointer": ci_gate["source_pointer"],
        "net_information_available": net_information is not None,
        "net_information_pass": net_information_pass,
        "net_information_pointer": "$.net_information",
        "positive_pointer_allowed": allowed,
    }


def _hardgate(
    source: dict[str, Any],
    frontier: list[dict[str, Any]],
    constraint_rows: list[dict[str, Any]],
    positive_gate: dict[str, Any],
) -> dict[str, Any]:
    source_hardgate = source.get("hardgate", {})
    source_basis = source_hardgate.get("basis", {}) if isinstance(source_hardgate, dict) else {}
    debt_delta = source_basis.get("debt_delta")
    benefit_delta = source_basis.get("benefit_delta")
    if debt_delta is None or benefit_delta is None:
        deltas = source.get("deltas", {})
        main = (
            deltas.get("debt_plus_benefit_minus_baseline")
            or deltas.get("after_minus_before")
            or {}
        )
        debt_delta = main.get("debt_delta")
        benefit_delta = main.get("benefit_delta")
    tradeoff = bool(
        debt_delta is not None
        and benefit_delta is not None
        and float(debt_delta) < 0.0
        and float(benefit_delta) < 0.0
    )
    any_feasible = any(cell["status"] != "infeasible" for cell in frontier)
    any_constraint_violation = any(
        row["feasible"] is False and (row["benefit_ok"] is False or row["debt_ok"] is False)
        for row in constraint_rows
    )
    blockers: list[str] = []
    if tradeoff:
        blockers.append("audit-improvement-tradeoff")
    if not any_feasible:
        blockers.append("no-feasible-constraint-cell")
    if any_constraint_violation:
        blockers.append("benefit-or-debt-constraint-not-satisfied-for-some-cells")
    if not positive_gate["positive_pointer_allowed"]:
        blockers.append("positive-pointer-gate-not-satisfied")
    status = "non-positive"
    failed_gate = "audit-improvement-tradeoff" if tradeoff else None
    if not any_feasible:
        status = "rejected"
        failed_gate = failed_gate or "no-feasible-constraint-cell"
    return {
        "status": status,
        "positive": False,
        "failed_gate": failed_gate,
        "discovery_level": "DN" if failed_gate else "D1",
        "source_hardgate_pointer": "$.hardgate",
        "source_failed_gate": source.get("failed_gate"),
        "basis": {
            "debt_delta": None if debt_delta is None else float(debt_delta),
            "benefit_delta": None if benefit_delta is None else float(benefit_delta),
            "audit_improvement_tradeoff": tradeoff,
            "feasible_frontier_cell_count": sum(
                1 for cell in frontier if cell["status"] != "infeasible"
            ),
            "constraint_row_count": len(constraint_rows),
            "positive_pointer_gate": positive_gate,
        },
        "gates": {
            "HG-CCF-1": {
                "status": "fail" if tradeoff else "pass",
                "failed_gate": "audit-improvement-tradeoff" if tradeoff else None,
                "positive": False,
                "discovery_level_bound": "DN_or_D1",
            },
            "HG-CCF-2": {
                "status": "pass" if any_feasible else "not-applicable",
                "candidate_status": "constraint-satisfied local candidate",
                "positive_requires": (
                    "source certificate-guided positive gate, net information, and paired CI"
                ),
                "positive_pointer_allowed": bool(positive_gate["positive_pointer_allowed"]),
            },
            "HG-CCF-3": {
                "status": "pass" if any_feasible else "fail",
                "no_feasible_verdict": "rejected",
                "no_feasible_discovery_level": "DN",
            },
            "HG-CCF-4": {
                "status": "fail" if any_constraint_violation else "pass",
                "failed_rows_are": "non-positive",
            },
            "HG-CCF-5": {
                "status": "pass",
                "hidden_weight": False,
                "combined_quality_metric": False,
                "selection_rule": "constraint satisfaction plus task_loss tie-break",
            },
            "HG-CCF-6": {
                "status": "pass",
                "canonical_status": "sidecar_not_canonical",
                "local_schema_id": LOCAL_SCHEMA_ID,
                "shared_schema_id_reused": False,
                "forbidden_positive_claim_term_hits": [],
            },
        },
        "blockers": blockers,
    }


def build_payload(source: dict[str, Any], *, generated_at: str | None = None) -> dict[str, Any]:
    summaries = _arm_means(source["records"])
    baseline = _baseline_arm(source, summaries)
    threshold_grid = _threshold_grid(summaries, baseline)
    constraint_rows = _constraint_rows(summaries, threshold_grid)
    positive_allowed, positive_gate = _positive_pointer_allowed(source)
    frontier = _frontier(threshold_grid, constraint_rows, positive_allowed)
    dominance = _dominance(summaries, baseline)
    hardgate = _hardgate(source, frontier, constraint_rows, positive_gate)
    generated = generated_at or datetime.now(timezone.utc).isoformat()
    payload = {
        "schema_id": LOCAL_SCHEMA_ID,
        "artifact": JSON_ARTIFACT,
        "report": REPORT_ARTIFACT,
        "generated_at": generated,
        "projection_script": PROJECTION_SCRIPT,
        "source_artifacts": {
            "source_json_artifact": SOURCE_JSON_ARTIFACT,
            "source_report_artifact": SOURCE_REPORT_ARTIFACT,
            "source_generation_script": source.get("source_artifacts", {}).get("generation_script"),
        },
        "sidecar_role": "pointer_only_non_canonical",
        "canonical_status": "sidecar_not_canonical",
        "input_contract": {
            "records_task_loss": "$.records[*].performance.task_loss",
            "records_unlogged_error_rate": "$.records[*].unlogged_error_rate",
            "records_quality_benefit": "$.records[*].quality_benefit",
            "records_quality_debt": "$.records[*].quality_debt",
            "records_quality_q": "$.records[*].quality_q",
            "deltas": "$.deltas",
            "claim_gate": "$.claim_gate",
            "hardgate": "$.hardgate",
            "paired_delta_ci": "$.paired_delta_ci",
            "arm_protocol": "$.arm_protocol",
        },
        "constraint_form": "min task_loss subject to UER<=alpha, Benefit>=beta, Debt<=gamma",
        "threshold_source_policy": {
            "alpha": "observed UER quantiles from arm means",
            "beta": "baseline benefit and candidate benefit bands from arm means",
            "gamma": "baseline debt and candidate debt bands from arm means",
            "lambda_weight_source": "$.lambda_weights",
            "cost_weight_source": "$.cost_protocol",
            "hidden_weight": False,
            "combined_quality_metric": False,
        },
        "baseline_arm": baseline,
        "arm_means": summaries,
        "threshold_grid": threshold_grid,
        "constraint_rows": constraint_rows,
        "frontier": frontier,
        "dominance": dominance,
        "hardgate": hardgate,
        "source_gate_pointers": {
            "claim_gate": "$.claim_gate",
            "hardgate": "$.hardgate",
            "paired_delta_ci": "$.paired_delta_ci",
            "deltas": "$.deltas",
        },
        "not_claimed": list(NOT_CLAIMED),
    }
    text = json.dumps(payload, sort_keys=True).lower()
    hits = [term for term in FORBIDDEN_POSITIVE_CLAIM_TERMS if term.lower() in text]
    payload["hardgate"]["gates"]["HG-CCF-6"]["forbidden_positive_claim_term_hits"] = hits
    if hits:
        payload["hardgate"]["status"] = "rejected"
        payload["hardgate"]["failed_gate"] = payload["hardgate"]["failed_gate"] or "forbidden-positive-claim-term"
        payload["hardgate"]["blockers"].append("forbidden-positive-claim-term")
    return payload


def _format_float(value: Any) -> str:
    return f"{float(value):.6f}"


def _render_markdown(payload: dict[str, Any]) -> str:
    hardgate = payload["hardgate"]
    feasible_count = hardgate["basis"]["feasible_frontier_cell_count"]
    lines = [
        "# Certificate Constraint Frontier",
        "",
        f"- Source JSON artifact: `{payload['source_artifacts']['source_json_artifact']}`",
        f"- Projection script: `{payload['projection_script']}`",
        f"- Local schema id: `{payload['schema_id']}`",
        f"- Sidecar role: `{payload['sidecar_role']}`",
        f"- Canonical status: `{payload['canonical_status']}`",
        f"- Constraint form: `{payload['constraint_form']}`",
        f"- Hardgate status: `{hardgate['status']}`",
        f"- Failed gate: `{hardgate['failed_gate'] or 'none'}`",
        f"- Positive pointer: `{str(bool(hardgate['positive'])).lower()}`",
        f"- Feasible frontier cells: `{feasible_count}`",
        f"- Not claimed: `{'; '.join(payload['not_claimed'])}`",
        "",
        "## Threshold Sources",
        "",
        "- Alpha: observed UER quantiles from `$.records[*].unlogged_error_rate`.",
        "- Beta: baseline benefit plus candidate benefit bands from `$.records[*].quality_benefit`.",
        "- Gamma: baseline debt plus candidate debt bands from `$.records[*].quality_debt`.",
        "- No hidden cost weight, total score, rank, or grade is produced.",
        "",
        "## Frontier Preview",
        "",
        "| threshold | alpha | beta | gamma | status | candidate | task_loss |",
        "| --- | ---: | ---: | ---: | --- | --- | ---: |",
    ]
    for cell in payload["frontier"][:12]:
        candidate = cell["candidate"] or {}
        lines.append(
            "| `{}` | {} | {} | {} | `{}` | `{}` | {} |".format(
                cell["threshold_id"],
                _format_float(cell["alpha"]),
                _format_float(cell["beta"]),
                _format_float(cell["gamma"]),
                cell["status"],
                candidate.get("arm", "none"),
                _format_float(candidate.get("task_loss", math.nan))
                if candidate
                else "`none`",
            )
        )
    lines.extend(
        [
            "",
            "## Dominance",
            "",
            "| arm | task_loss_delta | uer_delta | benefit_delta | debt_delta | positive |",
            "| --- | ---: | ---: | ---: | ---: | --- |",
        ]
    )
    for row in payload["dominance"]:
        lines.append(
            "| `{}` | {} | {} | {} | {} | `{}` |".format(
                row["arm"],
                _format_float(row["task_loss_delta"]),
                _format_float(row["uer_delta"]),
                _format_float(row["benefit_delta"]),
                _format_float(row["debt_delta"]),
                str(bool(row["positive"])).lower(),
            )
        )
    lines.extend(
        [
            "",
            "## HG-CCF",
            "",
        ]
    )
    for gate, result in hardgate["gates"].items():
        lines.append(f"- {gate}: `{result['status']}`")
    lines.append("")
    return "\n".join(lines)


def write_payload(payload: dict[str, Any], root: Path) -> None:
    json_path = root / JSON_ARTIFACT
    report_path = root / REPORT_ARTIFACT
    json_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    report_path.write_text(_render_markdown(payload), encoding="utf-8")


def main(argv: Sequence[str] | None = None) -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    args = parser.parse_args(argv)
    root = args.root.resolve()
    source = _load_source(root)
    payload = build_payload(source)
    write_payload(payload, root)
    print(f"wrote {JSON_ARTIFACT}")
    print(f"wrote {REPORT_ARTIFACT}")
    print(f"frontier_cells {len(payload['frontier'])}")
    print(f"hardgate {payload['hardgate']['status']}")


if __name__ == "__main__":
    main()
