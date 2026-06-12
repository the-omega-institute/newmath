#!/usr/bin/env python3
"""评估小鼠体内 senescence/SASP marker 方向证据。"""

from __future__ import annotations

import csv
import json
import math
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
CELLSTATE_ROOT = REPO_ROOT / "tools" / "cellstate_reality"
DATA_PATH = CELLSTATE_ROOT / "data" / "gse190665_function_signature_inputs.json"
OUT_DIR = CELLSTATE_ROOT / "out"
EXPERIMENT_ID = "gse190665-function-signature"
CLAIM_ID = "cellstate.function-signature-shift.gse190665"
CONTACT_ID = "k-f.gse190665-invivo-mouse"
CONJECTURE_ID = "function-signature-shift.gse190665"
PROBE_ID = "function-signature-shift.gse190665"
MIN_N_PER_GROUP = 3
SENESCENCE = ["Cdkn2a", "Cdkn1a", "Trp53", "Glb1", "Serpine1"]
SASP = ["Il6", "Il1a", "Il1b", "Cxcl1", "Cxcl2", "Mmp3", "Mmp12", "Tnf", "Ccl2"]


def now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def load_inputs() -> dict[str, Any]:
    return json.loads(DATA_PATH.read_text(encoding="utf-8"))


def mean(values: list[float]) -> float:
    return sum(values) / float(len(values)) if values else float("nan")


def finite(value: float) -> bool:
    return not math.isnan(value) and not math.isinf(value)


def check(name: str, passed: bool, reason: str, value: Any | None = None) -> dict[str, Any]:
    item: dict[str, Any] = {"name": name, "passed": bool(passed), "reason": reason}
    if value is not None:
        item["value"] = value
    return item


def group_values(expression: dict[str, dict[str, float]], marker: str, samples: list[str]) -> list[float]:
    values = expression.get(marker, {})
    return [float(values[sample]) for sample in samples if sample in values and finite(float(values[sample]))]


def panel_delta(expression: dict[str, dict[str, float]], markers: list[str], treated: list[str], control: list[str]) -> tuple[float, list[dict[str, Any]]]:
    marker_rows: list[dict[str, Any]] = []
    deltas: list[float] = []
    for marker in markers:
        treated_values = group_values(expression, marker, treated)
        control_values = group_values(expression, marker, control)
        if not treated_values or not control_values:
            marker_rows.append({"marker": marker, "covered": False})
            continue
        delta = mean(treated_values) - mean(control_values)
        marker_rows.append(
            {
                "marker": marker,
                "covered": True,
                "treated_mean_log2_cpm": mean(treated_values),
                "control_mean_log2_cpm": mean(control_values),
                "delta_treated_minus_control": delta,
                "treated_n": len(treated_values),
                "control_n": len(control_values),
            }
        )
        deltas.append(delta)
    return mean(deltas), marker_rows


def comparisons(payload: dict[str, Any]) -> list[dict[str, Any]]:
    samples = [item for item in payload.get("samples", []) if isinstance(item, dict)]
    expression_by_accession = payload.get("expression_log2_cpm", {})
    specs = payload.get("rna_subseries", {})
    rows: list[dict[str, Any]] = []
    keys = sorted({(str(s["accession"]), str(s["tissue"])) for s in samples if s.get("group") in {"reprogrammed", "control"}})
    for accession, tissue in keys:
        tissue_samples = [s for s in samples if str(s.get("accession")) == accession and str(s.get("tissue")) == tissue]
        treated = sorted(str(s["sample"]) for s in tissue_samples if s.get("group") == "reprogrammed")
        control = sorted(str(s["sample"]) for s in tissue_samples if s.get("group") == "control")
        expression = expression_by_accession.get(accession, {})
        if not isinstance(expression, dict):
            expression = {}
        delta_sen, sen_markers = panel_delta(expression, SENESCENCE, treated, control)
        delta_sasp, sasp_markers = panel_delta(expression, SASP, treated, control)
        n_ok = len(treated) >= MIN_N_PER_GROUP and len(control) >= MIN_N_PER_GROUP
        row = {
            "accession": accession,
            "tissue": tissue,
            "duration": specs.get(accession, {}).get("duration") if isinstance(specs, dict) else "",
            "age_at_endpoint_months": specs.get(accession, {}).get("age_at_endpoint_months") if isinstance(specs, dict) else None,
            "treated_n": len(treated),
            "control_n": len(control),
            "treated_samples": treated,
            "control_samples": control,
            "n_ok": n_ok,
            "delta_senescence": delta_sen,
            "delta_sasp_inflammation": delta_sasp,
            "direction_support": n_ok and delta_sen < 0.0 and delta_sasp < 0.0,
            "senescence_markers": sen_markers,
            "sasp_inflammation_markers": sasp_markers,
        }
        rows.append(row)
    return rows


def write_csv(path: Path, rows: list[dict[str, Any]]) -> None:
    fields = [
        "accession",
        "tissue",
        "duration",
        "age_at_endpoint_months",
        "treated_n",
        "control_n",
        "n_ok",
        "delta_senescence",
        "delta_sasp_inflammation",
        "direction_support",
    ]
    with path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=fields)
        writer.writeheader()
        for row in rows:
            writer.writerow({field: row.get(field, "") for field in fields})


def main() -> int:
    started_at = now_iso()
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    payload = load_inputs()
    rows = comparisons(payload)
    valid_rows = [row for row in rows if row["n_ok"]]
    supported_rows = [row for row in valid_rows if row["direction_support"]]
    aggregate_delta_sen = mean([float(row["delta_senescence"]) for row in valid_rows])
    aggregate_delta_sasp = mean([float(row["delta_sasp_inflammation"]) for row in valid_rows])
    all_valid_support = bool(valid_rows) and len(valid_rows) == len(supported_rows)
    aggregate_support = bool(valid_rows) and aggregate_delta_sen < 0.0 and aggregate_delta_sasp < 0.0
    marker_coverage = len(payload.get("marker_gene_ids", {}))
    marker_total = len(SENESCENCE) + len(SASP)
    missing_markers = payload.get("missing_markers", [])
    broad_support = all_valid_support and aggregate_support
    partial = aggregate_support and not all_valid_support

    checks = [
        check(
            "input.available",
            DATA_PATH.exists(),
            "Curated mouse RNA-seq marker input must exist.",
            {"data_path": str(DATA_PATH.relative_to(REPO_ROOT))},
        ),
        check(
            "marker.panel.coverage",
            marker_coverage == marker_total and not missing_markers,
            "All predeclared mouse senescence/SASP markers must map to Ensembl gene ids.",
            {"covered": marker_coverage, "total": marker_total, "missing": missing_markers},
        ),
        check(
            "age-matched.sample.structure",
            bool(valid_rows) and all(row["n_ok"] for row in valid_rows),
            "Every evaluated OSKM/control tissue scope must have at least three samples per group.",
            {"valid_scope_count": len(valid_rows), "min_n_per_group": MIN_N_PER_GROUP},
        ),
        check(
            "mean.delta.senescence.negative",
            aggregate_delta_sen < 0.0,
            "Aggregate treated-minus-control senescence marker delta must be negative.",
            {"aggregate_delta_senescence": aggregate_delta_sen},
        ),
        check(
            "mean.delta.sasp.negative",
            aggregate_delta_sasp < 0.0,
            "Aggregate treated-minus-control SASP/inflammation marker delta must be negative.",
            {"aggregate_delta_sasp_inflammation": aggregate_delta_sasp},
        ),
        check(
            "finite-scope.direction.consistency",
            broad_support,
            "Broad FunctionSignatureShift support requires every valid accession/tissue scope to satisfy both negative panel directions.",
            {"valid_scope_count": len(valid_rows), "supported_scope_count": len(supported_rows), "partial_aggregate_support": partial},
        ),
        check(
            "function-assay.boundary",
            True,
            "RNA marker direction is not a direct functional assay and cannot establish functional rejuvenation.",
            {"direct_functional_assay": False, "organism": "mouse", "human_scope_merge": False},
        ),
    ]
    status = "passed" if broad_support else "needs_data"
    verdict = "FunctionSignatureShiftUp_support" if broad_support else "partial_direction_or_needs_data"

    certificate = {
        "experiment_id": EXPERIMENT_ID,
        "claim_id": CLAIM_ID,
        "conjecture_id": CONJECTURE_ID,
        "probe_id": PROBE_ID,
        "contact_id": CONTACT_ID,
        "started_at": started_at,
        "completed_at": now_iso(),
        "support": broad_support,
        "partial_direction_support": partial,
        "verdict": verdict,
        "summary": {
            "valid_scope_count": len(valid_rows),
            "supported_scope_count": len(supported_rows),
            "aggregate_delta_senescence": aggregate_delta_sen,
            "aggregate_delta_sasp_inflammation": aggregate_delta_sasp,
            "min_n_per_group": MIN_N_PER_GROUP,
            "marker_coverage": marker_coverage,
            "marker_total": marker_total,
            "missing_markers": missing_markers,
        },
        "comparisons": rows,
        "checks": checks,
        "cannot_claim": [
            "Senescence/SASP marker direction is not a direct collagen, wound, organ-function, or organismal functional assay.",
            "Mouse in-vivo RNA-seq evidence cannot be generalized to human or merged with the human GSE142439 AgeClockShift scope.",
            "This packet does not establish IdentityPreservingAgeResetUp, RejuvenationUp, RenewableMaintenanceUp, or ImmortalityPotentialUp.",
            "This task does not score a mouse methylation clock and does not apply a human Horvath353 clock to mouse data.",
        ],
    }
    certificate_path = OUT_DIR / "gse190665_function_signature_certificate.json"
    csv_path = OUT_DIR / "gse190665_function_signature_comparisons.csv"
    certificate_path.write_text(json.dumps(certificate, ensure_ascii=False, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    write_csv(csv_path, rows)
    print(
        json.dumps(
            {
                "status": status,
                "checks": checks,
                "result": {
                    "experiment_id": EXPERIMENT_ID,
                    "claim_id": CLAIM_ID,
                    "support": broad_support,
                    "partial_direction_support": partial,
                    "verdict": verdict,
                    "aggregate_delta_senescence": aggregate_delta_sen,
                    "aggregate_delta_sasp_inflammation": aggregate_delta_sasp,
                    "valid_scope_count": len(valid_rows),
                    "supported_scope_count": len(supported_rows),
                    "certificate_path": str(certificate_path.relative_to(REPO_ROOT)),
                    "comparison_csv": str(csv_path.relative_to(REPO_ROOT)),
                    "scope_boundary": "mouse in-vivo RNA marker proxy only; not a direct functional assay or human scope",
                },
            },
            ensure_ascii=False,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
