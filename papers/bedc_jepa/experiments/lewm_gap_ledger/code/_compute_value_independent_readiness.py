from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any

import numpy as np


ROOT = Path(__file__).resolve().parent
REPORT_DIR = ROOT.parent / "reports"
DEFAULT_JSON = REPORT_DIR / "compute_value_independent_readiness.json"
DEFAULT_MD = REPORT_DIR / "compute_value_independent_readiness.md"
REQUIRED = ("episode", "option_error", "uniform_error", "predicted_option_score")


def clean_float(value: float) -> float:
    out = float(value)
    if out == 0.0:
        return 0.0
    if not math.isfinite(out):
        raise ValueError(f"non-finite value: {out!r}")
    return out


def clean_json(value: Any) -> Any:
    if isinstance(value, dict):
        return {str(k): clean_json(v) for k, v in value.items()}
    if isinstance(value, (list, tuple)):
        return [clean_json(v) for v in value]
    if isinstance(value, np.ndarray):
        return clean_json(value.tolist())
    if isinstance(value, (np.integer,)):
        return int(value)
    if isinstance(value, (np.floating,)):
        return clean_float(float(value))
    if isinstance(value, float):
        return clean_float(value)
    return value


def inspect_npz(path: Path) -> dict[str, Any]:
    try:
        with np.load(path, allow_pickle=False) as data:
            keys = sorted(data.files)
            missing = [key for key in REQUIRED if key not in keys]
            shapes = {key: list(data[key].shape) for key in keys if key in set(REQUIRED) | {"option_depths", "chosen_depth"}}
    except Exception as exc:
        return {"path": str(path), "readable": False, "error": str(exc), "usable": False}
    return {
        "path": str(path),
        "readable": True,
        "keys": keys,
        "missing_required": missing,
        "shapes": shapes,
        "usable": len(missing) == 0,
    }


def write_markdown(path: Path, report: dict[str, Any]) -> None:
    lines = [
        "# Compute-Value Independent Readiness",
        "",
        f"- status: `{report['status']}`",
        f"- usable independent structured artifacts: `{report['summary']['independent_usable_count']}`",
        f"- inspected artifacts: `{report['summary']['inspected_count']}`",
        "",
        "| artifact | usable | missing required arrays |",
        "|---|---:|---|",
    ]
    for row in report["artifacts"]:
        name = Path(row["path"]).name
        missing = ",".join(row.get("missing_required", []))
        lines.append(f"| `{name}` | `{row.get('usable', False)}` | `{missing}` |")
    lines.append("")
    path.write_text("\n".join(lines), encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Check whether independent export inputs exist for structured compute-value replication")
    parser.add_argument("--json", default=str(DEFAULT_JSON))
    parser.add_argument("--md", default=str(DEFAULT_MD))
    parser.add_argument("--candidate", action="append", default=[])
    args = parser.parse_args()
    candidates = [Path(item) for item in args.candidate]
    default_roots = [
        REPORT_DIR,
        Path("C:/OMEGA/le-wm-survey/reports"),
        Path("C:/OMEGA/_native_models_eval"),
    ]
    for root in default_roots:
        if root.exists():
            candidates.extend(root.rglob("*.npz") if root.name == "_native_models_eval" else root.glob("*.npz"))
    seen: set[str] = set()
    artifacts = []
    for path in candidates:
        key = str(path.resolve()) if path.exists() else str(path)
        if key in seen:
            continue
        seen.add(key)
        if path.exists():
            artifacts.append(inspect_npz(path))
    usable = [row for row in artifacts if row.get("usable")]
    fixed_export_names = {
        "compute_value_feature_group_ablation_predictions.npz",
        "compute_value_structured_ablation_predictions.npz",
        "compute_value_structured_assignment_predictions.npz",
        "compute_value_structured_stability_predictions.npz",
    }
    independent_usable = [row for row in usable if Path(str(row["path"])).name not in fixed_export_names]
    status = "ready" if independent_usable else "fail-closed"
    report = {
        "status": status,
        "schema_id": "bedc_jepa.compute_value_independent_readiness",
        "required_arrays": list(REQUIRED),
        "summary": {
            "inspected_count": int(len(artifacts)),
            "usable_count": int(len(usable)),
            "independent_usable_count": int(len(independent_usable)),
        },
        "artifacts": artifacts,
        "not_claimed": (
            "No independent-export structured compute-value replication is claimed unless an artifact "
            "with episode, option_error, uniform_error, and predicted_option_score exists outside the current fixed-export structured rows."
        ),
    }
    Path(args.json).parent.mkdir(parents=True, exist_ok=True)
    Path(args.json).write_text(json.dumps(clean_json(report), indent=2, ensure_ascii=False), encoding="utf-8")
    write_markdown(Path(args.md), report)
    print(json.dumps(clean_json(report["summary"]), ensure_ascii=False, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
