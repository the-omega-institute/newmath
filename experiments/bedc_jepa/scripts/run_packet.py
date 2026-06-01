#!/usr/bin/env python3
"""Build the BEDC-JEPA tiny world evidence packet."""

from __future__ import annotations

import json
from pathlib import Path
import sys
from typing import Any


ROOT = Path(__file__).resolve().parents[3]
EXPERIMENT_ROOT = Path(__file__).resolve().parents[1]
QUALITY_LAB = ROOT / "papers" / "bedc-quality-lab"
if str(QUALITY_LAB) not in sys.path:
    sys.path.insert(0, str(QUALITY_LAB))
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.torch_bedc_jepa import run_torch_bedc_jepa_benchmark, run_torch_bedc_jepa_sweep
from experiments.bedc_jepa.certs.build_ledger import build_ledger
from experiments.bedc_jepa.certs.build_namecert import build_namecert, render_namecert_yaml
from experiments.bedc_jepa.metrics.quality_gate import evaluate_quality_gate


def _parse_scalar(value: str) -> object:
    text = value.strip()
    if text in {"true", "false"}:
        return text == "true"
    try:
        if "." in text:
            return float(text)
        return int(text)
    except ValueError:
        return text


def _load_config(path: Path) -> dict[str, Any]:
    lines = [
        raw_line
        for raw_line in path.read_text(encoding="utf-8").splitlines()
        if raw_line.strip() and not raw_line.lstrip().startswith("#")
    ]

    def line_indent(raw_line: str) -> int:
        return len(raw_line) - len(raw_line.lstrip(" "))

    def parse_block(index: int, indent: int) -> tuple[object, int]:
        if index >= len(lines):
            return {}, index
        if line_indent(lines[index]) < indent:
            return {}, index
        is_list = lines[index].strip().startswith("- ")
        if is_list:
            result: list[object] = []
            while index < len(lines) and line_indent(lines[index]) == indent:
                line = lines[index].strip()
                if not line.startswith("- "):
                    break
                result.append(_parse_scalar(line[2:]))
                index += 1
            return result, index

        result_dict: dict[str, object] = {}
        while index < len(lines) and line_indent(lines[index]) == indent:
            line = lines[index].strip()
            key, sep, value = line.partition(":")
            if not sep:
                raise ValueError(f"malformed config line: {lines[index]}")
            key = key.strip()
            value = value.strip()
            index += 1
            if value:
                result_dict[key] = _parse_scalar(value)
                continue
            child, index = parse_block(index, indent + 2)
            result_dict[key] = child
        return result_dict, index

    parsed, end_index = parse_block(0, 0)
    if end_index != len(lines) or not isinstance(parsed, dict):
        raise ValueError("malformed config")
    return parsed


def _render_report(packet: dict[str, Any], namecert_path: str, ledger_path: str) -> str:
    single = packet["benchmark"]["single"]
    sweep = packet["benchmark"]["sweep"]
    latent = single["systems"]["latent_only"]
    bedc = single["systems"]["bedc_objective"]
    gate = packet["quality_gate"]
    lines = [
        "# BEDC-JEPA Tiny World Quality Report",
        "",
        "## Scope",
        "",
        "- World: `boundary-gated-ou-world`",
        "- Baseline: `torch-latent-only`",
        "- BEDC objective: `torch-bedc-jepa-objective`",
        "- Primary metric: `unlogged_error_rate`",
        "",
        "## Objective",
        "",
        "- `latent_prediction`",
        "- `distinction_bce`",
        "- `gap_bce`",
        "- `unlogged_error_penalty`",
        "",
        "## Single Run",
        "",
        f"- Baseline unlogged error: `{float(latent['unlogged_error_rate']):.6f}`",
        f"- BEDC-JEPA unlogged error: `{float(bedc['unlogged_error_rate']):.6f}`",
        f"- Baseline gap AUROC: `{float(latent['gap_detection_auc']):.6f}`",
        f"- BEDC-JEPA gap AUROC: `{float(bedc['gap_detection_auc']):.6f}`",
        f"- Baseline debt: `{float(latent['bedc_debt_score']):.6f}`",
        f"- BEDC-JEPA debt: `{float(bedc['bedc_debt_score']):.6f}`",
        "",
        "## Seed Sweep",
        "",
        f"- Seed count: `{int(float(sweep['seed_count']))}`",
        f"- Mean unlogged-error reduction: `{float(sweep['unlogged_error_reduction_mean']):.6f}`",
        f"- Mean gap-AUROC gain: `{float(sweep['gap_auc_gain_mean']):.6f}`",
        f"- Mean debt reduction: `{float(sweep['debt_reduction_mean']):.6f}`",
        f"- Latent R2 delta absolute max: `{float(sweep['latent_r2_delta_abs_max']):.6g}`",
        "",
        "## Gate",
        "",
        f"- Decision: `{gate['decision']}`",
        f"- Blocking checks: `{', '.join(gate['blocking_checks']) if gate['blocking_checks'] else 'none'}`",
        "",
        "## Evidence",
        "",
        f"- NameCert: `{namecert_path}`",
        f"- Ledger: `{ledger_path}`",
        "- Quality packet: `experiments/bedc_jepa/reports/quality_packet.json`",
        "",
        "## Not Claimed",
        "",
        "- Executed public JEPA implementation comparison.",
        "- Real-world physics.",
        "- Open-domain semantic naming.",
        "- Lean verification of neural training.",
    ]
    return "\n".join(lines) + "\n"


def build_packet() -> dict[str, Any]:
    config = _load_config(EXPERIMENT_ROOT / "configs" / "tiny_world.yaml")
    benchmark = {
        "single": run_torch_bedc_jepa_benchmark(),
        "sweep": run_torch_bedc_jepa_sweep(),
    }
    packet = {
        "schema_id": "bedc-jepa-quality-packet",
        "config": config,
        "benchmark": benchmark,
    }
    packet["quality_gate"] = evaluate_quality_gate(packet)
    packet["ledger"] = build_ledger(packet)
    packet["namecert"] = build_namecert(packet)
    return packet


def main() -> None:
    report_dir = EXPERIMENT_ROOT / "reports"
    report_dir.mkdir(parents=True, exist_ok=True)
    packet = build_packet()
    packet_path = report_dir / "quality_packet.json"
    namecert_path = report_dir / "namecert.yaml"
    ledger_path = report_dir / "ledger.json"
    report_path = report_dir / "quality_report.md"
    packet_path.write_text(json.dumps(packet, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    namecert_path.write_text(render_namecert_yaml(packet["namecert"]), encoding="utf-8")
    ledger_path.write_text(json.dumps(packet["ledger"], indent=2, sort_keys=True) + "\n", encoding="utf-8")
    report_path.write_text(
        _render_report(
            packet,
            "experiments/bedc_jepa/reports/namecert.yaml",
            "experiments/bedc_jepa/reports/ledger.json",
        ),
        encoding="utf-8",
    )
    print(f"wrote {packet_path.relative_to(ROOT)}")
    print(f"wrote {namecert_path.relative_to(ROOT)}")
    print(f"wrote {ledger_path.relative_to(ROOT)}")
    print(f"wrote {report_path.relative_to(ROOT)}")


if __name__ == "__main__":
    main()
