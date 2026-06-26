#!/usr/bin/env python3
"""Write public MiniGrid BEDC-JEPA debt decomposition and calibration records."""

from __future__ import annotations

from pathlib import Path
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.public_minigrid_debt_closure import write_public_minigrid_debt_closure_analysis


def main() -> None:
    write_public_minigrid_debt_closure_analysis(ROOT / "reports")
    for name in (
        "bedc_jepa_public_debt_decomposition.json",
        "bedc_jepa_certified_coverage_curve.json",
        "bedc_jepa_risk_constrained_planning.json",
        "bedc_jepa_conformal_certified_coverage.json",
        "bedc_jepa_risk_success_pareto.json",
        "bedc_jepa_loss_ablation.json",
        "bedc_jepa_public_debt_closure_report.md",
    ):
        print(f"wrote {(ROOT / 'reports' / name).relative_to(ROOT)}")


if __name__ == "__main__":
    main()
