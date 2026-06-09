"""Clean review bundle contract for BEDC-JEPA evidence packets."""

from __future__ import annotations

import json
from pathlib import Path
import subprocess
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
REPORTS = ROOT / "reports"


def _load_json(name: str) -> dict[str, Any]:
    return json.loads((REPORTS / name).read_text(encoding="utf-8"))


def _git_head() -> str | None:
    try:
        completed = subprocess.run(
            ["git", "rev-parse", "HEAD"],
            cwd=ROOT.parents[1],
            check=True,
            capture_output=True,
            text=True,
            timeout=10,
        )
    except (OSError, subprocess.CalledProcessError, subprocess.TimeoutExpired):
        return None
    return completed.stdout.strip()


def _check(condition: bool, name: str, failures: list[str]) -> None:
    if not condition:
        failures.append(name)


def build_review_bundle() -> dict[str, Any]:
    readiness = _load_json("bedc_jepa_readiness.json")
    native = _load_json("bedc_jepa_public_native_minigrid_benchmark.json")
    sweep = _load_json("bedc_jepa_public_native_minigrid_seed_sweep.json")
    public_debt = _load_json("bedc_jepa_public_debt_decomposition.json")
    conformal = _load_json("bedc_jepa_conformal_certified_coverage.json")
    ablation = _load_json("bedc_jepa_loss_ablation.json")
    cuda = _load_json("bedc_jepa_public_cuda_adapter_comparison.json")
    manifest = _load_json("bedc_jepa_artifact_manifest.json")
    failures: list[str] = []
    _check(readiness["evidence_boundary"]["checkpoint_contact"] == "closed", "checkpoint contact boundary", failures)
    _check(readiness["evidence_boundary"]["native_public_benchmark"] == "closed", "native public benchmark boundary", failures)
    _check(native.get("status") == "executed", "native MiniGrid benchmark executed", failures)
    _check(set(native.get("systems", {})) == {"S0", "S1", "S2", "S3"}, "native MiniGrid S0/S1/S2/S3 systems", failures)
    _check(float(native["deltas"]["s0_minus_s3_unlogged_error"]) > 0.05, "native MiniGrid UER reduction", failures)
    _check(float(native["deltas"]["lambda_0_minus_best_high_gap_rate"]) > 0.05, "native MiniGrid planning high-gap reduction", failures)
    _check(public_debt.get("status") == "executed", "public MiniGrid debt decomposition executed", failures)
    _check(
        public_debt["interpretation"]["diagnosis"] == "silent debt falls while coverage debt rises",
        "public MiniGrid debt diagnosis",
        failures,
    )
    _check(conformal.get("status") == "executed", "public MiniGrid conformal certified coverage executed", failures)
    _check(ablation.get("status") == "executed", "public MiniGrid local ablation executed", failures)
    _check(sweep.get("status") == "executed", "native MiniGrid seed sweep executed", failures)
    _check(float(sweep.get("seed_count_executed", 0.0)) >= 5.0, "native MiniGrid seed sweep count", failures)
    _check(float(sweep["summary"]["unlogged_error_win_rate"]) >= 0.6, "seed sweep UER win rate", failures)
    _check(cuda.get("status") == "executed", "CUDA checkpoint-contact comparison", failures)
    _check(cuda["public_adapters"]["ac_giant"]["model"]["checkpoint_status"] == "loaded", "AC Giant checkpoint loaded", failures)
    _check(manifest.get("schema_id") == "bedc-jepa-artifact-manifest", "artifact manifest schema", failures)
    status = "review_ready" if not failures else "incomplete"
    return {
        "schema_id": "bedc-jepa-review-bundle",
        "status": status,
        "source_commit_at_build": _git_head(),
        "required_artifacts": {
            "readiness": "reports/bedc_jepa_readiness.json",
            "native_minigrid": "reports/bedc_jepa_public_native_minigrid_benchmark.json",
            "native_minigrid_seed_sweep": "reports/bedc_jepa_public_native_minigrid_seed_sweep.json",
            "public_debt_decomposition": "reports/bedc_jepa_public_debt_decomposition.json",
            "certified_coverage_curve": "reports/bedc_jepa_certified_coverage_curve.json",
            "risk_constrained_planning": "reports/bedc_jepa_risk_constrained_planning.json",
            "public_debt_closure_report": "reports/bedc_jepa_public_debt_closure_report.md",
            "conformal_certified_coverage": "reports/bedc_jepa_conformal_certified_coverage.json",
            "risk_success_pareto": "reports/bedc_jepa_risk_success_pareto.json",
            "loss_ablation": "reports/bedc_jepa_loss_ablation.json",
            "cuda_adapter_comparison": "reports/bedc_jepa_public_cuda_adapter_comparison.json",
            "artifact_manifest": "reports/bedc_jepa_artifact_manifest.json",
            "quality_backend_candidate": "reports/bedc_jepa_quality_backend_candidate.json",
            "latent_claim_certificates": "reports/bedc_latent_claim_certificates.json",
            "conformal_gap_sweep": "reports/bedc_conformal_gap_sweep.json",
            "claim_boundary_audit": "reports/bedc_claim_boundary_audit.json",
        },
        "reproduction_commands": [
            "python scripts/run_public_minigrid_native_benchmark.py",
            "python scripts/run_public_minigrid_native_seed_sweep.py",
            "python scripts/build_public_minigrid_debt_closure.py",
            "python scripts/build_public_jepa_cuda_comparison.py",
            "python scripts/build_bedc_jepa_artifact_manifest.py",
            "python scripts/build_bedc_jepa_readiness.py",
            "python scripts/build_bedc_jepa_review_bundle.py",
            "python scripts/build_bedc_jepa_quality_backend_candidate.py",
            "python scripts/run_bedc_latent_claim_certificate.py",
            "python -m pytest -q tests/test_public_jepa_baselines.py tests/test_public_minigrid_native_benchmark.py tests/test_bedc_jepa_readiness.py tests/test_bedc_jepa_external_run_kit.py tests/test_bedc_jepa_artifact_manifest.py tests/test_bedc_jepa_review_bundle.py tests/test_bedc_jepa_quality_backend.py tests/test_latent_claim_certificate.py",
            "pdflatex -interaction=nonstopmode -halt-on-error main.tex",
        ],
        "checks": {
            "checkpoint_contact": readiness["evidence_boundary"]["checkpoint_contact"],
            "native_public_benchmark": readiness["evidence_boundary"]["native_public_benchmark"],
            "native_unlogged_error_reduction": native["deltas"]["s0_minus_s3_unlogged_error"],
            "native_planning_high_gap_reduction": native["deltas"]["lambda_0_minus_best_high_gap_rate"],
            "public_debt_diagnosis": public_debt["interpretation"]["diagnosis"],
            "public_silent_debt_reduction": public_debt["interpretation"]["changes"][
                "silent_debt_change_s0_minus_s3"
            ],
            "public_coverage_debt_change": public_debt["interpretation"]["changes"][
                "coverage_debt_change_s0_minus_s3"
            ],
            "public_conformal_predicate_count": float(
                len(conformal["conformal_certified_coverage"]["predicates"])
            ),
            "public_ablation_unlogged_penalty_effect": ablation["loss_ablation"]["mechanism_readout"][
                "unlogged_penalty_effect"
            ],
            "seed_sweep_count": sweep.get("seed_count_executed", 0.0),
            "seed_sweep_unlogged_error_win_rate": sweep["summary"].get("unlogged_error_win_rate") if sweep.get("summary") else None,
            "ac_giant_checkpoint_status": cuda["public_adapters"]["ac_giant"]["model"]["checkpoint_status"],
        },
        "failures": failures,
        "cannot_claim": [
            "public benchmark superiority",
            "native V-JEPA2-AC checkpoint reproduction",
            "robotics benchmark result",
            "large-scale real-world conclusion",
            "formal neural-network proof",
        ],
    }


def write_review_bundle(path: str | Path) -> dict[str, Any]:
    bundle = build_review_bundle()
    target = Path(path)
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(json.dumps(bundle, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return bundle
