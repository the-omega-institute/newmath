#!/usr/bin/env python3
"""Run a pointer-only sliced-CF Gaussianity reproduction sidecar."""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from datetime import datetime, timezone
import json
import math
from pathlib import Path
import sys
from typing import Any, Iterable, Mapping, Sequence

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.identifiability_bound import whitening_deviation_epsilon
from bedc_quality_lab.latent_distribution import LatentDistributionSpec


LOCAL_SCHEMA_ID = "bedc-quality-lab:sigreg-gaussianity-reproduction-sidecar"
ARTIFACT_ID = "bedc-quality-lab:sigreg-gaussianity-reproduction"
JSON_ARTIFACT = "runs/sigreg_gaussianity_reproduction.json"
REPORT_ARTIFACT = "runs/sigreg_gaussianity_reproduction.md"
CANONICAL_ROLE = "sidecar_not_in_" + "CANONICAL" + "_REPORTS"

DEFAULT_SAMPLE_COUNT = 4096
DEFAULT_SEEDS = (11, 23, 37, 53, 71, 89, 107, 131, 163, 197, 233, 269)
DEFAULT_DIRECTIONS = 64
DEFAULT_FREQUENCIES = (0.5, 1.0, 1.5, 2.0, 2.5)
DEFAULT_BOOTSTRAP_RESAMPLES = 2000
DEFAULT_BOOTSTRAP_SEED = 680
DEFAULT_COV_TO_IDENTITY_MAX = 0.20
DEFAULT_MIN_COV_EIGENVALUE_FLOOR = 0.80
DEFAULT_MIN_PROJECTED_VARIANCE_FLOOR = 0.70
EPS = 1.0e-12

NOT_CLAIMED = (
    "SIGReg statistic reproduction is not a complete LeJEPA claim",
    "no global or universal Gaussianity certification",
    "no project-wide quality conclusion",
    "no tensor NameCert conclusion",
    "no language-model behavior conclusion",
    "no solved model-quality conclusion",
    "no claim outside the listed source families, seeds, directions, and frequency grid",
)
REVOKE_CONDITIONS = (
    "revoke if fresh paired seeds remove Gaussian versus non-Gaussian CI separation",
    "revoke if a larger sample or a different direction and frequency grid removes CI separation",
    "revoke if any collapse or isometry guard fails",
    "revoke if the statistic computation path reads ground-truth labels or source-family keys",
)
FORBIDDEN_STATISTIC_KEYS = frozenset(
    {
        "z",
        "z_pair",
        "labels",
        "label",
        "source_family",
        "family",
        "distribution",
        "distribution_key",
        "latent_distribution",
    }
)


@dataclass(frozen=True)
class GuardThresholds:
    cov_to_identity_max: float = DEFAULT_COV_TO_IDENTITY_MAX
    min_cov_eigenvalue_floor: float = DEFAULT_MIN_COV_EIGENVALUE_FLOOR
    min_projected_variance_floor: float = DEFAULT_MIN_PROJECTED_VARIANCE_FLOOR


@dataclass(frozen=True)
class FamilyArm:
    arm_id: str
    role: str
    spec: LatentDistributionSpec
    predeclared_hg_f1: bool = True

    def report_row(self) -> dict[str, Any]:
        return {
            "arm_id": self.arm_id,
            "role": self.role,
            "latent_distribution": self.spec.to_source_spec(),
            "predeclared_hg_f1": bool(self.predeclared_hg_f1),
        }


def family_arms() -> tuple[FamilyArm, ...]:
    return (
        FamilyArm("gaussian", "gaussian_control", LatentDistributionSpec.gaussian(), False),
        FamilyArm("laplace", "non_gaussian_control", LatentDistributionSpec.laplace()),
        FamilyArm("uniform", "non_gaussian_control", LatentDistributionSpec.uniform()),
        FamilyArm("student_t_df3", "non_gaussian_control", LatentDistributionSpec.student_t(df=3)),
        FamilyArm(
            "generalized_normal_alpha4",
            "non_gaussian_control",
            LatentDistributionSpec.generalized_normal(alpha=4),
        ),
    )


def _as_h_matrix(h: np.ndarray) -> np.ndarray:
    value = np.asarray(h, dtype=np.float64)
    if value.ndim != 2:
        raise ValueError("h must be a matrix")
    if value.shape[0] < 3 or value.shape[1] < 1:
        raise ValueError("h must have at least three rows and one column")
    if not np.all(np.isfinite(value)):
        raise ValueError("h must contain only finite values")
    return value


def _covariance(h: np.ndarray) -> np.ndarray:
    value = _as_h_matrix(h)
    centered = value - np.mean(value, axis=0, keepdims=True)
    cov = centered.T @ centered / float(value.shape[0] - 1)
    if not np.all(np.isfinite(cov)):
        raise ValueError("covariance must be finite")
    return cov.astype(np.float64)


def _random_unit_directions(*, dim: int, count: int, seed: int) -> np.ndarray:
    if count <= 0:
        raise ValueError("directions must be positive")
    rng = np.random.default_rng(int(seed))
    raw = rng.normal(size=(int(count), int(dim)))
    norms = np.linalg.norm(raw, axis=1, keepdims=True)
    if np.any(norms <= EPS):
        raise ValueError("random direction norm vanished")
    return (raw / norms).astype(np.float64)


def _sorted_frequencies(frequencies: Sequence[float]) -> np.ndarray:
    value = np.asarray(tuple(float(item) for item in frequencies), dtype=np.float64)
    if value.ndim != 1 or value.size == 0:
        raise ValueError("frequencies must be a non-empty one-dimensional grid")
    if np.any(value <= 0.0) or not np.all(np.isfinite(value)):
        raise ValueError("frequencies must be positive finite values")
    return np.sort(value).astype(np.float64)


def _forbidden_feature_audit(features: Mapping[str, Any] | None) -> dict[str, Any]:
    keys = tuple(features.keys()) if features is not None else ()
    hits = sorted(set(keys) & FORBIDDEN_STATISTIC_KEYS)
    return {
        "status": "pass" if not hits else "fail",
        "forbidden_keys": hits,
        "checked_keys": list(keys),
        "criterion": "statistic computation path accepts only h plus numeric probe parameters",
    }


class SlicedCFGaussianityProbe:
    def __init__(
        self,
        *,
        directions: int,
        frequencies: Sequence[float],
        guard_thresholds: GuardThresholds | None = None,
    ) -> None:
        self.directions = int(directions)
        self.frequencies = _sorted_frequencies(frequencies)
        self.guard_thresholds = guard_thresholds or GuardThresholds()

    def score(
        self,
        h: np.ndarray,
        *,
        seed: int,
        directions: int | None = None,
        frequencies: Sequence[float] | None = None,
        features: Mapping[str, Any] | None = None,
    ) -> dict[str, Any]:
        feature_audit = _forbidden_feature_audit(features)
        if feature_audit["status"] != "pass":
            return {
                "sigreg_penalty": math.nan,
                "guard_status": "fail",
                "guard_reasons": ["forbidden_feature_in_statistic_path"],
                "forbidden_feature_audit": feature_audit,
            }
        value = _as_h_matrix(h)
        direction_count = self.directions if directions is None else int(directions)
        frequency_grid = self.frequencies if frequencies is None else _sorted_frequencies(frequencies)
        unit_directions = _random_unit_directions(dim=value.shape[1], count=direction_count, seed=int(seed))
        projections = value @ unit_directions.T
        projection_mean = np.mean(projections, axis=0, keepdims=True)
        centered_projections = projections - projection_mean
        projected_variances = np.var(centered_projections, axis=0, ddof=1)
        projected_scales = np.sqrt(np.maximum(projected_variances, EPS))
        standardized = centered_projections / projected_scales.reshape(1, -1)
        target = np.exp(-0.5 * np.square(frequency_grid))
        exp_values = np.exp(1j * standardized[:, :, None] * frequency_grid.reshape(1, 1, -1))
        empirical = np.mean(exp_values, axis=0)
        diff = empirical - target.reshape(1, -1)
        penalty_by_direction = np.mean(np.abs(diff) ** 2, axis=1)
        cov = _covariance(value)
        eigenvalues = np.linalg.eigvalsh(cov)
        cov_to_identity = float(np.linalg.norm(cov - np.eye(cov.shape[0], dtype=np.float64), ord="fro"))
        min_cov_eigenvalue = float(np.min(eigenvalues))
        min_projected_variance = float(np.min(projected_variances))
        reasons = []
        thresholds = self.guard_thresholds
        if cov_to_identity > thresholds.cov_to_identity_max:
            reasons.append("covariance_to_identity_exceeds_threshold")
        if min_cov_eigenvalue < thresholds.min_cov_eigenvalue_floor:
            reasons.append("min_cov_eigenvalue_below_floor")
        if min_projected_variance < thresholds.min_projected_variance_floor:
            reasons.append("min_projected_variance_below_floor")
        return {
            "sigreg_penalty": float(np.mean(penalty_by_direction)),
            "penalty_by_direction": [float(item) for item in penalty_by_direction],
            "cov_to_identity_fro": cov_to_identity,
            "min_cov_eigenvalue": min_cov_eigenvalue,
            "min_projected_variance": min_projected_variance,
            "projected_variance_min": min_projected_variance,
            "projected_variance_max": float(np.max(projected_variances)),
            "direction_count": int(direction_count),
            "frequency_grid": [float(item) for item in frequency_grid],
            "guard_status": "ok" if not reasons else "fail",
            "guard_reasons": reasons,
            "forbidden_feature_audit": feature_audit,
        }


def _paired_bootstrap_ci(
    differences: Sequence[float],
    *,
    resamples: int,
    seed: int,
) -> dict[str, Any]:
    values = np.asarray(tuple(float(item) for item in differences), dtype=np.float64)
    if values.ndim != 1 or values.size < 2:
        raise ValueError("paired bootstrap needs at least two differences")
    if not np.all(np.isfinite(values)):
        raise ValueError("paired bootstrap differences must be finite")
    rng = np.random.default_rng(int(seed))
    draws = np.empty(int(resamples), dtype=np.float64)
    for idx in range(int(resamples)):
        sample = values[rng.integers(0, values.size, size=values.size)]
        draws[idx] = float(np.mean(sample))
    low, high = np.quantile(draws, [0.025, 0.975])
    return {
        "n": int(values.size),
        "mean": float(np.mean(values)),
        "ci95_low": float(low),
        "ci95_high": float(high),
        "bootstrap_resamples": int(resamples),
        "bootstrap_seed": int(seed),
        "differences": [float(item) for item in values],
    }


def _sample_metrics(
    *,
    arm: FamilyArm,
    seed: int,
    sample_count: int,
    probe: SlicedCFGaussianityProbe,
) -> dict[str, Any]:
    h = arm.spec.sample(int(sample_count), int(seed))
    score = probe.score(h, seed=int(seed), directions=probe.directions, frequencies=probe.frequencies)
    return {
        "arm_id": arm.arm_id,
        "seed": int(seed),
        "sample_count": int(sample_count),
        "sigreg_penalty": float(score["sigreg_penalty"]),
        "proxy_whitening_deviation_epsilon": float(whitening_deviation_epsilon(h)),
        "guard_status": score["guard_status"],
        "guard_reasons": list(score["guard_reasons"]),
        "cov_to_identity_fro": float(score["cov_to_identity_fro"]),
        "min_cov_eigenvalue": float(score["min_cov_eigenvalue"]),
        "min_projected_variance": float(score["min_projected_variance"]),
        "forbidden_feature_audit": score["forbidden_feature_audit"],
    }


def _mean_metric(records: Iterable[Mapping[str, Any]], key: str) -> float:
    values = [float(record[key]) for record in records]
    if not values:
        return math.nan
    return float(np.mean(np.asarray(values, dtype=np.float64)))


def _family_aggregates(records: Sequence[Mapping[str, Any]]) -> dict[str, dict[str, Any]]:
    by_arm: dict[str, list[Mapping[str, Any]]] = {}
    for record in records:
        by_arm.setdefault(str(record["arm_id"]), []).append(record)
    return {
        arm_id: {
            "seed_count": len(items),
            "sigreg_penalty_mean": _mean_metric(items, "sigreg_penalty"),
            "proxy_whitening_deviation_epsilon_mean": _mean_metric(items, "proxy_whitening_deviation_epsilon"),
            "guard_status": "ok" if all(item["guard_status"] == "ok" for item in items) else "fail",
        }
        for arm_id, items in sorted(by_arm.items())
    }


def _paired_ci_cells(
    *,
    records: Sequence[Mapping[str, Any]],
    arms: Sequence[FamilyArm],
    resamples: int,
    bootstrap_seed: int,
) -> list[dict[str, Any]]:
    by_key = {(str(record["arm_id"]), int(record["seed"])): record for record in records}
    gaussian = next(arm for arm in arms if arm.role == "gaussian_control")
    cells = []
    for arm in arms:
        if not arm.predeclared_hg_f1:
            continue
        differences = []
        proxy_differences = []
        paired_seeds = []
        for seed in sorted({seed for key_arm, seed in by_key if key_arm == gaussian.arm_id}):
            left = by_key[(arm.arm_id, seed)]
            right = by_key[(gaussian.arm_id, seed)]
            differences.append(float(left["sigreg_penalty"]) - float(right["sigreg_penalty"]))
            proxy_differences.append(
                float(left["proxy_whitening_deviation_epsilon"])
                - float(right["proxy_whitening_deviation_epsilon"])
            )
            paired_seeds.append(seed)
        sigreg_ci = _paired_bootstrap_ci(
            differences,
            resamples=int(resamples),
            seed=int(bootstrap_seed) + len(cells),
        )
        proxy_ci = _paired_bootstrap_ci(
            proxy_differences,
            resamples=int(resamples),
            seed=int(bootstrap_seed) + 1000 + len(cells),
        )
        cells.append(
            {
                "family": arm.arm_id,
                "comparison": f"{arm.arm_id}_minus_{gaussian.arm_id}",
                "paired_seeds": paired_seeds,
                "non_gaussian_minus_gaussian_sigreg_penalty": sigreg_ci,
                "non_gaussian_minus_gaussian_proxy_whitening_deviation": proxy_ci,
                "hg_f1_status": "pass" if sigreg_ci["ci95_low"] > 0.0 else "fail",
            }
        )
    return cells


def _proxy_contrast(cells: Sequence[Mapping[str, Any]]) -> dict[str, Any]:
    rows = []
    for cell in cells:
        sigreg_low = float(cell["non_gaussian_minus_gaussian_sigreg_penalty"]["ci95_low"])
        proxy_low = float(cell["non_gaussian_minus_gaussian_proxy_whitening_deviation"]["ci95_low"])
        rows.append(
            {
                "family": cell["family"],
                "sigreg_separates": sigreg_low > 0.0,
                "proxy_separates": proxy_low > 0.0,
                "status": "disagreement_preserved" if (sigreg_low > 0.0) != (proxy_low > 0.0) else "agreement_recorded",
            }
        )
    return {
        "status": "reported_not_promoted",
        "proxy": "bedc_quality_lab.identifiability_bound.whitening_deviation_epsilon",
        "rows": rows,
        "promotion": "none",
    }


def _hardgates(
    *,
    records: Sequence[Mapping[str, Any]],
    cells: Sequence[Mapping[str, Any]],
    proxy_contrast: Mapping[str, Any],
) -> dict[str, Any]:
    guard_failures = [
        {
            "arm_id": record["arm_id"],
            "seed": record["seed"],
            "guard_reasons": record["guard_reasons"],
        }
        for record in records
        if record["guard_status"] != "ok"
    ]
    audit_failures = [
        {
            "arm_id": record["arm_id"],
            "seed": record["seed"],
            "forbidden_feature_audit": record["forbidden_feature_audit"],
        }
        for record in records
        if record["forbidden_feature_audit"]["status"] != "pass"
    ]
    separation_failures = [cell["family"] for cell in cells if cell["hg_f1_status"] != "pass"]
    return {
        "HG-F1": {
            "status": "pass" if not separation_failures else "fail",
            "criterion": "paired bootstrap 95 percent CI low for non-Gaussian minus Gaussian SIGReg penalty is strictly positive",
            "failed_families": separation_failures,
        },
        "HG-F2": {
            "status": "pass",
            "criterion": "SIGReg and whitening proxy are reported side by side without promotion",
            "proxy_contrast_status": proxy_contrast["status"],
        },
        "HG-F3": {
            "status": "pass" if not guard_failures else "fail",
            "criterion": "covariance, minimum eigenvalue, and projected-variance guards must all pass",
            "failures": guard_failures,
        },
        "HG-F4": {
            "status": "pass" if not audit_failures else "fail",
            "criterion": "statistic path must not read labels, z, z_pair, or source-family keys",
            "failures": audit_failures,
        },
        "HG-F5": {
            "status": "pass",
            "criterion": "failed CI separation demotes the sidecar verdict to negative/compression",
        },
    }


def _verdict(hardgates: Mapping[str, Mapping[str, Any]]) -> dict[str, Any]:
    failed = [gate for gate, row in hardgates.items() if row["status"] != "pass" and gate != "HG-F5"]
    if failed:
        status = "negative/compression"
        reason = "CI separation or guard/audit condition failed; no positive promotion is recorded"
    else:
        status = "positive_control_passed_pointer_only"
        reason = "finite positive controls separate under the predeclared SIGReg statistic"
    return {
        "status": status,
        "passed_gates": [gate for gate, row in hardgates.items() if row["status"] == "pass"],
        "failed_gates": failed,
        "reason": reason,
        "promotion": "none",
    }


def build_payload(
    *,
    generated_at: str,
    sample_count: int = DEFAULT_SAMPLE_COUNT,
    seeds: Sequence[int] = DEFAULT_SEEDS,
    directions: int = DEFAULT_DIRECTIONS,
    frequencies: Sequence[float] = DEFAULT_FREQUENCIES,
    bootstrap_resamples: int = DEFAULT_BOOTSTRAP_RESAMPLES,
    bootstrap_seed: int = DEFAULT_BOOTSTRAP_SEED,
    guard_thresholds: GuardThresholds | None = None,
) -> dict[str, Any]:
    thresholds = guard_thresholds or GuardThresholds()
    probe = SlicedCFGaussianityProbe(
        directions=int(directions),
        frequencies=tuple(float(item) for item in frequencies),
        guard_thresholds=thresholds,
    )
    arms = family_arms()
    records = [
        _sample_metrics(arm=arm, seed=int(seed), sample_count=int(sample_count), probe=probe)
        for arm in arms
        for seed in seeds
    ]
    aggregates = _family_aggregates(records)
    cells = _paired_ci_cells(
        records=records,
        arms=arms,
        resamples=int(bootstrap_resamples),
        bootstrap_seed=int(bootstrap_seed),
    )
    proxy_contrast = _proxy_contrast(cells)
    hardgates = _hardgates(records=records, cells=cells, proxy_contrast=proxy_contrast)
    verdict = _verdict(hardgates)
    return {
        "schema_id": LOCAL_SCHEMA_ID,
        "artifact_id": ARTIFACT_ID,
        "artifact": JSON_ARTIFACT,
        "report": REPORT_ARTIFACT,
        "canonical_role": CANONICAL_ROLE,
        "status": "pointer-only",
        "generated_at": generated_at,
        "parameters": {
            "sample_count": int(sample_count),
            "seeds": [int(seed) for seed in seeds],
            "directions": int(directions),
            "frequencies": [float(item) for item in probe.frequencies],
            "bootstrap_resamples": int(bootstrap_resamples),
            "bootstrap_seed": int(bootstrap_seed),
            "guard_thresholds": {
                "cov_to_identity_max": float(thresholds.cov_to_identity_max),
                "min_cov_eigenvalue_floor": float(thresholds.min_cov_eigenvalue_floor),
                "min_projected_variance_floor": float(thresholds.min_projected_variance_floor),
            },
            "projection_standardization": "per_direction_before_characteristic_function",
        },
        "source_artifacts": {
            "generation_script": "scripts/run_sigreg_gaussianity_reproduction.py",
            "latent_distribution": "bedc_quality_lab.latent_distribution.LatentDistributionSpec",
            "proxy_whitening_deviation": "bedc_quality_lab.identifiability_bound.whitening_deviation_epsilon",
        },
        "family_arms": [arm.report_row() for arm in arms],
        "per_family_per_seed_records": records,
        "guard_rows": [
            {
                "arm_id": record["arm_id"],
                "seed": record["seed"],
                "guard_status": record["guard_status"],
                "guard_reasons": record["guard_reasons"],
                "cov_to_identity_fro": record["cov_to_identity_fro"],
                "min_cov_eigenvalue": record["min_cov_eigenvalue"],
                "min_projected_variance": record["min_projected_variance"],
            }
            for record in records
        ],
        "family_aggregates": aggregates,
        "paired_ci_cells": cells,
        "proxy_contrast": proxy_contrast,
        "hardgate_evidence": hardgates,
        "verdict": verdict,
        "negative_compression_fallback": {
            "status": "active" if verdict["status"] == "negative/compression" else "available",
            "rule": "CI separation failure records negative/compression and never promotes the sidecar",
        },
        "not_claimed": list(NOT_CLAIMED),
        "revoke_conditions": list(REVOKE_CONDITIONS),
    }


def render_markdown(payload: Mapping[str, Any]) -> str:
    lines = [
        "# SIGReg Gaussianity Reproduction Sidecar",
        "",
        f"- artifact: `{payload['artifact']}`",
        f"- schema_id: `{payload['schema_id']}`",
        f"- canonical_role: `{payload['canonical_role']}`",
        f"- verdict: `{payload['verdict']['status']}`",
        f"- promotion: `{payload['verdict']['promotion']}`",
        "",
        "## Hardgates",
        "",
    ]
    for gate, row in payload["hardgate_evidence"].items():
        lines.append(f"- {gate}: `{row['status']}`")
    lines.extend(["", "## Paired CI Cells", ""])
    for cell in payload["paired_ci_cells"]:
        ci = cell["non_gaussian_minus_gaussian_sigreg_penalty"]
        proxy = cell["non_gaussian_minus_gaussian_proxy_whitening_deviation"]
        lines.append(
            "- "
            f"{cell['family']}: SIGReg mean={ci['mean']:.8f}, "
            f"CI95=[{ci['ci95_low']:.8f}, {ci['ci95_high']:.8f}], "
            f"proxy mean={proxy['mean']:.8f}, proxy CI95=[{proxy['ci95_low']:.8f}, {proxy['ci95_high']:.8f}], "
            f"HG-F1={cell['hg_f1_status']}"
        )
    lines.extend(["", "## Proxy Contrast", ""])
    for row in payload["proxy_contrast"]["rows"]:
        lines.append(
            "- "
            f"{row['family']}: sigreg_separates={row['sigreg_separates']}, "
            f"proxy_separates={row['proxy_separates']}, status={row['status']}"
        )
    lines.extend(["", "## Not Claimed", ""])
    for item in payload["not_claimed"]:
        lines.append(f"- {item}")
    lines.extend(["", "## Revoke Conditions", ""])
    for item in payload["revoke_conditions"]:
        lines.append(f"- {item}")
    lines.append("")
    return "\n".join(lines)


def write_artifacts(payload: Mapping[str, Any], *, root: Path) -> None:
    json_path = root / JSON_ARTIFACT
    md_path = root / REPORT_ARTIFACT
    json_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    md_path.write_text(render_markdown(payload), encoding="utf-8")


def _parse_seed_list(value: str) -> tuple[int, ...]:
    seeds = tuple(int(item.strip()) for item in value.split(",") if item.strip())
    if len(seeds) < 2:
        raise argparse.ArgumentTypeError("at least two seeds are required")
    return seeds


def _parse_frequency_list(value: str) -> tuple[float, ...]:
    frequencies = tuple(float(item.strip()) for item in value.split(",") if item.strip())
    if not frequencies:
        raise argparse.ArgumentTypeError("at least one frequency is required")
    return frequencies


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--sample-count", type=int, default=DEFAULT_SAMPLE_COUNT)
    parser.add_argument("--seeds", type=_parse_seed_list, default=DEFAULT_SEEDS)
    parser.add_argument("--directions", type=int, default=DEFAULT_DIRECTIONS)
    parser.add_argument("--frequencies", type=_parse_frequency_list, default=DEFAULT_FREQUENCIES)
    parser.add_argument("--bootstrap-resamples", type=int, default=DEFAULT_BOOTSTRAP_RESAMPLES)
    args = parser.parse_args(argv)
    payload = build_payload(
        generated_at=datetime.now(timezone.utc).isoformat(),
        sample_count=args.sample_count,
        seeds=args.seeds,
        directions=args.directions,
        frequencies=args.frequencies,
        bootstrap_resamples=args.bootstrap_resamples,
    )
    write_artifacts(payload, root=args.root)
    print(json.dumps({"artifact": JSON_ARTIFACT, "verdict": payload["verdict"]["status"]}, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
