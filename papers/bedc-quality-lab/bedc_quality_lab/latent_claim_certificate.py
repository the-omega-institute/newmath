"""Fail-closed latent claim certificates for BEDC-JEPA evidence."""

from __future__ import annotations

from dataclasses import dataclass
import importlib.util
import json
from pathlib import Path
from typing import Any, Iterable

import numpy as np

from bedc_quality_lab.public_minigrid_native_benchmark import (
    DEFAULT_ENVIRONMENT_ID,
    _collect_examples,
)


ROOT = Path(__file__).resolve().parents[1]
REPORTS = ROOT / "reports"
ALPHAS = (0.20, 0.10, 0.05, 0.02, 0.01)
PRIMARY_ALPHA = 0.05
MIN_SINGLETON_COVERAGE = 0.50


@dataclass(frozen=True)
class LatentCarrierSplit:
    carrier_id: str
    source: str
    features_train: np.ndarray
    labels_train: np.ndarray
    features_calibration: np.ndarray
    labels_calibration: np.ndarray
    features_test: np.ndarray
    labels_test: np.ndarray
    predicate: str
    test_surface: str
    stability_condition: str
    gap_policy: str


@dataclass(frozen=True)
class BinaryReadout:
    weights: np.ndarray

    def score(self, features: np.ndarray) -> np.ndarray:
        logits = _design(features) @ self.weights
        return _sigmoid(logits)


def _sigmoid(values: np.ndarray) -> np.ndarray:
    return 1.0 / (1.0 + np.exp(-np.clip(values, -40.0, 40.0)))


def _design(features: np.ndarray) -> np.ndarray:
    matrix = np.asarray(features, dtype=np.float64)
    if matrix.ndim != 2:
        raise ValueError("features must be a matrix")
    quadratic = matrix * matrix
    return np.column_stack([matrix, quadratic, np.ones(matrix.shape[0])])


def fit_binary_readout(features: np.ndarray, labels: np.ndarray, *, ridge: float = 1e-3) -> BinaryReadout:
    labels_bool = np.asarray(labels, dtype=bool)
    target = np.where(labels_bool, 0.92, 0.08)
    logits = np.log(target / (1.0 - target))
    design = _design(features)
    gram = design.T @ design + float(ridge) * np.eye(design.shape[1])
    rhs = design.T @ logits
    return BinaryReadout(np.linalg.solve(gram, rhs))


def conformal_quantile(scores: np.ndarray, alpha: float) -> float:
    values = np.sort(np.asarray(scores, dtype=np.float64).reshape(-1))
    if values.size == 0:
        raise ValueError("calibration scores must be nonempty")
    rank = int(np.ceil((values.size + 1) * (1.0 - float(alpha))))
    rank = max(1, min(rank, values.size))
    return float(values[rank - 1])


def _true_label_nonconformity(probability_one: np.ndarray, labels: np.ndarray) -> np.ndarray:
    labels_bool = np.asarray(labels, dtype=bool)
    probabilities = np.asarray(probability_one, dtype=np.float64)
    true_probabilities = np.where(labels_bool, probabilities, 1.0 - probabilities)
    return 1.0 - true_probabilities


def _prediction_set_sizes(probability_one: np.ndarray, threshold: float) -> tuple[np.ndarray, np.ndarray]:
    probabilities = np.asarray(probability_one, dtype=np.float64)
    include_zero = probabilities <= threshold
    include_one = (1.0 - probabilities) <= threshold
    sizes = include_zero.astype(np.int64) + include_one.astype(np.int64)
    singleton_prediction = np.where(include_one, 1, 0)
    return sizes, singleton_prediction.astype(bool)


def evaluate_conformal_certificate(
    *,
    readout: BinaryReadout,
    calibration_features: np.ndarray,
    calibration_labels: np.ndarray,
    test_features: np.ndarray,
    test_labels: np.ndarray,
    alpha: float,
) -> dict[str, float]:
    cal_prob = readout.score(calibration_features)
    test_prob = readout.score(test_features)
    q_alpha = conformal_quantile(_true_label_nonconformity(cal_prob, calibration_labels), alpha)
    set_sizes, singleton_predictions = _prediction_set_sizes(test_prob, q_alpha)
    labels = np.asarray(test_labels, dtype=bool)
    singleton = set_sizes == 1
    contains_true = np.where(labels, (1.0 - test_prob) <= q_alpha, test_prob <= q_alpha)
    singleton_wrong = singleton & (singleton_predictions != labels)
    singleton_count = int(np.sum(singleton))
    coverage = float(np.mean(singleton)) if labels.size else 0.0
    unlogged = float(np.mean(singleton_wrong)) if labels.size else 0.0
    conformal_miscoverage = float(np.mean(~contains_true)) if labels.size else 0.0
    outside_gap_accuracy = (
        float(np.mean(singleton_predictions[singleton] == labels[singleton]))
        if singleton_count
        else 0.0
    )
    return {
        "alpha": float(alpha),
        "q_alpha": q_alpha,
        "certified_coverage": coverage,
        "singleton_claim_rate": coverage,
        "gap_rate": float(1.0 - coverage),
        "unlogged_error": unlogged,
        "conformal_miscoverage": conformal_miscoverage,
        "outside_gap_accuracy": outside_gap_accuracy,
        "test_count": float(labels.size),
        "singleton_count": float(singleton_count),
    }


def certify_latent_claim(split: LatentCarrierSplit, *, alphas: Iterable[float] = ALPHAS) -> dict[str, Any]:
    readout = fit_binary_readout(split.features_train, split.labels_train)
    sweep = [
        evaluate_conformal_certificate(
            readout=readout,
            calibration_features=split.features_calibration,
            calibration_labels=split.labels_calibration,
            test_features=split.features_test,
            test_labels=split.labels_test,
            alpha=alpha,
        )
        for alpha in alphas
    ]
    primary = next(row for row in sweep if abs(float(row["alpha"]) - PRIMARY_ALPHA) < 1e-12)
    claim_status = (
        "certified"
        if (
            float(primary["certified_coverage"]) >= MIN_SINGLETON_COVERAGE
            and float(primary["unlogged_error"]) <= PRIMARY_ALPHA
            and float(primary["conformal_miscoverage"]) <= PRIMARY_ALPHA
        )
        else "coverage_gap"
    )
    return {
        "carrier_id": split.carrier_id,
        "source": split.source,
        "predicate": split.predicate,
        "test_surface": split.test_surface,
        "stability_condition": split.stability_condition,
        "gap_policy": split.gap_policy,
        "alpha": PRIMARY_ALPHA,
        "claim_status": claim_status,
        "primary": primary,
        "sweep": sweep,
        "train_count": float(split.labels_train.shape[0]),
        "calibration_count": float(split.labels_calibration.shape[0]),
        "test_count": float(split.labels_test.shape[0]),
        "debt_decomposition": {
            "silent_error_debt": float(primary["unlogged_error"]),
            "coverage_debt": float(1.0 - primary["certified_coverage"]),
            "source_debt": 0.0,
            "planning_risk_debt": 0.0,
        },
        "claim_rule": "emit singleton conformal label only when the prediction set has size one; otherwise ledger gap",
        "cannot_claim": [
            "natural-language semantic grounding",
            "public benchmark superiority",
            "native V-JEPA2-AC checkpoint reproduction",
        ],
    }


def source_gap_claim(
    *,
    carrier_id: str,
    source: str,
    predicate: str,
    test_surface: str,
    stability_condition: str,
    reason: str,
) -> dict[str, Any]:
    return {
        "carrier_id": carrier_id,
        "source": source,
        "predicate": predicate,
        "test_surface": test_surface,
        "stability_condition": stability_condition,
        "gap_policy": "ledger source gap before issuing any singleton claim",
        "alpha": PRIMARY_ALPHA,
        "claim_status": "source_gap",
        "reason": reason,
        "primary": None,
        "sweep": [],
        "train_count": 0.0,
        "calibration_count": 0.0,
        "test_count": 0.0,
        "debt_decomposition": {
            "silent_error_debt": 0.0,
            "coverage_debt": 1.0,
            "source_debt": 1.0,
            "planning_risk_debt": 0.0,
        },
        "cannot_claim": [
            "certified operational claim",
            "natural-language semantic grounding",
            "public benchmark superiority",
        ],
    }


def _dependency_status() -> dict[str, str]:
    return {
        name: "installed" if importlib.util.find_spec(name) is not None else "missing"
        for name in ("gymnasium", "minigrid")
    }


def _build_minigrid_carrier_split(
    *,
    environment_id: str,
    seed: int,
    train_count: int,
    calibration_count: int,
    test_count: int,
) -> LatentCarrierSplit:
    train_cal, _, _ = _collect_examples(
        environment_id=environment_id,
        sample_count=train_count + calibration_count,
        planning_state_count=0,
        seed=seed,
    )
    test, _, _ = _collect_examples(
        environment_id=environment_id,
        sample_count=test_count,
        planning_state_count=0,
        seed=seed + 1,
    )
    return LatentCarrierSplit(
        carrier_id="public-minigrid-native-feature-carrier",
        source="MiniGrid image/action stream generated by public_minigrid_native_benchmark._collect_examples",
        features_train=train_cal["features"][:train_count],
        labels_train=train_cal["labels"][:train_count],
        features_calibration=train_cal["features"][train_count:],
        labels_calibration=train_cal["labels"][train_count:],
        features_test=test["features"],
        labels_test=test["labels"],
        predicate="door_key_context_visible",
        test_surface="action-conditioned next-image readback for visible key, door, or goal context",
        stability_condition="disjoint train/calibration/test seeds over the same public MiniGrid environment",
        gap_policy="split conformal prediction set; non-singleton sets are ledgered as gap",
    )


def build_latent_claim_certificate_artifacts(
    *,
    environment_id: str = DEFAULT_ENVIRONMENT_ID,
    seed: int = 20260607,
    train_count: int = 128,
    calibration_count: int = 128,
    test_count: int = 128,
) -> tuple[dict[str, Any], dict[str, Any], dict[str, Any]]:
    deps = _dependency_status()
    carrier_id = "public-minigrid-native-feature-carrier"
    claims: list[dict[str, Any]]
    if all(status == "installed" for status in deps.values()):
        split = _build_minigrid_carrier_split(
            environment_id=environment_id,
            seed=seed,
            train_count=train_count,
            calibration_count=calibration_count,
            test_count=test_count,
        )
        claims = [certify_latent_claim(split)]
    else:
        claims = [
            source_gap_claim(
                carrier_id=carrier_id,
                source=environment_id,
                predicate="door_key_context_visible",
                test_surface="action-conditioned next-image readback",
                stability_condition="disjoint train/calibration/test seeds",
                reason="MiniGrid dependencies are not installed, so the source split cannot be collected",
            )
        ]

    claims.extend(
        [
            source_gap_claim(
                carrier_id=carrier_id,
                source=environment_id,
                predicate="has_key",
                test_surface="pickup intervention changes carried-key state",
                stability_condition="inventory-state source split",
                reason="the current image/action evidence record does not expose an inventory or carried-object trace",
            ),
            source_gap_claim(
                carrier_id=carrier_id,
                source=environment_id,
                predicate="door_open_or_unlocked",
                test_surface="toggle intervention changes door transition state",
                stability_condition="door-state source split",
                reason="the current native MiniGrid evidence record does not preserve a separate door-state label split",
            ),
            source_gap_claim(
                carrier_id=carrier_id,
                source=environment_id,
                predicate="goal_reachable_with_current_state",
                test_surface="planner feasibility under current known state",
                stability_condition="environment-graph source split",
                reason="the current evidence record does not expose a graph-level reachability source split",
            ),
        ]
    )
    sweep_rows = [
        {
            "carrier_id": claim["carrier_id"],
            "predicate": claim["predicate"],
            **row,
        }
        for claim in claims
        for row in claim.get("sweep", [])
    ]
    audit_checks = []
    for claim in claims:
        source_ok = claim["claim_status"] != "source_gap"
        certificate_ok = bool(claim.get("sweep"))
        primary = claim.get("primary") or {}
        coverage_ok = bool(primary) and float(primary.get("certified_coverage", 0.0)) >= MIN_SINGLETON_COVERAGE
        uer_ok = bool(primary) and float(primary.get("unlogged_error", 1.0)) <= PRIMARY_ALPHA
        miscoverage_ok = bool(primary) and float(primary.get("conformal_miscoverage", 1.0)) <= PRIMARY_ALPHA
        audit_checks.append(
            {
                "carrier_id": claim["carrier_id"],
                "predicate": claim["predicate"],
                "source_split_declared": source_ok,
                "latent_carrier_frozen": True,
                "test_surface_declared": bool(claim["test_surface"]),
                "conformal_certificate_computed": certificate_ok,
                "singleton_coverage_reported": bool(primary),
                "unlogged_error_reported": bool(primary),
                "conformal_miscoverage_within_alpha": miscoverage_ok,
                "stability_test_declared": bool(claim["stability_condition"]),
                "fail_closed_gap_recorded": claim["claim_status"] != "certified",
                "accepted_as_operational_name": source_ok and certificate_ok and coverage_ok and uer_ok and miscoverage_ok,
            }
        )
    certificates = {
        "schema_id": "bedc-latent-claim-certificates",
        "status": "executed" if any(claim["claim_status"] == "certified" for claim in claims) else "gap_only",
        "protocol": "Latent Claim Certificate Protocol",
        "environment_id": environment_id,
        "risk_level": PRIMARY_ALPHA,
        "dependency_status": deps,
        "claims": claims,
        "cannot_claim": [
            "public benchmark superiority",
            "native V-JEPA2-AC checkpoint reproduction",
            "natural-language semantic grounding",
            "global latent interpretability",
        ],
    }
    sweep = {
        "schema_id": "bedc-conformal-gap-sweep",
        "status": "executed" if sweep_rows else "source_gap",
        "alphas": [float(alpha) for alpha in ALPHAS],
        "rows": sweep_rows,
    }
    audit = {
        "schema_id": "bedc-claim-boundary-audit",
        "status": "executed",
        "protocol": "Latent Claim Certificate Protocol",
        "audit_checks": audit_checks,
        "accepted_claim_count": float(sum(1 for row in audit_checks if row["accepted_as_operational_name"])),
        "gap_claim_count": float(sum(1 for claim in claims if claim["claim_status"] != "certified")),
        "claim_rule": "certify singleton conformal claims; otherwise ledger source, coverage, or stability gap",
    }
    return certificates, sweep, audit


def write_latent_claim_certificate_artifacts(report_dir: str | Path = REPORTS) -> tuple[Path, Path, Path]:
    certificates, sweep, audit = build_latent_claim_certificate_artifacts()
    target_dir = Path(report_dir)
    target_dir.mkdir(parents=True, exist_ok=True)
    paths_payloads = (
        (target_dir / "bedc_latent_claim_certificates.json", certificates),
        (target_dir / "bedc_conformal_gap_sweep.json", sweep),
        (target_dir / "bedc_claim_boundary_audit.json", audit),
    )
    for path, payload in paths_payloads:
        path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return tuple(path for path, _ in paths_payloads)
