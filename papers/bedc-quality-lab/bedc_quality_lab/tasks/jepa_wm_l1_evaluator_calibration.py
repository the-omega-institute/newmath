"""Evaluator calibration for the JEPA-WM-L1 rank surface."""

from __future__ import annotations

from datetime import datetime, timezone
import json
from pathlib import Path
import platform
from typing import Any, Mapping, Sequence

import numpy as np

from bedc_quality_lab.tasks import jepa_wm_l1 as admission


SCHEMA_ID = "bedc-quality-lab:jepa-wm-l1-evaluator-calibration"
ARTIFACT_ID = "bedc-quality-lab:jepa-wm-l1-evaluator-calibration"
FINGERPRINT_SCHEMA_ID = admission.FINGERPRINT_SCHEMA_ID
JSON_ARTIFACT = "reports/canonical/jepa-wm-l1-evaluator-calibration.json"
MARKDOWN_ARTIFACT = "reports/canonical/jepa-wm-l1-evaluator-calibration.md"
FINGERPRINT_ARTIFACT = "reports/canonical/jepa-wm-l1-evaluator-calibration.fingerprint.json"
DEFAULT_GENERATED_AT = admission.DEFAULT_GENERATED_AT
DEFAULT_SEED = admission.DEFAULT_SEED
DEFAULT_CASE_COUNT = admission.DEFAULT_CASE_COUNT
DEFAULT_BOOTSTRAP_RESAMPLES = admission.DEFAULT_BOOTSTRAP_RESAMPLES
CALIBRATION_ARM_ORDER = ("raw", "frozen-probe", "oracle", "label-shuffle")
VALIDATION_GATE_KEYS = (
    "status",
    "criterion",
    "margin",
    "base",
    "empirical_chance",
    "chance_selected_baseline",
    "chance_components",
    "ci_margin_delta",
)


def fixture_encoded_surface(batch: admission.RankCaseBatch) -> admission.EncodedRankSurface:
    n = int(batch.true_indices.shape[0])
    contexts = batch.context_videos.reshape(n, -1).astype(np.float64)
    candidates = batch.candidate_videos.reshape(n, admission.CHOICE_COUNT, -1).astype(np.float64)
    return admission.EncodedRankSurface(contexts=contexts, candidates=candidates)


def validation_indices(batch: admission.RankCaseBatch, *, seed: int) -> np.ndarray:
    count = int(batch.true_indices.shape[0])
    permutation = np.random.default_rng(seed + 1542).permutation(count)
    validation_count = max(1, count // 2)
    return np.sort(permutation[-validation_count:])


def _train_indices(batch: admission.RankCaseBatch, validation: np.ndarray) -> np.ndarray:
    mask = np.ones(int(batch.true_indices.shape[0]), dtype=bool)
    mask[np.asarray(validation, dtype=np.int64)] = False
    return np.flatnonzero(mask)


def _subset_batch(batch: admission.RankCaseBatch, indices: np.ndarray) -> admission.RankCaseBatch:
    selected = np.asarray(indices, dtype=np.int64)
    return admission.RankCaseBatch(
        context_videos=batch.context_videos[selected],
        candidate_videos=batch.candidate_videos[selected],
        true_indices=batch.true_indices[selected],
        metadata=[batch.metadata[int(index)] for index in selected],
    )


def frozen_probe_cells(
    batch: admission.RankCaseBatch,
    encoded_surface: admission.EncodedRankSurface,
    *,
    train_indices: np.ndarray,
    validation_indices_: np.ndarray,
) -> np.ndarray:
    train = np.asarray(train_indices, dtype=np.int64)
    validation = np.asarray(validation_indices_, dtype=np.int64)
    if train.size == 0:
        train = validation
    x_train = admission._l2_normalize(encoded_surface.contexts[train])
    candidate_train = encoded_surface.candidates[train]
    y_train = admission._l2_normalize(candidate_train[np.arange(train.size), batch.true_indices[train]])
    ridge = 1e-3
    dual_gram = x_train @ x_train.T + ridge * np.eye(train.size, dtype=np.float64)
    alpha = np.linalg.solve(dual_gram, y_train)
    projected = admission._l2_normalize(encoded_surface.contexts[validation] @ x_train.T @ alpha)
    candidates = admission._l2_normalize(encoded_surface.candidates[validation])
    scores = np.einsum("nd,nkd->nk", projected, candidates)
    predictions = np.argmax(scores, axis=1)
    return (predictions == batch.true_indices[validation]).astype(np.float64)


def oracle_cells(batch: admission.RankCaseBatch) -> np.ndarray:
    return np.ones(int(batch.true_indices.shape[0]), dtype=np.float64)


def label_shuffle_cells(batch: admission.RankCaseBatch, *, seed: int) -> np.ndarray:
    rng = np.random.default_rng(seed + 1542)
    shuffled = np.asarray(batch.true_indices, dtype=np.int64).copy()
    if shuffled.size > 1:
        shuffled = shuffled[rng.permutation(shuffled.size)]
    return (shuffled == batch.true_indices).astype(np.float64)


def _arm_result(
    arm_id: str,
    *,
    cells: np.ndarray,
    chance_components: Mapping[str, np.ndarray],
    seed: int,
    bootstrap_resamples: int,
    scorer: str,
    input_pointer: str,
) -> dict[str, Any]:
    gate = admission.base_chance_gate(
        np.asarray(cells, dtype=np.float64),
        chance_components,
        seed=seed,
        bootstrap_resamples=bootstrap_resamples,
    )
    normalized_gate = {key: gate[key] for key in VALIDATION_GATE_KEYS}
    return {
        "arm_id": arm_id,
        "scorer": scorer,
        "input_pointer": input_pointer,
        "n": int(np.asarray(cells).shape[0]),
        "mean": float(np.mean(cells)) if np.asarray(cells).size else 0.0,
        "validation_gate": normalized_gate,
        "claim_allowed": False,
        "interpretation": "diagnostic calibration only",
    }


def evaluate_calibration_arms(
    batch: admission.RankCaseBatch,
    encoded_surface: admission.EncodedRankSurface,
    raw_rank: Mapping[str, Any],
    *,
    seed: int,
    bootstrap_resamples: int,
) -> list[dict[str, Any]]:
    validation = validation_indices(batch, seed=seed)
    train = _train_indices(batch, validation)
    validation_batch = _subset_batch(batch, validation)
    chance = admission.chance_eval(validation_batch.true_indices, seed=seed + 1000)
    raw_cells = np.asarray(raw_rank["correct"], dtype=np.float64)
    arm_cells = {
        "raw": raw_cells[validation],
        "frozen-probe": frozen_probe_cells(
            batch,
            encoded_surface,
            train_indices=train,
            validation_indices_=validation,
        ),
        "oracle": oracle_cells(validation_batch),
        "label-shuffle": label_shuffle_cells(validation_batch, seed=seed),
    }
    scorers = {
        "raw": "admission.evaluate_encoded_rank_cases",
        "frozen-probe": "frozen-ridge-probe",
        "oracle": "true-label-upper-bound",
        "label-shuffle": "shuffled-label-negative-control",
    }
    pointers = {
        "raw": "$.raw_admission",
        "frozen-probe": "$.calibration_inputs.frozen_probe",
        "oracle": "$.calibration_inputs.oracle",
        "label-shuffle": "$.calibration_inputs.label_shuffle",
    }
    return [
        _arm_result(
            arm,
            cells=arm_cells[arm],
            chance_components=chance,
            seed=seed + 1100 + index,
            bootstrap_resamples=bootstrap_resamples,
            scorer=scorers[arm],
            input_pointer=pointers[arm],
        )
        for index, arm in enumerate(CALIBRATION_ARM_ORDER)
    ]


def _hardgate(calibration_arms: Sequence[Mapping[str, Any]]) -> dict[str, Any]:
    gates = {
        f"CAL-{index}": {
            "status": "diagnostic-only",
            "arm_id": arm["arm_id"],
            "validation_status": arm["validation_gate"]["status"],
            "claim_allowed": False,
            "evidence_pointer": f"$.calibration_arms[{index - 1}].validation_gate",
        }
        for index, arm in enumerate(calibration_arms, start=1)
    }
    return {
        "status": "diagnostic-only",
        "status_cell": "fail",
        "gate_shape": list(VALIDATION_GATE_KEYS),
        "gates": gates,
        "claim_allowed": False,
    }


def _reproducibility_contract(seed: int, status: str) -> dict[str, Any]:
    return {
        "schema_id": "bedc-quality-lab:canonical-reproducibility-contract",
        "mode": "exact_fixture",
        "seed_list": [int(seed)],
        "metric_bands": [
            {
                "pointer": "$.diagnostic_next_step.status",
                "reference_value": status,
                "tolerance": 0,
                "comparison": "status_equal",
                "owner": "jepa-wm-l1-evaluator-calibration",
                "calibration_source": "$.calibration_arms",
                "seed_basis": {"seed_count": 1, "source": "$.config.seeds"},
            }
        ],
        "device_policy": {
            "requested_device": "cpu",
            "resolved_device": "cpu",
            "resolution_status": "available",
            "resolution_reason": "fixture calibration uses deterministic numpy surfaces",
            "backend_details": {"torch": "not-requested", "numpy": np.__version__},
        },
        "framework_provenance": {
            "python": platform.python_version(),
            "dependency_abi": {"torch": "not-requested", "numpy": np.__version__},
        },
        "calibration": {
            "calibration_source": "$.calibration_arms",
            "owner": "jepa-wm-l1-evaluator-calibration",
            "basis": "four scorer arms over the admission owner rank cases",
        },
    }


def build_payload(
    *,
    generated_at: str | None = None,
    case_count: int = DEFAULT_CASE_COUNT,
    seed: int = DEFAULT_SEED,
    bootstrap_resamples: int = DEFAULT_BOOTSTRAP_RESAMPLES,
    batch: admission.RankCaseBatch | None = None,
    encoded_surface: admission.EncodedRankSurface | None = None,
    raw_rank: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    timestamp = generated_at or DEFAULT_GENERATED_AT
    bounded_case_count = int(max(100, min(500, case_count)))
    rank_batch = batch if batch is not None else admission.make_rank_cases(case_count=bounded_case_count, seed=seed)
    surface = encoded_surface if encoded_surface is not None else fixture_encoded_surface(rank_batch)
    rank = raw_rank if raw_rank is not None else admission.evaluate_encoded_rank_cases(rank_batch, surface)
    arms = evaluate_calibration_arms(
        rank_batch,
        surface,
        rank,
        seed=seed,
        bootstrap_resamples=bootstrap_resamples,
    )
    diagnostic_status = "diagnostic-routing-recorded"
    payload = {
        "schema_id": SCHEMA_ID,
        "artifact_id": ARTIFACT_ID,
        "generated_at": timestamp,
        "run_id": "jepa-wm-l1-evaluator-calibration",
        "producer": "bedc_quality_lab.tasks.jepa_wm_l1_evaluator_calibration",
        "canonical_role": "diagnostic_evaluator_calibration",
        "source_issue": "#1542",
        "source_artifacts": {
            "cost_protocol": "configs/default_cost_protocol.yaml",
            "admission_owner": admission.JSON_ARTIFACT,
            "admission_module": "bedc_quality_lab.tasks.jepa_wm_l1",
        },
        "admission_owner": {
            "producer": "bedc_quality_lab.tasks.jepa_wm_l1",
            "json_artifact": admission.JSON_ARTIFACT,
            "markdown_artifact": admission.MARKDOWN_ARTIFACT,
            "owned_semantics": [
                "rank_cases",
                "k=7",
                "empirical_chance",
                "base_chance_gate",
                "controls",
                "weight_acquisition",
                "raw_admission_verdict",
            ],
        },
        "config": {
            "seed": int(seed),
            "seeds": [int(seed)],
            "case_count": int(rank_batch.true_indices.shape[0]),
            "negative_count": admission.NEGATIVE_COUNT,
            "choice_count": admission.CHOICE_COUNT,
            "base_chance_margin": admission.BASE_CHANCE_MARGIN,
            "bootstrap_resamples": int(bootstrap_resamples),
        },
        "calibration_inputs": {
            "rank_case_source": "admission.make_rank_cases",
            "encoded_surface_source": "fixture_encoded_surface",
            "split": {
                "status": "deterministic",
                "train_fraction": 0.5,
                "validation_fraction": 0.5,
                "seed": int(seed + 1542),
            },
            "frozen_probe": {
                "status": "deterministic",
                "training_rule": "ridge projection from frozen context features to true candidate features",
                "feature_owner": "admission.EncodedRankSurface",
            },
            "oracle": {"status": "deterministic", "label_access": "true_index"},
            "label_shuffle": {"status": "deterministic", "seed": int(seed + 1542)},
        },
        "raw_admission": {
            "score_source": "admission.evaluate_encoded_rank_cases",
            "top1_accuracy": float(rank["top1_accuracy"]),
            "mean_rank": float(rank["mean_rank"]),
            "sample_count": int(np.asarray(rank["correct"]).shape[0]),
        },
        "calibration_arms": arms,
        "hardgate": _hardgate(arms),
        "claim_boundary": {
            "status": "not-applicable",
            "diagnostic_status": "diagnostic-only",
            "scope": "four-arm evaluator calibration over admission-owned rank cases",
            "claim_allowed": False,
        },
        "diagnostic_next_step": {
            "status": "not-applicable",
            "routing_status": diagnostic_status,
            "route": "inspect evaluator scorer separation before any admission rerun",
            "claim_allowed": False,
            "cascade_triggered": False,
        },
        "positive_claim": {
            "status": "not-applicable",
            "positive_discovery": False,
            "level": "not-applicable",
        },
        "not_claimed": [
            "No DRT or DGT cascade is triggered by this evaluator calibration.",
            "No downstream capability claim is produced.",
            "No admission verdict is changed by this evaluator calibration.",
            "No second owner is created for k, chance, controls, weight acquisition, or raw admission semantics.",
        ],
        "reproducibility_contract": _reproducibility_contract(seed, diagnostic_status),
    }
    payload["raw_digest"] = admission.canonical_digest(
        {
            "admission_owner": payload["admission_owner"],
            "config": payload["config"],
            "calibration_arms": payload["calibration_arms"],
            "diagnostic_next_step": payload["diagnostic_next_step"],
        }
    )
    return payload


def render_markdown(payload: Mapping[str, Any]) -> str:
    lines = [
        "# JEPA-WM-L1 Evaluator Calibration",
        "",
        f"- Generated at: `{payload.get('generated_at')}`",
        f"- Producer: `{payload.get('producer')}`",
        f"- Admission owner: `{payload.get('admission_owner', {}).get('producer')}`",
        f"- Diagnostic route: `{payload.get('diagnostic_next_step', {}).get('route')}`",
        "- Boundary: diagnostic only; no cascade and no capability claim.",
        "",
        "## Calibration Arms",
        "",
        "| arm | scorer | gate | mean |",
        "| --- | --- | --- | --- |",
    ]
    for arm in payload.get("calibration_arms", []):
        gate = arm.get("validation_gate", {}) if isinstance(arm, Mapping) else {}
        lines.append(
            f"| `{arm.get('arm_id')}` | `{arm.get('scorer')}` | `{gate.get('status')}` | `{arm.get('mean')}` |"
        )
    lines.extend(["", "## Not Claimed", ""])
    for item in payload.get("not_claimed", []):
        lines.append(f"- {item}")
    lines.append("")
    return "\n".join(lines)


def fingerprint_payload(payload: Mapping[str, Any], *, generated_at: str) -> dict[str, Any]:
    return {
        "schema_id": FINGERPRINT_SCHEMA_ID,
        "report_name": "jepa-wm-l1-evaluator-calibration",
        "json_artifact": JSON_ARTIFACT,
        "markdown_artifact": MARKDOWN_ARTIFACT,
        "producer_command": ["python3", "scripts/run_jepa_wm_l1_evaluator_calibration.py"],
        "input_fingerprint": admission.canonical_digest(
            {
                "producer": "bedc_quality_lab.tasks.jepa_wm_l1_evaluator_calibration",
                "admission_owner": payload.get("admission_owner"),
                "config": payload.get("config"),
                "calibration_inputs": payload.get("calibration_inputs"),
            }
        ),
        "inputs": {
            "admission_owner": payload.get("admission_owner"),
            "source_artifacts": payload.get("source_artifacts"),
        },
        "reproducibility_mode": "exact_fixture",
        "reproducibility_contract": payload.get("reproducibility_contract"),
        "reproducibility_contract_digest": admission.canonical_digest(payload.get("reproducibility_contract")),
        "generated_by": {
            "runner": "scripts/run_jepa_wm_l1_evaluator_calibration.py",
            "generated_at": generated_at,
        },
    }


def write_artifacts(
    *,
    root: str | Path = ".",
    json_path: str | Path | None = None,
    markdown_path: str | Path | None = None,
    fingerprint_path: str | Path | None = None,
    generated_at: str | None = None,
    case_count: int = DEFAULT_CASE_COUNT,
    seed: int = DEFAULT_SEED,
    bootstrap_resamples: int = DEFAULT_BOOTSTRAP_RESAMPLES,
) -> dict[str, Any]:
    root_path = Path(root)
    payload = build_payload(
        generated_at=generated_at,
        case_count=case_count,
        seed=seed,
        bootstrap_resamples=bootstrap_resamples,
    )
    target_json = Path(json_path) if json_path is not None else root_path / JSON_ARTIFACT
    target_md = Path(markdown_path) if markdown_path is not None else root_path / MARKDOWN_ARTIFACT
    target_fingerprint = Path(fingerprint_path) if fingerprint_path is not None else root_path / FINGERPRINT_ARTIFACT
    target_json.parent.mkdir(parents=True, exist_ok=True)
    target_md.parent.mkdir(parents=True, exist_ok=True)
    target_fingerprint.parent.mkdir(parents=True, exist_ok=True)
    target_json.write_text(
        json.dumps(payload, indent=2, sort_keys=True, default=admission._json_default) + "\n",
        encoding="utf-8",
    )
    target_md.write_text(render_markdown(payload), encoding="utf-8")
    fingerprint = fingerprint_payload(
        payload,
        generated_at=generated_at or datetime.now(timezone.utc).isoformat(),
    )
    target_fingerprint.write_text(
        json.dumps(fingerprint, indent=2, sort_keys=True, default=admission._json_default) + "\n",
        encoding="utf-8",
    )
    return payload
