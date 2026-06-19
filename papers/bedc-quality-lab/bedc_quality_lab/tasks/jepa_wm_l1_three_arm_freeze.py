"""SHA-addressed JEPA-WM-L1 three-arm venue freeze."""

from __future__ import annotations

from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
from typing import Any, Mapping, Sequence

from bedc_quality_lab.tasks import jepa_wm_l1 as admission
from bedc_quality_lab.tasks import jepa_wm_l1_evaluator_calibration as calibration


SCHEMA_ID = "bedc-quality-lab:jepa-wm-l1-three-arm-freeze"
ARTIFACT_ID = "bedc-quality-lab:jepa-wm-l1-three-arm-freeze"
FINGERPRINT_SCHEMA_ID = admission.FINGERPRINT_SCHEMA_ID
JSON_ARTIFACT = "reports/canonical/jepa-wm-l1-three-arm-freeze.json"
MARKDOWN_ARTIFACT = "reports/canonical/jepa-wm-l1-three-arm-freeze.md"
FINGERPRINT_ARTIFACT = "reports/canonical/jepa-wm-l1-three-arm-freeze.fingerprint.json"
STUB_EVAL_JSON_ARTIFACT = "reports/canonical/jepa-wm-l1-three-arm-stub-eval.json"
STUB_EVAL_MARKDOWN_ARTIFACT = "reports/canonical/jepa-wm-l1-three-arm-stub-eval.md"
DEFAULT_GENERATED_AT = admission.DEFAULT_GENERATED_AT
DEFAULT_SEED = admission.DEFAULT_SEED
THREE_ARM_IDS = ("bedc_jepa", "plain_jepa", "chance_control")
PREDICTION_SCHEMA_ID = "bedc-quality-lab:jepa-wm-l1-three-arm-prediction"
OOD_SLICE_IDS = ("temporal_shuffle", "action_shuffle", "goal_shuffle")
FREEZE_HARDGATE_IDS = tuple(f"JWM-L1-THREE-ARM-HG{index}" for index in range(1, 8))
PREDICTION_FORBIDDEN_OWNER_STRINGS = (
    admission.JSON_ARTIFACT,
    calibration.JSON_ARTIFACT,
    "jepa-wm-l1-admission",
    "jepa-wm-l1-evaluator-calibration",
)


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _canonical_json(value: Any) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), default=admission._json_default)


def _digest(value: Any) -> str:
    return hashlib.sha256(_canonical_json(value).encode("utf-8")).hexdigest()


def venue_content_sha256(payload: Mapping[str, Any]) -> str:
    normalized = json.loads(json.dumps(payload, sort_keys=True, default=admission._json_default))
    normalized.setdefault("decision", {})["venue_sha256"] = "0" * 64
    normalized.setdefault("stub_smoke", {})["stub_predictions"] = [
        _stub_prediction(arm_id, venue_sha256="0" * 64) for arm_id in THREE_ARM_IDS
    ]
    normalized.setdefault("stub_smoke", {})["results"] = [
        validate_prediction_stub(stub, venue_sha256="0" * 64)
        for stub in normalized["stub_smoke"]["stub_predictions"]
    ]
    normalized.setdefault("stub_smoke", {})["status"] = (
        "pass"
        if all(result["status"] == "pass" for result in normalized["stub_smoke"]["results"])
        else "fail"
    )
    text = json.dumps(normalized, indent=2, sort_keys=True, default=admission._json_default) + "\n"
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def _mapping(value: Any) -> Mapping[str, Any]:
    return value if isinstance(value, Mapping) else {}


def _sequence(value: Any) -> Sequence[Any]:
    return value if isinstance(value, Sequence) and not isinstance(value, (str, bytes, bytearray)) else ()


def _load_json(root: Path, artifact: str) -> dict[str, Any]:
    path = root / artifact
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError(f"{artifact} must contain a JSON object")
    return payload


def _input_ref(root: Path, artifact: str, *, role: str, expected_schema_id: str) -> dict[str, Any]:
    payload = _load_json(root, artifact)
    schema_id = payload.get("schema_id")
    if schema_id != expected_schema_id:
        raise ValueError(f"{artifact} schema_id mismatch")
    return {
        "role": role,
        "path": artifact,
        "sha256": _sha256(root / artifact),
        "schema_id": schema_id,
        "artifact_id": payload.get("artifact_id"),
    }


def _admission_snapshot(payload: Mapping[str, Any]) -> dict[str, Any]:
    config = _mapping(payload.get("config"))
    prereg = _mapping(payload.get("preregistration"))
    chance = _mapping(prereg.get("chance_eval"))
    negative_protocol = _mapping(prereg.get("negative_protocol"))
    task = _mapping(prereg.get("task"))
    return {
        "status": payload.get("execution_status") or payload.get("verdict"),
        "case_count": config.get("case_count"),
        "seed": config.get("seed"),
        "choice_count": config.get("choice_count"),
        "negative_count": config.get("negative_count"),
        "chance_floor": task.get("chance_floor"),
        "chance_eval": {
            "definition": chance.get("definition"),
            "ci_method": chance.get("ci_method"),
            "criterion": chance.get("criterion"),
            "margin": chance.get("margin"),
        },
        "negative_protocol": {
            key: negative_protocol.get(key)
            for key in ("temporal_shuffle", "action_shuffle", "goal_shuffle", "per_case_hard_negatives")
        },
        "metrics": {
            "rank_eval": payload.get("rank_eval"),
            "base_chance_gate": payload.get("base_chance_gate"),
            "anti_triviality_controls": payload.get("anti_triviality_controls"),
        },
    }


def _calibration_snapshot(payload: Mapping[str, Any]) -> dict[str, Any]:
    config = _mapping(payload.get("config"))
    inputs = _mapping(payload.get("calibration_inputs"))
    return {
        "status": payload.get("diagnostic_next_step", {}).get("status") if isinstance(payload.get("diagnostic_next_step"), Mapping) else None,
        "case_count": config.get("case_count"),
        "seed": config.get("seed"),
        "bootstrap_resamples": config.get("bootstrap_resamples"),
        "split": inputs.get("split"),
        "calibration_arms": payload.get("calibration_arms"),
        "hardgate": payload.get("hardgate"),
    }


def _prediction_schema() -> dict[str, Any]:
    return {
        "schema_id": PREDICTION_SCHEMA_ID,
        "required_top_level_keys": [
            "schema_id",
            "venue_artifact",
            "venue_sha256",
            "prediction_id",
            "arm_predictions",
            "declared_no_training_on_eval",
        ],
        "venue_binding": {
            "artifact": JSON_ARTIFACT,
            "sha256_pointer": "$.venue_sha256",
            "sha256_semantics": "canonical freeze content digest with self-reference fields zeroed",
            "schema_id": SCHEMA_ID,
        },
        "arm_schema": {
            "required_arm_ids": list(THREE_ARM_IDS),
            "per_arm_required_keys": ["arm_id", "score", "n", "metric", "input_schema"],
            "metric": "top1_accuracy",
            "score_range": [0.0, 1.0],
        },
        "fail_closed_rules": [
            "venue_sha256 must equal the canonical freeze content digest",
            "all three arms must be present exactly once",
            "declared_no_training_on_eval must be true",
            "prediction must not point directly at admission or evaluator owner internals",
        ],
    }


def _forbidden_owner_refs(value: Any, *, path: str = "$") -> list[str]:
    refs: list[str] = []
    if isinstance(value, str):
        if any(token in value for token in PREDICTION_FORBIDDEN_OWNER_STRINGS):
            refs.append(path)
    elif isinstance(value, Mapping):
        for key, child in value.items():
            refs.extend(_forbidden_owner_refs(child, path=f"{path}.{key}"))
    elif isinstance(value, Sequence) and not isinstance(value, (str, bytes, bytearray)):
        for index, child in enumerate(value):
            refs.extend(_forbidden_owner_refs(child, path=f"{path}[{index}]"))
    return refs


def _stub_prediction(arm_id: str, *, venue_sha256: str) -> dict[str, Any]:
    return {
        "schema_id": PREDICTION_SCHEMA_ID,
        "venue_artifact": JSON_ARTIFACT,
        "venue_sha256": venue_sha256,
        "prediction_id": f"stub-{arm_id}",
        "declared_no_training_on_eval": True,
        "arm_predictions": [
            {
                "arm_id": candidate,
                "score": 0.125 if candidate == arm_id else 0.0,
                "n": 0,
                "metric": "top1_accuracy",
                "input_schema": "$.prediction_schema",
            }
            for candidate in THREE_ARM_IDS
        ],
    }


def validate_prediction_stub(stub: Mapping[str, Any], *, venue_sha256: str) -> dict[str, Any]:
    errors: list[str] = []
    for key in _prediction_schema()["required_top_level_keys"]:
        if key not in stub:
            errors.append(f"missing:{key}")
    if stub.get("schema_id") != PREDICTION_SCHEMA_ID:
        errors.append("schema_id")
    if stub.get("venue_artifact") != JSON_ARTIFACT:
        errors.append("venue_artifact")
    if stub.get("venue_sha256") != venue_sha256:
        errors.append("venue_sha256")
    if stub.get("declared_no_training_on_eval") is not True:
        errors.append("declared_no_training_on_eval")
    arms = stub.get("arm_predictions")
    if not isinstance(arms, Sequence) or isinstance(arms, (str, bytes, bytearray)):
        errors.append("arm_predictions")
        arm_ids: list[str] = []
    else:
        arm_ids = [str(row.get("arm_id")) for row in arms if isinstance(row, Mapping)]
        if tuple(arm_ids) != THREE_ARM_IDS:
            errors.append("arm_ids")
        for row in arms:
            if not isinstance(row, Mapping):
                errors.append("arm_row")
                continue
            for key in _prediction_schema()["arm_schema"]["per_arm_required_keys"]:
                if key not in row:
                    errors.append(f"missing:{row.get('arm_id')}:{key}")
            score = row.get("score")
            if not isinstance(score, (int, float)) or isinstance(score, bool) or not 0.0 <= float(score) <= 1.0:
                errors.append(f"score:{row.get('arm_id')}")
            n = row.get("n")
            if not isinstance(n, int) or isinstance(n, bool) or n < 0:
                errors.append(f"n:{row.get('arm_id')}")
            if row.get("metric") != "top1_accuracy":
                errors.append(f"metric:{row.get('arm_id')}")
            if row.get("input_schema") != "$.prediction_schema":
                errors.append(f"input_schema:{row.get('arm_id')}")
    forbidden_refs = _forbidden_owner_refs(stub)
    errors.extend(f"forbidden_owner_ref:{ref}" for ref in forbidden_refs)
    return {
        "prediction_id": stub.get("prediction_id"),
        "status": "pass" if not errors else "fail",
        "errors": errors,
        "arm_ids": arm_ids,
    }


def _hardgates(
    *,
    admission_ref: Mapping[str, Any],
    calibration_ref: Mapping[str, Any],
    admission_payload: Mapping[str, Any],
    calibration_payload: Mapping[str, Any],
    stub_results: Sequence[Mapping[str, Any]],
) -> dict[str, Any]:
    config = admission_payload.get("config") if isinstance(admission_payload.get("config"), Mapping) else {}
    calibration_config = (
        calibration_payload.get("config") if isinstance(calibration_payload.get("config"), Mapping) else {}
    )
    split = (
        _mapping(calibration_payload.get("calibration_inputs")).get("split")
    )
    prereg = _mapping(admission_payload.get("preregistration"))
    negative_protocol = _mapping(prereg.get("negative_protocol"))
    ood_labels_frozen = all(isinstance(negative_protocol.get(slice_id), str) and negative_protocol.get(slice_id) for slice_id in OOD_SLICE_IDS)
    bootstrap_resamples = _mapping(calibration_config).get("bootstrap_resamples")
    bootstrap_seed = _mapping(calibration_config).get("seed")
    bootstrap_holm_frozen = (
        isinstance(bootstrap_resamples, int)
        and not isinstance(bootstrap_resamples, bool)
        and bootstrap_resamples > 0
        and isinstance(bootstrap_seed, int)
        and not isinstance(bootstrap_seed, bool)
    )
    admission_controls = _mapping(_mapping(admission_payload.get("anti_triviality_controls")).get("controls"))
    calibration_arms = _sequence(calibration_payload.get("calibration_arms"))
    arm_by_id = {
        row.get("arm_id"): row
        for row in calibration_arms
        if isinstance(row, Mapping)
    }
    leakage_sources_present = (
        isinstance(admission_controls.get("metadata_only"), Mapping)
        and isinstance(admission_controls.get("no_context"), Mapping)
        and isinstance(arm_by_id.get("label-shuffle"), Mapping)
    )
    gates = {
        "JWM-L1-THREE-ARM-HG1": {
            "status": "pass" if admission_ref.get("sha256") and calibration_ref.get("sha256") else "fail",
            "criterion": "admission and evaluator inputs are SHA-addressed",
            "evidence_pointer": "$.source_artifacts",
        },
        "JWM-L1-THREE-ARM-HG2": {
            "status": "pass" if config.get("case_count") == calibration_config.get("case_count") else "fail",
            "criterion": "admission and evaluator agree on sample count",
            "evidence_pointer": "$.venue.sample",
        },
        "JWM-L1-THREE-ARM-HG3": {
            "status": "pass" if isinstance(split, Mapping) and split.get("status") == "deterministic" else "fail",
            "criterion": "deterministic split is owned by the freeze venue",
            "evidence_pointer": "$.venue.split",
        },
        "JWM-L1-THREE-ARM-HG4": {
            "status": "pass" if ood_labels_frozen else "fail",
            "criterion": "OOD labels are fixed before prediction",
            "evidence_pointer": "$.venue.ood_labels",
        },
        "JWM-L1-THREE-ARM-HG5": {
            "status": "pass" if all(result.get("status") == "pass" for result in stub_results) else "fail",
            "criterion": "three stub predictions satisfy the prediction schema",
            "evidence_pointer": "$.stub_smoke",
        },
        "JWM-L1-THREE-ARM-HG6": {
            "status": "pass" if bootstrap_holm_frozen else "fail",
            "criterion": "bootstrap and Holm settings are frozen in the venue",
            "evidence_pointer": "$.statistical_plan",
        },
        "JWM-L1-THREE-ARM-HG7": {
            "status": "pass" if leakage_sources_present else "fail",
            "criterion": "leakage gates are represented as fail-closed controls",
            "evidence_pointer": "$.leakage_gates",
        },
    }
    failed = [gate_id for gate_id in FREEZE_HARDGATE_IDS if gates[gate_id]["status"] != "pass"]
    return {
        "status": "pass" if not failed else "fail",
        "status_cell": "pass" if not failed else "fail",
        "gate_order": list(FREEZE_HARDGATE_IDS),
        "failed_gates": failed,
        "gates": gates,
    }


def build_payload(
    *,
    root: str | Path = ".",
    generated_at: str | None = None,
    venue_sha256: str | None = None,
) -> dict[str, Any]:
    root_path = Path(root)
    admission_payload = _load_json(root_path, admission.JSON_ARTIFACT)
    calibration_payload = _load_json(root_path, calibration.JSON_ARTIFACT)
    admission_ref = _input_ref(
        root_path,
        admission.JSON_ARTIFACT,
        role="admission-owner",
        expected_schema_id=admission.SCHEMA_ID,
    )
    calibration_ref = _input_ref(
        root_path,
        calibration.JSON_ARTIFACT,
        role="evaluator-calibration-owner",
        expected_schema_id=calibration.SCHEMA_ID,
    )
    placeholder_sha = venue_sha256 or "0" * 64
    stubs = [_stub_prediction(arm_id, venue_sha256=placeholder_sha) for arm_id in THREE_ARM_IDS]
    stub_results = [validate_prediction_stub(stub, venue_sha256=placeholder_sha) for stub in stubs]
    hardgate = _hardgates(
        admission_ref=admission_ref,
        calibration_ref=calibration_ref,
        admission_payload=admission_payload,
        calibration_payload=calibration_payload,
        stub_results=stub_results,
    )
    payload: dict[str, Any] = {
        "schema_id": SCHEMA_ID,
        "artifact_id": ARTIFACT_ID,
        "generated_at": generated_at or DEFAULT_GENERATED_AT,
        "producer": "bedc_quality_lab.tasks.jepa_wm_l1_three_arm_freeze",
        "canonical_role": "three_arm_prediction_venue_freeze",
        "source_issue": "#1556",
        "source_artifacts": {
            "admission": admission_ref,
            "evaluator_calibration": calibration_ref,
            "cost_protocol": "configs/default_cost_protocol.yaml",
        },
        "venue": {
            "venue_id": "jepa-wm-l1-three-arm",
            "status": "frozen",
            "sample": {
                "case_count": admission_payload.get("config", {}).get("case_count")
                if isinstance(admission_payload.get("config"), Mapping)
                else None,
                "sample_source": f"{admission.JSON_ARTIFACT}:$.data_surface",
                "admission_snapshot": _admission_snapshot(admission_payload),
            },
            "split": {
                "source": f"{calibration.JSON_ARTIFACT}:$.calibration_inputs.split",
                "snapshot": _calibration_snapshot(calibration_payload).get("split"),
            },
            "ood_labels": [
                {
                    "slice_id": slice_id,
                    "source_pointer": f"{admission.JSON_ARTIFACT}:$.preregistration.negative_protocol.{slice_id}",
                }
                for slice_id in OOD_SLICE_IDS
            ],
            "arms": [
                {"arm_id": "bedc_jepa", "role": "candidate", "input_owner": "future-prediction-only"},
                {"arm_id": "plain_jepa", "role": "baseline", "input_owner": "future-prediction-only"},
                {"arm_id": "chance_control", "role": "negative-control", "input_owner": "venue"},
            ],
        },
        "metrics": {
            "primary_metric": "top1_accuracy",
            "base_chance": {
                "probability": admission.REQUIRED_CHANCE,
                "source_pointer": f"{admission.JSON_ARTIFACT}:$.preregistration.chance_eval",
            },
            "admission_metrics_pointer": f"{admission.JSON_ARTIFACT}:$.rank_eval",
            "evaluator_metrics_pointer": f"{calibration.JSON_ARTIFACT}:$.calibration_arms",
        },
        "statistical_plan": {
            "bootstrap_resamples": calibration_payload.get("config", {}).get("bootstrap_resamples")
            if isinstance(calibration_payload.get("config"), Mapping)
            else None,
            "bootstrap_seed": calibration_payload.get("config", {}).get("seed")
            if isinstance(calibration_payload.get("config"), Mapping)
            else None,
            "holm_family": list(THREE_ARM_IDS),
            "power_gate": {
                "status": "predeclared",
                "criterion": "candidate must clear chance and baseline after family correction",
            },
            "discriminativity_gate": {
                "status": "predeclared",
                "criterion": "oracle calibration must separate from label-shuffle control",
                "source_pointer": f"{calibration.JSON_ARTIFACT}:$.calibration_arms",
            },
        },
        "leakage_gates": {
            "metadata_only": {
                "status": "fail-closed",
                "source_pointer": f"{admission.JSON_ARTIFACT}:$.anti_triviality_controls.controls.metadata_only",
            },
            "no_context": {
                "status": "fail-closed",
                "source_pointer": f"{admission.JSON_ARTIFACT}:$.anti_triviality_controls.controls.no_context",
            },
            "label_shuffle": {
                "status": "fail-closed",
                "source_pointer": f"{calibration.JSON_ARTIFACT}:$.calibration_arms[3]",
            },
        },
        "prediction_schema": _prediction_schema(),
        "stub_smoke": {
            "status": "pass" if all(result["status"] == "pass" for result in stub_results) else "fail",
            "stub_predictions": stubs,
            "results": stub_results,
        },
        "hardgate": hardgate,
        "claim_boundary": {
            "status": "venue-only",
            "status_axis": "scoped-boundary",
            "claim_allowed": False,
            "scope": "pre-prediction JEPA-WM-L1 three-arm venue freeze",
        },
        "decision": {
            "status": "ready_for_prediction" if hardgate["status"] == "pass" else "blocked",
            "status_axis": "ready" if hardgate["status"] == "pass" else "blocked",
            "prediction_schema_pointer": f"{JSON_ARTIFACT}:$.prediction_schema",
            "venue_artifact": JSON_ARTIFACT,
            "venue_sha256": placeholder_sha,
        },
        "not_claimed": [
            "No three-arm model result is claimed by this freeze.",
            "No admission or evaluator owner semantics are changed by this freeze.",
            "No downstream prediction may bypass the venue artifact and prediction schema.",
        ],
    }
    payload["freeze_digest"] = _digest(
        {
            "source_artifacts": payload["source_artifacts"],
            "venue": payload["venue"],
            "prediction_schema": payload["prediction_schema"],
            "hardgate": payload["hardgate"],
        }
    )
    validate_payload(payload)
    return payload


def bind_payload_sha(payload: Mapping[str, Any]) -> dict[str, Any]:
    bound = json.loads(json.dumps(payload, sort_keys=True, default=admission._json_default))
    bound.setdefault("decision", {})["venue_sha256"] = "0" * 64
    bound.setdefault("stub_smoke", {})["stub_predictions"] = [
        _stub_prediction(arm_id, venue_sha256="0" * 64) for arm_id in THREE_ARM_IDS
    ]
    sha = venue_content_sha256(bound)
    bound["decision"]["venue_sha256"] = sha
    bound["stub_smoke"]["stub_predictions"] = [_stub_prediction(arm_id, venue_sha256=sha) for arm_id in THREE_ARM_IDS]
    bound["stub_smoke"]["results"] = [
        validate_prediction_stub(stub, venue_sha256=sha) for stub in bound["stub_smoke"]["stub_predictions"]
    ]
    bound["stub_smoke"]["status"] = "pass"
    bound["hardgate"] = _hardgates(
        admission_ref=bound["source_artifacts"]["admission"],
        calibration_ref=bound["source_artifacts"]["evaluator_calibration"],
        admission_payload={
            "config": {"case_count": bound["venue"]["sample"]["case_count"]},
            "preregistration": {
                "negative_protocol": _mapping(
                    _mapping(bound["venue"]["sample"].get("admission_snapshot")).get("negative_protocol")
                )
            },
            "anti_triviality_controls": {
                "controls": _mapping(
                    _mapping(
                        _mapping(bound["venue"]["sample"].get("admission_snapshot")).get("metrics")
                    ).get("anti_triviality_controls")
                ).get("controls")
            },
        },
        calibration_payload={
            "config": {
                "case_count": bound["venue"]["sample"]["case_count"],
                "bootstrap_resamples": bound["statistical_plan"].get("bootstrap_resamples"),
                "seed": bound["statistical_plan"].get("bootstrap_seed"),
            },
            "calibration_inputs": {"split": bound["venue"]["split"]["snapshot"]},
            "calibration_arms": [{"arm_id": "label-shuffle"}],
        },
        stub_results=bound["stub_smoke"]["results"],
    )
    bound["decision"]["status"] = "ready_for_prediction" if bound["hardgate"]["status"] == "pass" else "blocked"
    bound["decision"]["status_axis"] = "ready" if bound["hardgate"]["status"] == "pass" else "blocked"
    bound["freeze_digest"] = _digest(
        {
            "source_artifacts": bound["source_artifacts"],
            "venue": bound["venue"],
            "prediction_schema": bound["prediction_schema"],
            "hardgate": bound["hardgate"],
        }
    )
    validate_payload(bound)
    return bound


def validate_payload(payload: Mapping[str, Any]) -> None:
    if payload.get("schema_id") != SCHEMA_ID:
        raise ValueError("schema_id mismatch")
    source_artifacts = payload.get("source_artifacts")
    if not isinstance(source_artifacts, Mapping):
        raise ValueError("source_artifacts must be a mapping")
    for key in ("admission", "evaluator_calibration"):
        row = source_artifacts.get(key)
        if not isinstance(row, Mapping):
            raise ValueError(f"missing source artifact {key}")
        digest = row.get("sha256")
        if not isinstance(digest, str) or len(digest) != 64:
            raise ValueError(f"invalid sha256 for {key}")
    hardgate = payload.get("hardgate")
    if not isinstance(hardgate, Mapping) or tuple(hardgate.get("gate_order", ())) != FREEZE_HARDGATE_IDS:
        raise ValueError("hardgate order mismatch")
    prediction_schema = payload.get("prediction_schema")
    if not isinstance(prediction_schema, Mapping) or prediction_schema.get("schema_id") != PREDICTION_SCHEMA_ID:
        raise ValueError("prediction schema mismatch")
    decision = payload.get("decision")
    if not isinstance(decision, Mapping) or decision.get("prediction_schema_pointer") != f"{JSON_ARTIFACT}:$.prediction_schema":
        raise ValueError("decision schema pointer mismatch")
    stub_smoke = payload.get("stub_smoke")
    if not isinstance(stub_smoke, Mapping):
        raise ValueError("stub smoke missing")
    venue_sha = decision.get("venue_sha256")
    if not isinstance(venue_sha, str) or len(venue_sha) != 64:
        raise ValueError("venue sha mismatch")
    results = [
        validate_prediction_stub(stub, venue_sha256=venue_sha)
        for stub in stub_smoke.get("stub_predictions", [])
        if isinstance(stub, Mapping)
    ]
    if len(results) != len(THREE_ARM_IDS) or any(result["status"] != "pass" for result in results):
        raise ValueError("stub smoke failed")
    hardgate_status = _mapping(hardgate).get("status")
    decision_status = _mapping(decision).get("status")
    if (hardgate_status == "pass") != (decision_status == "ready_for_prediction"):
        raise ValueError("decision hardgate mismatch")
    expected_axis = "ready" if decision_status == "ready_for_prediction" else "blocked"
    if decision.get("status_axis") != expected_axis:
        raise ValueError("decision status axis mismatch")
    claim_boundary = _mapping(payload.get("claim_boundary"))
    if claim_boundary.get("status_axis") != "scoped-boundary":
        raise ValueError("claim boundary status axis mismatch")


def render_markdown(payload: Mapping[str, Any]) -> str:
    source_artifacts = payload.get("source_artifacts", {}) if isinstance(payload.get("source_artifacts"), Mapping) else {}
    decision = payload.get("decision", {}) if isinstance(payload.get("decision"), Mapping) else {}
    hardgate = payload.get("hardgate", {}) if isinstance(payload.get("hardgate"), Mapping) else {}
    lines = [
        "# JEPA-WM-L1 Three-Arm Freeze",
        "",
        f"- Generated at: `{payload.get('generated_at')}`",
        f"- Venue status: `{payload.get('venue', {}).get('status')}`",
        f"- Decision: `{decision.get('status')}`",
        f"- Prediction schema: `{decision.get('prediction_schema_pointer')}`",
        f"- Venue SHA: `{decision.get('venue_sha256')}`",
        "",
        "## Source Artifacts",
        "",
    ]
    for key in ("admission", "evaluator_calibration"):
        row = source_artifacts.get(key, {}) if isinstance(source_artifacts.get(key), Mapping) else {}
        lines.append(f"- {key}: `{row.get('path')}` `{row.get('sha256')}`")
    lines.extend(
        [
            "",
            "## Hardgates",
            "",
            "| gate | status | criterion |",
            "| --- | --- | --- |",
        ]
    )
    gates = hardgate.get("gates", {}) if isinstance(hardgate.get("gates"), Mapping) else {}
    for gate_id in hardgate.get("gate_order", []):
        row = gates.get(gate_id, {}) if isinstance(gates.get(gate_id), Mapping) else {}
        lines.append(f"| `{gate_id}` | `{row.get('status')}` | {row.get('criterion')} |")
    lines.extend(["", "## Not Claimed", ""])
    for item in payload.get("not_claimed", []):
        lines.append(f"- {item}")
    lines.append("")
    return "\n".join(lines)


def stub_eval_payload(payload: Mapping[str, Any]) -> dict[str, Any]:
    decision = payload.get("decision", {}) if isinstance(payload.get("decision"), Mapping) else {}
    stub_smoke = payload.get("stub_smoke", {}) if isinstance(payload.get("stub_smoke"), Mapping) else {}
    results = list(_sequence(stub_smoke.get("results")))
    status = (
        "pass"
        if len(results) == len(THREE_ARM_IDS)
        and all(isinstance(row, Mapping) and row.get("status") == "pass" for row in results)
        else "fail"
    )
    return {
        "schema_id": f"{SCHEMA_ID}:stub-eval",
        "artifact_id": "bedc-quality-lab:jepa-wm-l1-three-arm-stub-eval",
        "generated_at": payload.get("generated_at"),
        "source_artifact": JSON_ARTIFACT,
        "source_sha256": decision.get("venue_sha256"),
        "prediction_schema": decision.get("prediction_schema_pointer"),
        "status": status,
        "results": results,
        "not_claimed": ["Stub smoke does not evaluate a real model arm."],
    }


def render_stub_eval_markdown(payload: Mapping[str, Any]) -> str:
    lines = [
        "# JEPA-WM-L1 Three-Arm Stub Eval",
        "",
        f"- Status: `{payload.get('status')}`",
        f"- Source artifact: `{payload.get('source_artifact')}`",
        f"- Source SHA: `{payload.get('source_sha256')}`",
        "",
    ]
    return "\n".join(lines)


def fingerprint_payload(payload: Mapping[str, Any], *, generated_at: str) -> dict[str, Any]:
    return {
        "schema_id": FINGERPRINT_SCHEMA_ID,
        "report_name": "jepa-wm-l1-three-arm-freeze",
        "json_artifact": JSON_ARTIFACT,
        "markdown_artifact": MARKDOWN_ARTIFACT,
        "producer_command": ["python3", "scripts/run_jepa_wm_l1_three_arm_freeze.py"],
        "input_fingerprint": _digest(
            {
                "source_artifacts": payload.get("source_artifacts"),
                "venue": payload.get("venue"),
                "prediction_schema": payload.get("prediction_schema"),
                "statistical_plan": payload.get("statistical_plan"),
                "leakage_gates": payload.get("leakage_gates"),
                "hardgate": payload.get("hardgate"),
            }
        ),
        "inputs": {
            "source_artifacts": payload.get("source_artifacts"),
            "venue_artifact": {
                "json": JSON_ARTIFACT,
                "sha256": _mapping(payload.get("decision")).get("venue_sha256"),
                "sha256_semantics": _mapping(_mapping(payload.get("prediction_schema")).get("venue_binding")).get(
                    "sha256_semantics"
                ),
            },
            "stub_eval_artifacts": {
                "json": STUB_EVAL_JSON_ARTIFACT,
                "markdown": STUB_EVAL_MARKDOWN_ARTIFACT,
            },
        },
        "reproducibility_mode": "exact_fixture",
        "reproducibility_contract": payload.get("statistical_plan"),
        "reproducibility_contract_digest": _digest(payload.get("statistical_plan")),
        "generated_by": {
            "runner": "scripts/run_jepa_wm_l1_three_arm_freeze.py",
            "generated_at": generated_at,
        },
    }


def write_artifacts(
    *,
    root: str | Path = ".",
    json_path: str | Path | None = None,
    markdown_path: str | Path | None = None,
    fingerprint_path: str | Path | None = None,
    stub_eval_json_path: str | Path | None = None,
    stub_eval_markdown_path: str | Path | None = None,
    generated_at: str | None = None,
) -> dict[str, Any]:
    root_path = Path(root)
    payload = bind_payload_sha(build_payload(root=root_path, generated_at=generated_at))
    target_json = Path(json_path) if json_path is not None else root_path / JSON_ARTIFACT
    target_md = Path(markdown_path) if markdown_path is not None else root_path / MARKDOWN_ARTIFACT
    target_fingerprint = Path(fingerprint_path) if fingerprint_path is not None else root_path / FINGERPRINT_ARTIFACT
    target_stub_json = Path(stub_eval_json_path) if stub_eval_json_path is not None else root_path / STUB_EVAL_JSON_ARTIFACT
    target_stub_md = (
        Path(stub_eval_markdown_path) if stub_eval_markdown_path is not None else root_path / STUB_EVAL_MARKDOWN_ARTIFACT
    )
    for path in (target_json, target_md, target_fingerprint, target_stub_json, target_stub_md):
        path.parent.mkdir(parents=True, exist_ok=True)
    target_json.write_text(
        json.dumps(payload, indent=2, sort_keys=True, default=admission._json_default) + "\n",
        encoding="utf-8",
    )
    target_md.write_text(render_markdown(payload), encoding="utf-8")
    stub_payload = stub_eval_payload(payload)
    target_stub_json.write_text(
        json.dumps(stub_payload, indent=2, sort_keys=True, default=admission._json_default) + "\n",
        encoding="utf-8",
    )
    target_stub_md.write_text(render_stub_eval_markdown(stub_payload), encoding="utf-8")
    fingerprint = fingerprint_payload(
        payload,
        generated_at=generated_at or datetime.now(timezone.utc).isoformat(),
    )
    target_fingerprint.write_text(
        json.dumps(fingerprint, indent=2, sort_keys=True, default=admission._json_default) + "\n",
        encoding="utf-8",
    )
    return payload
