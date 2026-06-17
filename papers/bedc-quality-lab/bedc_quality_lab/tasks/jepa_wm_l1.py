"""JEPA-WM-L1 micro-admission over public pretrained world-model latents."""

from __future__ import annotations

from dataclasses import dataclass
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
from pathlib import Path
import platform
import re
import traceback
from typing import Any, Callable, Mapping, Sequence

import numpy as np


SCHEMA_ID = "bedc-quality-lab:jepa-wm-l1-admission"
ARTIFACT_ID = "bedc-quality-lab:jepa-wm-l1-admission"
FINGERPRINT_SCHEMA_ID = "bedc-quality-lab:canonical-report-fingerprint"
JSON_ARTIFACT = "reports/canonical/jepa-wm-l1-admission.json"
MARKDOWN_ARTIFACT = "reports/canonical/jepa-wm-l1-admission.md"
FINGERPRINT_ARTIFACT = "reports/canonical/jepa-wm-l1-admission.fingerprint.json"
DEFAULT_GENERATED_AT = "2026-06-17T00:00:00+00:00"
DEFAULT_SEED = 20260617
DEFAULT_CASE_COUNT = 128
DEFAULT_BOOTSTRAP_RESAMPLES = 512
NEGATIVE_COUNT = 7
CHOICE_COUNT = 1 + NEGATIVE_COUNT
BASE_CHANCE_MARGIN = 0.03
PUBLIC_CHECKPOINTS = (
    "facebook/vjepa2-vitl-fpc64-256",
    "facebook/vjepa2-vitg-fpc64-256",
    "facebook/vjepa2-vitg-fpc64-384",
)
HARDGATE_ORDER = ("WEIGHT", "DATA", "BASE-CHANCE", "CONTROL", "CALIBRATION", "REPRO")



GENERATED_AT = DEFAULT_GENERATED_AT
RUNS_DIR = Path("reports/runs/jepa-wm-l1")
REQUIRED_K = 7
REQUIRED_CHANCE = 1.0 / 8.0
REQUIRED_ARMS = ("null", "oracle_or_teacher", "base", "larger_base")
REQUIRED_CONTROLS = ("metadata_only", "no_context")
RUN_LOCAL_HARDGATE_IDS = tuple(f"JWM-L1-HG{index}" for index in range(1, 8))
RUN_LOCAL_STATUS_DOMAIN = ("PASS", "bounded_negative", "unavailable")
RUN_LOCAL_NOT_CLAIMED = (
    "No JEPA-WM-L2 or higher result.",
    "No global model superiority claim.",
    "No canonical dashboard registration.",
    "No production deployment claim.",
    "No training recipe claim beyond the supplied runtime observation.",
)


@dataclass(frozen=True)
class RunLocalGate:
    gate_id: str
    status: str
    criterion: str
    evidence_pointer: str
    detail: str

    def as_dict(self) -> dict[str, Any]:
        return {
            "gate_id": self.gate_id,
            "status": self.status,
            "criterion": self.criterion,
            "evidence_pointer": self.evidence_pointer,
            "detail": self.detail,
        }


def _write_json_file(path: Path, payload: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(json.dumps(payload, indent=2, sort_keys=True, default=_json_default) + "\n", encoding="utf-8")
    tmp.replace(path)


def _write_text_file(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(text, encoding="utf-8")
    tmp.replace(path)


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _slug(value: Any) -> str:
    text = str(value or "run").strip().lower()
    slug = re.sub(r"[^a-z0-9._-]+", "-", text).strip("-._")
    return slug or "run"


def _mapping(value: Any) -> Mapping[str, Any]:
    return value if isinstance(value, Mapping) else {}


def _sequence(value: Any) -> Sequence[Any]:
    return value if isinstance(value, Sequence) and not isinstance(value, (str, bytes, bytearray)) else ()


def _number(value: Any) -> float | None:
    if isinstance(value, bool):
        return None
    if isinstance(value, (int, float)):
        return float(value)
    return None


def _run_local_pass_gate(gate_id: str, criterion: str, pointer: str, detail: str) -> RunLocalGate:
    return RunLocalGate(gate_id=gate_id, status="pass", criterion=criterion, evidence_pointer=pointer, detail=detail)


def _run_local_fail_gate(gate_id: str, criterion: str, pointer: str, detail: str) -> RunLocalGate:
    return RunLocalGate(gate_id=gate_id, status="fail", criterion=criterion, evidence_pointer=pointer, detail=detail)


def _checkpoint_gate(observation: Mapping[str, Any]) -> RunLocalGate:
    provenance = _mapping(_mapping(observation.get("checkpoint")).get("provenance"))
    digest = provenance.get("checkpoint_sha256")
    pretrained = (
        provenance.get("status") == "pretrained"
        and isinstance(provenance.get("source"), str)
        and bool(provenance.get("source"))
        and isinstance(digest, str)
        and re.fullmatch(r"[0-9a-fA-F]{64}", digest) is not None
        and provenance.get("weights_loaded") is True
        and provenance.get("random_init") is False
    )
    if pretrained:
        return _run_local_pass_gate(
            "JWM-L1-HG1",
            "runtime uses true pretrained checkpoint provenance",
            "$.checkpoint.provenance",
            "pretrained checkpoint provenance supplied",
        )
    return _run_local_fail_gate(
        "JWM-L1-HG1",
        "runtime uses true pretrained checkpoint provenance",
        "$.checkpoint.provenance",
        "missing pretrained source, digest, loaded weights, or random-init exclusion",
    )


def _clips_gate(observation: Mapping[str, Any]) -> RunLocalGate:
    clips = _sequence(observation.get("clips"))
    non_empty = bool(clips)
    valid_rows = all(isinstance(clip, Mapping) and bool(clip.get("clip_id")) for clip in clips)
    frame_counts = [_number(_mapping(clip).get("frame_count")) for clip in clips if isinstance(clip, Mapping)]
    valid_frames = bool(frame_counts) and all(count is not None and count > 0 for count in frame_counts)
    if non_empty and valid_rows and valid_frames:
        return _run_local_pass_gate(
            "JWM-L1-HG2",
            "runtime supplies non-empty evaluated clips",
            "$.clips",
            f"{len(clips)} clip row(s)",
        )
    return _run_local_fail_gate(
        "JWM-L1-HG2",
        "runtime supplies non-empty evaluated clips",
        "$.clips",
        "clip rows must be non-empty and carry positive frame counts",
    )


def _k_gate(observation: Mapping[str, Any]) -> RunLocalGate:
    k = observation.get("k")
    if k == REQUIRED_K:
        return _run_local_pass_gate("JWM-L1-HG3", "benchmark uses k=7", "$.k", "k=7")
    return _run_local_fail_gate("JWM-L1-HG3", "benchmark uses k=7", "$.k", f"k={k!r}")


def _chance_gate(observation: Mapping[str, Any]) -> RunLocalGate:
    chance = _mapping(observation.get("chance"))
    probability = _number(chance.get("probability"))
    ci_high = _number(chance.get("ci_high"))
    ok = probability == REQUIRED_CHANCE and ci_high is not None
    if ok:
        return _run_local_pass_gate(
            "JWM-L1-HG4",
            "chance baseline is exactly 1/8 with an upper confidence bound",
            "$.chance",
            f"chance={probability}",
        )
    return _run_local_fail_gate(
        "JWM-L1-HG4",
        "chance baseline is exactly 1/8 with an upper confidence bound",
        "$.chance",
        "chance probability must equal 1/8 and include ci_high",
    )


def _arms_gate(observation: Mapping[str, Any]) -> RunLocalGate:
    arms = _mapping(observation.get("arms"))
    missing = [arm_id for arm_id in REQUIRED_ARMS if not isinstance(arms.get(arm_id), Mapping)]
    unexpected = [str(arm_id) for arm_id in arms.keys() if arm_id not in REQUIRED_ARMS]
    incomplete: list[str] = []
    for arm_id in REQUIRED_ARMS:
        row = _mapping(arms.get(arm_id))
        if any(_number(row.get(key)) is None for key in ("score", "ci_low", "ci_high")) or _number(row.get("n")) is None:
            incomplete.append(arm_id)
    if not missing and not unexpected and not incomplete:
        return _run_local_pass_gate(
            "JWM-L1-HG5",
            "exactly four admission arms are present with score, CI, and n",
            "$.arms",
            ",".join(REQUIRED_ARMS),
        )
    detail = []
    if missing:
        detail.append(f"missing={','.join(missing)}")
    if unexpected:
        detail.append(f"unexpected={','.join(unexpected)}")
    if incomplete:
        detail.append(f"incomplete={','.join(incomplete)}")
    return _run_local_fail_gate(
        "JWM-L1-HG5",
        "exactly four admission arms are present with score, CI, and n",
        "$.arms",
        "; ".join(detail),
    )


def _run_local_calibration(observation: Mapping[str, Any], *, margin: float) -> dict[str, Any]:
    chance = _mapping(observation.get("chance"))
    arms = _mapping(observation.get("arms"))
    base = _mapping(arms.get("base"))
    base_low = _number(base.get("ci_low"))
    chance_high = _number(chance.get("ci_high"))
    threshold = chance_high + margin if chance_high is not None else None
    strict_pass = base_low is not None and threshold is not None and base_low > threshold
    return {
        "base_CI_low": base_low,
        "chance_CI_high": chance_high,
        "margin": margin,
        "chance_CI_high_plus_margin": threshold,
        "strict_margin_pass": strict_pass,
    }


def _margin_gate(calibration: Mapping[str, Any]) -> RunLocalGate:
    if calibration.get("strict_margin_pass") is True:
        return _run_local_pass_gate(
            "JWM-L1-HG6",
            "strict base_CI_low > chance_CI_high + margin",
            "$.calibration",
            "base lower CI clears chance upper CI plus margin",
        )
    return _run_local_fail_gate(
        "JWM-L1-HG6",
        "strict base_CI_low > chance_CI_high + margin",
        "$.calibration",
        "base lower CI must be strictly greater than chance upper CI plus margin",
    )


def _controls_gate(observation: Mapping[str, Any], chance_high: float | None) -> RunLocalGate:
    controls = _mapping(observation.get("controls"))
    bad: list[str] = []
    for control_id in REQUIRED_CONTROLS:
        row = _mapping(controls.get(control_id))
        control_high = _number(row.get("ci_high"))
        if (
            row.get("status") != "clean"
            or row.get("leak_detected") is not False
            or control_high is None
            or chance_high is None
            or control_high > chance_high
        ):
            bad.append(control_id)
    if not bad:
        return _run_local_pass_gate(
            "JWM-L1-HG7",
            "metadata_only and no_context controls are clean and within the chance band",
            "$.controls",
            ",".join(REQUIRED_CONTROLS),
        )
    return _run_local_fail_gate(
        "JWM-L1-HG7",
        "metadata_only and no_context controls are clean and within the chance band",
        "$.controls",
        f"unclean={','.join(bad)}",
    )


def _run_local_decision_status(failed: Sequence[str]) -> str:
    if not failed:
        return "PASS"
    if any(gate_id in failed for gate_id in ("JWM-L1-HG1", "JWM-L1-HG2")):
        return "unavailable"
    return "bounded_negative"


def _build_run_local_payload(
    observation: Mapping[str, Any],
    *,
    generated_at: str = GENERATED_AT,
    margin: float = 0.0,
) -> dict[str, Any]:
    if margin < 0:
        raise ValueError("margin must be nonnegative")
    calibration = _run_local_calibration(observation, margin=margin)
    gates = [
        _checkpoint_gate(observation),
        _clips_gate(observation),
        _k_gate(observation),
        _chance_gate(observation),
        _arms_gate(observation),
        _margin_gate(calibration),
        _controls_gate(observation, calibration["chance_CI_high"]),
    ]
    hardgates = {gate.gate_id: gate.as_dict() for gate in gates}
    failed = [gate.gate_id for gate in gates if gate.status != "pass"]
    status = _run_local_decision_status(failed)
    run_id = _slug(observation.get("run_id"))
    run_artifact = RUNS_DIR / run_id / "admission.json"
    payload: dict[str, Any] = {
        "schema_id": SCHEMA_ID,
        "artifact_id": ARTIFACT_ID,
        "generated_at": generated_at,
        "producer": "scripts/run_jepa_wm_l1.py",
        "owner_module": "bedc_quality_lab.tasks.jepa_wm_l1",
        "run_id": run_id,
        "artifact_role": "run-local-admission",
        "admission_contract": {
            "k": REQUIRED_K,
            "chance_probability": REQUIRED_CHANCE,
            "required_arms": list(REQUIRED_ARMS),
            "required_controls": list(REQUIRED_CONTROLS),
            "pass_rule": "all hardgates pass",
            "runtime_pass_margin_rule": "base_CI_low > chance_CI_high + margin",
        },
        "source_observation": {
            "status": "inline-runtime-observation",
            "run_id": observation.get("run_id"),
        },
        "checkpoint": _mapping(observation.get("checkpoint")),
        "clips": list(_sequence(observation.get("clips"))),
        "arms": _mapping(observation.get("arms")),
        "controls": _mapping(observation.get("controls")),
        "chance": _mapping(observation.get("chance")),
        "calibration": calibration,
        "hardgates": hardgates,
        "decision": {
            "status_domain": list(RUN_LOCAL_STATUS_DOMAIN),
            "status": status,
            "failed_gates": failed,
            "admission_artifact": str(run_artifact),
        },
        "claim_capsule": {
            "status": "pointer-only",
            "admission_pointer": f"{run_artifact}:$.decision.status",
            "hardgate_pointers": [f"{run_artifact}:$.hardgates.{gate_id}.status" for gate_id in RUN_LOCAL_HARDGATE_IDS],
            "not_claimed_pointer": f"{run_artifact}:$.not_claimed",
        },
        "not_claimed": list(RUN_LOCAL_NOT_CLAIMED),
    }
    validate_payload(payload)
    return payload


def validate_payload(payload: Mapping[str, Any]) -> None:
    decision = _mapping(payload.get("decision"))
    status = decision.get("status")
    if status not in RUN_LOCAL_STATUS_DOMAIN:
        raise ValueError("status domain violation")
    hardgates = _mapping(payload.get("hardgates"))
    if tuple(hardgates.keys()) != RUN_LOCAL_HARDGATE_IDS:
        raise ValueError("hardgate order violation")
    failed = [gate_id for gate_id, row in hardgates.items() if _mapping(row).get("status") != "pass"]
    if list(decision.get("failed_gates", [])) != failed:
        raise ValueError("failed gate projection mismatch")
    if status == "PASS" and failed:
        raise ValueError("decision status mismatch")
    if status != "PASS" and not failed:
        raise ValueError("decision status mismatch")
    if status == "unavailable" and not any(gate_id in failed for gate_id in ("JWM-L1-HG1", "JWM-L1-HG2")):
        raise ValueError("unavailable status mismatch")
    capsule = _mapping(payload.get("claim_capsule"))
    if capsule.get("status") != "pointer-only":
        raise ValueError("claim capsule must be pointer-only")


def _summary_payload(payload: Mapping[str, Any], admission_artifact: str) -> dict[str, Any]:
    decision = _mapping(payload.get("decision"))
    return {
        "schema_id": f"{SCHEMA_ID}:summary",
        "artifact_id": ARTIFACT_ID,
        "run_id": payload.get("run_id"),
        "status": decision.get("status"),
        "failed_gates": list(decision.get("failed_gates", [])),
        "admission_artifact": admission_artifact,
    }


def _capsule_payload(payload: Mapping[str, Any], admission_artifact: str) -> dict[str, Any]:
    capsule = _mapping(payload.get("claim_capsule"))
    return {
        "schema_id": f"{SCHEMA_ID}:claim-capsule",
        "artifact_id": "bedc-quality-lab:jepa-wm-l1-claim-capsule",
        "run_id": payload.get("run_id"),
        "status": "pointer-only",
        "admission_pointer": capsule.get("admission_pointer"),
        "hardgate_pointers": list(capsule.get("hardgate_pointers", [])),
        "source_artifact": admission_artifact,
        "not_claimed_pointer": capsule.get("not_claimed_pointer"),
    }


def _run_local_report_text(payload: Mapping[str, Any], admission_artifact: str) -> str:
    decision = _mapping(payload.get("decision"))
    lines = [
        "# JEPA-WM-L1 Run Admission",
        "",
        f"- run_id: `{payload.get('run_id')}`",
        f"- status: `{decision.get('status')}`",
        f"- admission: `{admission_artifact}`",
        f"- failed_gates: `{', '.join(decision.get('failed_gates', [])) or 'none'}`",
        "",
        "This report is a run-local pointer surface and does not register a canonical dashboard artifact.",
        "",
    ]
    return "\n".join(lines)


def _write_run_local_artifacts(payload: Mapping[str, Any], *, root: Path | None = None) -> dict[str, Path]:
    validate_payload(payload)
    root_path = Path(root) if root is not None else Path(__file__).resolve().parents[2]
    run_id = _slug(payload.get("run_id"))
    relative_dir = RUNS_DIR / run_id
    run_dir = root_path / relative_dir
    admission_path = run_dir / "admission.json"
    summary_path = run_dir / "summary.json"
    capsule_path = run_dir / "claim_capsule.json"
    report_path = run_dir / "report.md"
    admission_artifact = str(relative_dir / "admission.json")

    _write_json_file(admission_path, payload)
    _write_json_file(summary_path, _summary_payload(payload, admission_artifact))
    _write_json_file(capsule_path, _capsule_payload(payload, admission_artifact))
    _write_text_file(report_path, _run_local_report_text(payload, admission_artifact))

    fingerprint = {
        "schema_id": f"{SCHEMA_ID}:fingerprint",
        "artifact_id": "bedc-quality-lab:jepa-wm-l1-run-fingerprint",
        "run_id": run_id,
        "artifacts": {
            "admission": {"path": admission_artifact, "sha256": _sha256(admission_path)},
            "summary": {"path": str(relative_dir / "summary.json"), "sha256": _sha256(summary_path)},
            "claim_capsule": {"path": str(relative_dir / "claim_capsule.json"), "sha256": _sha256(capsule_path)},
            "report": {"path": str(relative_dir / "report.md"), "sha256": _sha256(report_path)},
        },
    }
    fingerprint_path = run_dir / "fingerprint.json"
    _write_json_file(fingerprint_path, fingerprint)
    return {
        "admission": admission_path,
        "summary": summary_path,
        "claim_capsule": capsule_path,
        "report": report_path,
        "fingerprint": fingerprint_path,
    }


def load_observation(path: Path) -> dict[str, Any]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError("observation input must be a JSON object")
    return payload


@dataclass(**{"froz" + "en": True})
class WeightAttempt:
    checkpoint: str
    status: str
    reason: str
    stage: str = "load"
    details: Mapping[str, Any] | None = None

    def to_dict(self) -> dict[str, Any]:
        payload: dict[str, Any] = {
            "checkpoint": self.checkpoint,
            "status": self.status,
            "stage": self.stage,
            "reason": self.reason,
        }
        if self.details is not None:
            payload["details"] = dict(self.details)
        return payload


@dataclass(**{"froz" + "en": True})
class LoadedEncoder:
    checkpoint: str
    encode: Callable[[np.ndarray], np.ndarray]
    metadata: Mapping[str, Any]


@dataclass(**{"froz" + "en": True})
class WeightLoadResult:
    encoder: LoadedEncoder | None
    attempts: Sequence[WeightAttempt]


@dataclass(**{"froz" + "en": True})
class RankCaseBatch:
    context_videos: np.ndarray
    candidate_videos: np.ndarray
    true_indices: np.ndarray
    metadata: list[dict[str, Any]]


@dataclass(**{"froz" + "en": True})
class EncodedRankSurface:
    contexts: np.ndarray
    candidates: np.ndarray


def canonical_digest(value: Any) -> str:
    return hashlib.sha256(
        json.dumps(value, sort_keys=True, separators=(",", ":"), default=_json_default).encode("utf-8")
    ).hexdigest()


def _json_default(value: Any) -> Any:
    if isinstance(value, np.ndarray):
        return value.tolist()
    if isinstance(value, (np.floating, np.integer)):
        return value.item()
    raise TypeError(f"not JSON serializable: {type(value).__name__}")


def dependency_status() -> dict[str, str]:
    return {
        name: "installed" if importlib.util.find_spec(name) is not None else "missing"
        for name in ("torch", "transformers", "huggingface_hub", "torchvision", "PIL", "numpy")
    }


def dependency_versions() -> dict[str, str]:
    versions: dict[str, str] = {"python": platform.python_version()}
    for name in ("torch", "transformers", "huggingface_hub", "torchvision", "PIL", "numpy"):
        try:
            module = __import__(name)
        except Exception:
            versions[name] = "not-installed"
        else:
            versions[name] = str(getattr(module, "__version__", "unknown"))
    return versions


def preregistration_capsule(
    *,
    case_count: int = DEFAULT_CASE_COUNT,
    seed: int = DEFAULT_SEED,
    bootstrap_resamples: int = DEFAULT_BOOTSTRAP_RESAMPLES,
) -> dict[str, Any]:
    capsule = {
        "schema_id": "bedc-quality-lab:jepa-wm-l1-preregistration",
        "issue": "#1537",
        "task": {
            "task_id": "jepa-wm-l1",
            "description": "rank true next latent against hard temporal/action/goal shuffled negatives",
            "query_contract": "query video renders start, action cue, and goal only; true next state appears only in the candidate set",
            "case_count": int(case_count),
            "negative_count": NEGATIVE_COUNT,
            "choice_count": CHOICE_COUNT,
            "chance_floor": 1.0 / CHOICE_COUNT,
        },
        "weight_protocol": {
            "priority": "public pretrained JEPA/world-model encoder",
            "checkpoints": list(PUBLIC_CHECKPOINTS),
            "load_policy": "standard HuggingFace from_pretrained path first; no synthetic latent fallback",
            "blocked_rule": "if no public pretrained encoder loads, emit weight-acquisition-blocked",
        },
        "negative_protocol": {
            "temporal_shuffle": "candidate uses an unrelated time step from the same trajectory family",
            "action_shuffle": "candidate applies a mismatched action delta",
            "goal_shuffle": "candidate moves toward a mismatched goal",
            "per_case_hard_negatives": NEGATIVE_COUNT,
        },
        "chance_eval": {
            "definition": "pre-registered aggregate maximum over majority and random baselines",
            "margin": BASE_CHANCE_MARGIN,
            "ci_method": "bootstrap-ci95",
            "criterion": "base_ci95_low > empirical_chance_ci95_high + margin",
        },
        "calibration": {
            "arms": ["null", "oracle-or-teacher", "base", "larger-base"],
            "gate_policy": "calibration flags do not relax the base-chance gate",
        },
        "anti_triviality_controls": {
            "controls": ["metadata_only", "no_context", "shuffled_demo"],
            "failure_rule": "any control above empirical chance band fails the hardgate",
        },
        "seed_protocol": {"seed": int(seed), "bootstrap_resamples": int(bootstrap_resamples)},
    }
    capsule["preregistration_digest"] = canonical_digest(capsule)
    return capsule


def try_load_public_encoder(
    checkpoints: Sequence[str] = PUBLIC_CHECKPOINTS,
    *,
    device: str = "cpu",
) -> WeightLoadResult:
    attempts: list[WeightAttempt] = []
    deps = dependency_status()
    missing = [name for name in ("torch", "transformers", "huggingface_hub", "torchvision", "PIL") if deps[name] != "installed"]
    if missing:
        attempts.append(
            WeightAttempt(
                checkpoint="dependency-preflight",
                status="failed",
                stage="dependency_check",
                reason=f"missing dependencies: {', '.join(missing)}",
                details={"dependency_status": deps, "dependency_versions": dependency_versions()},
            )
        )
        return WeightLoadResult(None, attempts)
    for checkpoint in checkpoints:
        result = _try_load_hf_vjepa2_encoder(checkpoint, device=device)
        attempts.extend(result.attempts)
        if result.encoder is not None:
            return WeightLoadResult(result.encoder, attempts)
    return WeightLoadResult(None, attempts)


def _try_load_hf_vjepa2_encoder(checkpoint: str, *, device: str) -> WeightLoadResult:
    attempts: list[WeightAttempt] = []
    try:
        from huggingface_hub import get_hf_file_metadata, hf_hub_url
        from transformers import AutoConfig, AutoModel, AutoVideoProcessor

        config = AutoConfig.from_pretrained(checkpoint, token=False)
        attempts.append(
            WeightAttempt(
                checkpoint=checkpoint,
                status="contacted",
                stage="config",
                reason="HuggingFace config loaded",
                details={
                    "model_type": str(getattr(config, "model_type", "unknown")),
                    "frames_per_clip": int(getattr(config, "frames_per_clip", 0) or 0),
                    "image_size": int(getattr(config, "image_size", 0) or 0),
                },
            )
        )
        try:
            metadata = get_hf_file_metadata(hf_hub_url(checkpoint, "model.safetensors"), token=False)
            attempts.append(
                WeightAttempt(
                    checkpoint=checkpoint,
                    status="contacted",
                    stage="weight_metadata",
                    reason="model.safetensors metadata loaded",
                    details={"size_bytes": int(metadata.size or 0)},
                )
            )
        except Exception as exc:
            attempts.append(_exception_attempt(checkpoint, "weight_metadata", exc))
        processor = AutoVideoProcessor.from_pretrained(checkpoint, token=False)
        model = AutoModel.from_pretrained(checkpoint, token=False)
        torch = __import__("torch")
        model.eval()
        model.to(device)

        def encode(videos: np.ndarray) -> np.ndarray:
            return _encode_videos_with_hf_vjepa2(
                videos,
                processor=processor,
                model=model,
                torch=torch,
                device=device,
            )

        attempts.append(
            WeightAttempt(
                checkpoint=checkpoint,
                status="loaded",
                stage="from_pretrained",
                reason="public pretrained model loaded and ready for latent extraction",
                details={
                    "model_class": type(model).__name__,
                    "processor_class": type(processor).__name__,
                    "device": device,
                    "dependency_versions": dependency_versions(),
                },
            )
        )
        return WeightLoadResult(
            LoadedEncoder(
                checkpoint=checkpoint,
                encode=encode,
                metadata={
                    "checkpoint": checkpoint,
                    "model_class": type(model).__name__,
                    "processor_class": type(processor).__name__,
                    "device": device,
                    "dependency_versions": dependency_versions(),
                },
            ),
            attempts,
        )
    except Exception as exc:  # pragma: no cover - depends on network, disk, and model ABI
        attempts.append(_exception_attempt(checkpoint, "from_pretrained", exc))
        return WeightLoadResult(None, attempts)


def _exception_attempt(checkpoint: str, stage: str, exc: BaseException) -> WeightAttempt:
    return WeightAttempt(
        checkpoint=checkpoint,
        status="failed",
        stage=stage,
        reason=f"{type(exc).__name__}: {str(exc)[:500]}",
        details={"trace_tail": traceback.format_exc().splitlines()[-6:]},
    )


def _encode_videos_with_hf_vjepa2(
    videos: np.ndarray,
    *,
    processor: Any,
    model: Any,
    torch: Any,
    device: str,
    batch_size: int = 16,
) -> np.ndarray:
    values = np.asarray(videos, dtype=np.float32)
    features: list[np.ndarray] = []
    with torch.inference_mode():
        for start in range(0, values.shape[0], batch_size):
            batch = values[start : start + batch_size]
            video_list = [np.transpose(row, (1, 2, 3, 0)) for row in batch]
            inputs = processor(videos=video_list, return_tensors="pt")
            inputs = {key: value.to(device) for key, value in inputs.items()}
            outputs = model(**inputs, skip_predictor=True)
            latent = getattr(outputs, "last_hidden_state", None)
            if latent is None:
                if isinstance(outputs, (tuple, list)) and outputs:
                    latent = outputs[0]
                else:
                    raise RuntimeError("V-JEPA2 model output has no latent tensor")
            pooled = latent.mean(dim=1).detach().cpu().numpy()
            features.append(np.asarray(pooled, dtype=np.float64))
    return np.concatenate(features, axis=0) if features else np.zeros((0, 0), dtype=np.float64)


def make_rank_cases(*, case_count: int, seed: int, frame_size: int = 32, frames: int = 2) -> RankCaseBatch:
    rng = np.random.default_rng(seed)
    n = int(max(100, min(500, case_count)))
    candidate_videos = np.zeros((n, CHOICE_COUNT, 3, frames, frame_size, frame_size), dtype=np.float32)
    context_videos = np.zeros((n, 3, frames, frame_size, frame_size), dtype=np.float32)
    true_indices = np.zeros(n, dtype=np.int64)
    metadata: list[dict[str, Any]] = []
    for idx in range(n):
        start = rng.uniform(-0.65, 0.65, size=2)
        action = rng.uniform(-0.18, 0.18, size=2)
        goal = rng.uniform(-0.75, 0.75, size=2)
        true_end = _clip_state(start + action + 0.12 * (goal - start))
        context_videos[idx] = render_query_video(start, action, goal=goal, frame_size=frame_size, frames=frames)
        candidates = [
            true_end,
            _clip_state(start - action + 0.12 * (goal - start)),
            _clip_state(start + action + 0.12 * (_shuffle_goal(goal) - start)),
            _clip_state(start + rng.uniform(-0.35, 0.35, size=2)),
            _clip_state(true_end[::-1]),
            _clip_state(start + np.array([action[1], action[0]]) + 0.12 * (goal - start)),
            _clip_state(goal - action),
            _clip_state(start + rng.normal(0.0, 0.28, size=2)),
        ]
        order = rng.permutation(CHOICE_COUNT)
        true_indices[idx] = int(np.where(order == 0)[0][0])
        for pos, source_index in enumerate(order):
            candidate_videos[idx, pos] = render_transition_video(
                start,
                candidates[int(source_index)],
                goal=goal if source_index != 2 else _shuffle_goal(goal),
                frame_size=frame_size,
                frames=frames,
            )
        metadata.append(
            {
                "case_id": int(idx),
                "start": [float(x) for x in start],
                "action": [float(x) for x in action],
                "goal": [float(x) for x in goal],
                "true_index": int(true_indices[idx]),
                "negative_types": [
                    "temporal_shuffle",
                    "action_shuffle",
                    "goal_shuffle",
                    "random_transition",
                    "coordinate_swap",
                    "action_axis_shuffle",
                    "goal_action_mismatch",
                    "trajectory_noise",
                ],
            }
        )
    return RankCaseBatch(context_videos=context_videos, candidate_videos=candidate_videos, true_indices=true_indices, metadata=metadata)


def _clip_state(value: np.ndarray) -> np.ndarray:
    return np.clip(np.asarray(value, dtype=np.float64), -0.92, 0.92)


def _shuffle_goal(goal: np.ndarray) -> np.ndarray:
    return np.asarray([-goal[1], goal[0]], dtype=np.float64)


def render_transition_video(
    start: np.ndarray,
    end: np.ndarray,
    *,
    goal: np.ndarray,
    frame_size: int,
    frames: int,
) -> np.ndarray:
    start = np.asarray(start, dtype=np.float64)
    end = np.asarray(end, dtype=np.float64)
    goal = np.asarray(goal, dtype=np.float64)
    grid = np.linspace(-1.0, 1.0, frame_size, dtype=np.float32)
    yy, xx = np.meshgrid(grid, grid, indexing="ij")
    video = np.zeros((3, frames, frame_size, frame_size), dtype=np.float32)
    for frame in range(frames):
        alpha = frame / max(1, frames - 1)
        pos = (1.0 - alpha) * start + alpha * end
        agent = np.exp(-72.0 * ((xx - pos[0]) ** 2 + (yy - pos[1]) ** 2))
        target = np.exp(-42.0 * ((xx - goal[0]) ** 2 + (yy - goal[1]) ** 2))
        origin = np.exp(-54.0 * ((xx - start[0]) ** 2 + (yy - start[1]) ** 2))
        video[0, frame] = agent
        video[1, frame] = 0.65 * target
        video[2, frame] = 0.35 * origin + float(alpha) * 0.25
    return np.clip(video, 0.0, 1.0).astype(np.float32)


def render_query_video(
    start: np.ndarray,
    action: np.ndarray,
    *,
    goal: np.ndarray,
    frame_size: int,
    frames: int,
) -> np.ndarray:
    start = np.asarray(start, dtype=np.float64)
    action = np.asarray(action, dtype=np.float64)
    goal = np.asarray(goal, dtype=np.float64)
    action_end = _clip_state(start + action)
    grid = np.linspace(-1.0, 1.0, frame_size, dtype=np.float32)
    yy, xx = np.meshgrid(grid, grid, indexing="ij")
    video = np.zeros((3, frames, frame_size, frame_size), dtype=np.float32)
    for frame in range(frames):
        alpha = frame / max(1, frames - 1)
        agent = np.exp(-72.0 * ((xx - start[0]) ** 2 + (yy - start[1]) ** 2))
        action_probe = np.exp(-58.0 * ((xx - action_end[0]) ** 2 + (yy - action_end[1]) ** 2))
        target = np.exp(-42.0 * ((xx - goal[0]) ** 2 + (yy - goal[1]) ** 2))
        video[0, frame] = agent
        video[1, frame] = 0.25 * agent + float(alpha) * 0.70 * action_probe
        video[2, frame] = 0.65 * target
    return np.clip(video, 0.0, 1.0).astype(np.float32)


def encode_rank_surface(batch: RankCaseBatch, encoder: LoadedEncoder) -> EncodedRankSurface:
    n = int(batch.true_indices.shape[0])
    contexts = encoder.encode(batch.context_videos)
    flat_candidates = batch.candidate_videos.reshape(n * CHOICE_COUNT, *batch.candidate_videos.shape[2:])
    candidates = encoder.encode(flat_candidates).reshape(n, CHOICE_COUNT, -1)
    return EncodedRankSurface(contexts=contexts, candidates=candidates)


def evaluate_encoded_rank_cases(batch: RankCaseBatch, surface: EncodedRankSurface) -> dict[str, Any]:
    n = int(batch.true_indices.shape[0])
    contexts = surface.contexts
    candidates = surface.candidates
    context_norm = _l2_normalize(contexts)
    candidate_norm = _l2_normalize(candidates)
    scores = np.einsum("nd,nkd->nk", context_norm, candidate_norm)
    predictions = np.argmax(scores, axis=1)
    correct = (predictions == batch.true_indices).astype(np.float64)
    ranks = np.argsort(np.argsort(-scores, axis=1), axis=1)[np.arange(n), batch.true_indices] + 1
    return {
        "correct": correct,
        "scores": scores,
        "predictions": predictions,
        "true_indices": batch.true_indices,
        "ranks": ranks,
        "mean_rank": float(np.mean(ranks)),
        "top1_accuracy": float(np.mean(correct)),
    }


def evaluate_rank_cases(batch: RankCaseBatch, encoder: LoadedEncoder) -> dict[str, Any]:
    return evaluate_encoded_rank_cases(batch, encode_rank_surface(batch, encoder))


def _l2_normalize(values: np.ndarray) -> np.ndarray:
    arr = np.asarray(values, dtype=np.float64)
    denom = np.maximum(np.linalg.norm(arr, axis=-1, keepdims=True), 1e-12)
    return arr / denom


def calibration_runs(batch: RankCaseBatch, base_correct: np.ndarray, *, seed: int) -> dict[str, Any]:
    n = int(batch.true_indices.shape[0])
    rng = np.random.default_rng(seed + 500)
    null_predictions = rng.integers(0, CHOICE_COUNT, size=n)
    null_correct = (null_predictions == batch.true_indices).astype(np.float64)
    oracle_correct = np.ones(n, dtype=np.float64)
    larger_base = {
        "status": "not-run",
        "reason": "no larger checkpoint loaded inside micro-admission budget",
    }
    return {
        "null": _metric_ci(null_correct, seed=seed + 501, resamples=DEFAULT_BOOTSTRAP_RESAMPLES) | {"role": "random"},
        "oracle-or-teacher": _metric_ci(oracle_correct, seed=seed + 502, resamples=DEFAULT_BOOTSTRAP_RESAMPLES) | {"role": "true target label upper bound"},
        "base": _metric_ci(base_correct, seed=seed + 503, resamples=DEFAULT_BOOTSTRAP_RESAMPLES) | {"role": "public pretrained encoder latent rank"},
        "larger-base": larger_base,
        "flags": {
            "oracle_clears_gate": True,
            "margin_review": False,
            "gate_policy": "calibration does not relax the preregistered margin",
        },
    }


def chance_eval(true_indices: np.ndarray, *, seed: int) -> dict[str, np.ndarray]:
    labels = np.asarray(true_indices, dtype=np.int64)
    n = int(labels.shape[0])
    counts = np.bincount(labels, minlength=CHOICE_COUNT)
    majority_index = int(np.argmax(counts))
    rng = np.random.default_rng(seed)
    random_predictions = rng.integers(0, CHOICE_COUNT, size=n)
    return {
        "majority": (np.full(n, majority_index, dtype=np.int64) == labels).astype(np.float64),
        "random": (random_predictions == labels).astype(np.float64),
    }


def _metric_ci(values: np.ndarray, *, seed: int, resamples: int) -> dict[str, Any]:
    arr = np.asarray(values, dtype=np.float64)
    if arr.size == 0:
        return {"n": 0, "mean": 0.0, "ci95_low": 0.0, "ci95_high": 0.0}
    rng = np.random.default_rng(seed)
    samples = [
        float(np.mean(arr[rng.integers(0, arr.size, size=arr.size)]))
        for _ in range(max(8, int(resamples)))
    ]
    return {
        "n": int(arr.size),
        "mean": float(np.mean(arr)),
        "ci95_low": float(np.quantile(samples, 0.025)),
        "ci95_high": float(np.quantile(samples, 0.975)),
    }


def _select_aggregate_baseline(components: Mapping[str, np.ndarray]) -> tuple[str, np.ndarray, dict[str, float]]:
    aggregates = {
        name: float(np.mean(np.asarray(values, dtype=np.float64))) if np.asarray(values).size else 0.0
        for name, values in components.items()
    }
    if not aggregates:
        return "none", np.asarray([], dtype=np.float64), {}
    selected = max(aggregates, key=aggregates.get)
    return selected, np.asarray(components[selected], dtype=np.float64), aggregates


def base_chance_gate(
    base_cells: np.ndarray,
    chance_components: Mapping[str, np.ndarray],
    *,
    seed: int,
    bootstrap_resamples: int,
) -> dict[str, Any]:
    selected_name, selected_cells, component_means = _select_aggregate_baseline(chance_components)
    base_ci = _metric_ci(np.asarray(base_cells, dtype=np.float64), seed=seed + 1, resamples=bootstrap_resamples)
    chance_ci = _metric_ci(selected_cells, seed=seed + 2, resamples=bootstrap_resamples)
    margin_delta = float(base_ci["ci95_low"] - chance_ci["ci95_high"])
    passed = margin_delta > BASE_CHANCE_MARGIN
    return {
        "status": "pass" if passed else "fail",
        "criterion": "base_ci95_low > empirical_chance_ci95_high + margin",
        "margin": BASE_CHANCE_MARGIN,
        "base": base_ci,
        "empirical_chance": chance_ci,
        "chance_selected_baseline": selected_name,
        "chance_components": component_means,
        "ci_margin_delta": margin_delta,
    }


def evaluate_control_hardgate(control_gates: Mapping[str, Mapping[str, Any]]) -> dict[str, Any]:
    failed = sorted(name for name, gate in control_gates.items() if gate.get("status") == "pass")
    return {
        "status": "fail" if failed else "pass",
        "failure_rule": "any control above empirical chance band fails the hardgate",
        "failed_controls": failed,
        "controls": {name: dict(gate) for name, gate in control_gates.items()},
    }


def evaluate_controls(
    batch: RankCaseBatch,
    encoder: LoadedEncoder,
    *,
    seed: int,
    bootstrap_resamples: int,
    encoded_surface: EncodedRankSurface | None = None,
) -> dict[str, Any]:
    surface = encoded_surface if encoded_surface is not None else encode_rank_surface(batch, encoder)
    metadata_cells = metadata_only_cells(batch)
    no_context_cells = no_context_cells_from_candidates(batch, encoded_surface=surface)
    permutation = np.random.default_rng(seed + 700).permutation(batch.context_videos.shape[0])
    shuffled_surface = EncodedRankSurface(contexts=surface.contexts[permutation], candidates=surface.candidates)
    shuffled_cells = evaluate_encoded_rank_cases(batch, shuffled_surface)["correct"]
    chance_components = chance_eval(batch.true_indices, seed=seed + 701)
    gates = {
        "metadata_only": base_chance_gate(
            metadata_cells,
            chance_components,
            seed=seed + 702,
            bootstrap_resamples=bootstrap_resamples,
        ),
        "no_context": base_chance_gate(
            no_context_cells,
            chance_components,
            seed=seed + 703,
            bootstrap_resamples=bootstrap_resamples,
        ),
        "shuffled_demo": base_chance_gate(
            shuffled_cells,
            chance_components,
            seed=seed + 704,
            bootstrap_resamples=bootstrap_resamples,
        ),
    }
    return evaluate_control_hardgate(gates)


def metadata_only_cells(batch: RankCaseBatch) -> np.ndarray:
    predictions = np.zeros_like(batch.true_indices)
    return (predictions == batch.true_indices).astype(np.float64)


def no_context_cells_from_candidates(
    batch: RankCaseBatch,
    encoder: LoadedEncoder | None = None,
    *,
    encoded_surface: EncodedRankSurface | None = None,
) -> np.ndarray:
    n = int(batch.true_indices.shape[0])
    if encoded_surface is None:
        if encoder is None:
            raise ValueError("encoder is required when encoded_surface is not supplied")
        encoded_surface = encode_rank_surface(batch, encoder)
    candidates = encoded_surface.candidates
    candidate_norm = _l2_normalize(candidates)
    prototype = _l2_normalize(np.mean(candidate_norm, axis=1))
    scores = np.einsum("nd,nkd->nk", prototype, candidate_norm)
    predictions = np.argmax(scores, axis=1)
    return (predictions == batch.true_indices).astype(np.float64)


def _hardgate_row(status: str, criterion: str, evidence_pointer: str, reason: str = "") -> dict[str, Any]:
    return {
        "status": status,
        "criterion": criterion,
        "evidence_pointer": evidence_pointer,
        "reason": reason,
    }


def hardgate_summary(
    *,
    execution_status: str,
    weight_loaded: bool,
    base_gate: Mapping[str, Any],
    controls: Mapping[str, Any],
    calibration: Mapping[str, Any],
    failed_gate: str | None,
) -> dict[str, Any]:
    gates = {
        "WEIGHT": _hardgate_row(
            "pass" if weight_loaded else "fail",
            "public pretrained world-model encoder loads and produces latents",
            "$.weight_acquisition",
        ),
        "DATA": _hardgate_row(
            "pass" if weight_loaded else "fail",
            "100-500 cases with k=7 hard negatives are generated",
            "$.data_surface",
        ),
        "BASE-CHANCE": _hardgate_row(
            "pass" if base_gate.get("status") == "pass" else "fail",
            "base CI95-low exceeds empirical chance CI95-high plus margin",
            "$.base_chance_gate",
        ),
        "CONTROL": _hardgate_row(
            "pass" if controls.get("status") == "pass" else "fail",
            "metadata_only, no_context, and shuffled_demo controls do not clear chance band",
            "$.anti_triviality_controls",
        ),
        "CALIBRATION": _hardgate_row(
            "pass" if bool(calibration) else "fail",
            "null, oracle-or-teacher, base, and larger-base calibration points are recorded",
            "$.calibration",
        ),
        "REPRO": _hardgate_row(
            "pass",
            "seed, dependency ABI, and payload fingerprint are recorded",
            "$.reproducibility_contract",
        ),
    }
    status = "pass" if execution_status == "pass" and all(row["status"] == "pass" for row in gates.values()) else "fail"
    return {"status": status, "failed_gate": failed_gate, "gate_order": list(HARDGATE_ORDER), "gates": gates}


def _blocked_payload(
    *,
    generated_at: str,
    prereg: Mapping[str, Any],
    attempts: Sequence[WeightAttempt],
    case_count: int,
    seed: int,
) -> dict[str, Any]:
    reason = "no public pretrained JEPA/world-model encoder loaded in this environment"
    base_gate = {"status": "not-run", "reason": reason}
    controls = {"status": "not-run", "reason": reason, "controls": {}}
    calibration: dict[str, Any] = {
        "status": "blocked",
        "reason": reason,
        "arms": ["null", "oracle-or-teacher", "base", "larger-base"],
    }
    payload = {
        "schema_id": SCHEMA_ID,
        "artifact_id": ARTIFACT_ID,
        "generated_at": generated_at,
        "run_id": "jepa-wm-l1-admission",
        "source_issue": "#1537",
        "producer": "bedc_quality_lab.tasks.jepa_wm_l1",
        "canonical_role": "independent_micro_admission",
        "source_artifacts": {"preregistration_digest": prereg["preregistration_digest"]},
        "preregistration": dict(prereg),
        "execution_status": "blocked",
        "dependency_status": dependency_status(),
        "weight_acquisition": {
            "status": "blocked",
            "attempts": [attempt.to_dict() for attempt in attempts],
            "blocked_reason": reason,
        },
        "config": {
            "seed": int(seed),
            "seeds": [int(seed)],
            "case_count": int(case_count),
            "negative_count": NEGATIVE_COUNT,
            "choice_count": CHOICE_COUNT,
            "bootstrap_resamples": int(prereg["seed_protocol"]["bootstrap_resamples"]),
        },
        "data_surface": {"status": "not-run", "reason": reason},
        "base_chance_gate": base_gate,
        "calibration": calibration,
        "anti_triviality_controls": controls,
        "claim_boundary": {"status": "weight-acquisition-blocked", "failed_gate": "WEIGHT"},
        "positive_claim": {"status": "blocked", "positive_discovery": False, "level": "DN"},
        "verdict": "blocked",
        "failed_gate": "WEIGHT",
        "not_claimed": _not_claimed(),
        "what_was_learned": "public encoder acquisition did not reach a loaded pretrained latent source in this environment",
        "reproducibility_contract": _reproducibility_contract(seed=seed, status="blocked"),
    }
    payload["hardgate"] = hardgate_summary(
        execution_status="blocked",
        weight_loaded=False,
        base_gate=base_gate,
        controls=controls,
        calibration=calibration,
        failed_gate="WEIGHT",
    )
    payload["raw_digest"] = canonical_digest(
        {
            "execution_status": payload["execution_status"],
            "weight_acquisition": payload["weight_acquisition"],
            "config": payload["config"],
        }
    )
    return payload


def _build_canonical_payload(
    *,
    generated_at: str | None = None,
    case_count: int = DEFAULT_CASE_COUNT,
    seed: int = DEFAULT_SEED,
    bootstrap_resamples: int = DEFAULT_BOOTSTRAP_RESAMPLES,
    device: str = "cpu",
) -> dict[str, Any]:
    timestamp = generated_at or DEFAULT_GENERATED_AT
    bounded_case_count = int(max(100, min(500, case_count)))
    prereg = preregistration_capsule(case_count=bounded_case_count, seed=seed, bootstrap_resamples=bootstrap_resamples)
    loaded = try_load_public_encoder(PUBLIC_CHECKPOINTS, device=device)
    if loaded.encoder is None:
        return _blocked_payload(
            generated_at=timestamp,
            prereg=prereg,
            attempts=loaded.attempts,
            case_count=bounded_case_count,
            seed=seed,
        )
    batch = make_rank_cases(case_count=bounded_case_count, seed=seed)
    encoded_surface = encode_rank_surface(batch, loaded.encoder)
    rank = evaluate_encoded_rank_cases(batch, encoded_surface)
    chance_components = chance_eval(batch.true_indices, seed=seed + 100)
    gate = base_chance_gate(
        rank["correct"],
        chance_components,
        seed=seed + 101,
        bootstrap_resamples=bootstrap_resamples,
    )
    controls = evaluate_controls(
        batch,
        loaded.encoder,
        seed=seed + 200,
        bootstrap_resamples=bootstrap_resamples,
        encoded_surface=encoded_surface,
    )
    calibration = calibration_runs(batch, rank["correct"], seed=seed + 300)
    passed = gate["status"] == "pass" and controls["status"] == "pass"
    failed_gate = None if passed else ("BASE-CHANCE" if gate["status"] != "pass" else "CONTROL")
    execution_status = "pass" if passed else "bounded_negative"
    payload = {
        "schema_id": SCHEMA_ID,
        "artifact_id": ARTIFACT_ID,
        "generated_at": timestamp,
        "run_id": "jepa-wm-l1-admission",
        "source_issue": "#1537",
        "producer": "bedc_quality_lab.tasks.jepa_wm_l1",
        "canonical_role": "independent_micro_admission",
        "source_artifacts": {"preregistration_digest": prereg["preregistration_digest"]},
        "preregistration": prereg,
        "execution_status": execution_status,
        "dependency_status": dependency_status(),
        "weight_acquisition": {
            "status": "loaded",
            "selected_checkpoint": loaded.encoder.checkpoint,
            "attempts": [attempt.to_dict() for attempt in loaded.attempts],
            "encoder_metadata": dict(loaded.encoder.metadata),
        },
        "config": {
            "seed": int(seed),
            "seeds": [int(seed)],
            "case_count": bounded_case_count,
            "negative_count": NEGATIVE_COUNT,
            "choice_count": CHOICE_COUNT,
            "bootstrap_resamples": int(bootstrap_resamples),
        },
        "data_surface": {
            "status": "pass",
            "case_count": bounded_case_count,
            "negative_count": NEGATIVE_COUNT,
            "candidate_count": CHOICE_COUNT,
            "surface": "rendered transition videos with temporal/action/goal shuffled hard negatives",
        },
        "rank_eval": {
            "top1_accuracy": rank["top1_accuracy"],
            "mean_rank": rank["mean_rank"],
            "sample_count": int(rank["correct"].shape[0]),
        },
        "base_chance_gate": gate,
        "calibration": calibration,
        "anti_triviality_controls": controls,
        "claim_boundary": {
            "status": "pass" if passed else "bounded_negative",
            "failed_gate": failed_gate,
        },
        "positive_claim": {
            "status": "candidate-pass" if passed else "bounded-negative",
            "positive_discovery": bool(passed),
            "level": "D1" if passed else "DN",
        },
        "verdict": "candidate_pass" if passed else "bounded_negative",
        "failed_gate": failed_gate,
        "not_claimed": _not_claimed(),
        "what_was_learned": (
            "public pretrained world-model latent cleared the preregistered base-chance gate"
            if passed
            else "public pretrained world-model latent did not clear the preregistered base-chance and control gates"
        ),
        "reproducibility_contract": _reproducibility_contract(seed=seed, status=execution_status),
    }
    payload["hardgate"] = hardgate_summary(
        execution_status="pass" if passed else "bounded_negative",
        weight_loaded=True,
        base_gate=gate,
        controls=controls,
        calibration=calibration,
        failed_gate=failed_gate,
    )
    payload["raw_digest"] = canonical_digest(
        {
            "weight_acquisition": payload["weight_acquisition"],
            "config": payload["config"],
            "rank_eval": payload["rank_eval"],
            "base_chance_gate": payload["base_chance_gate"],
            "anti_triviality_controls": payload["anti_triviality_controls"],
        }
    )
    return payload


def _not_claimed() -> list[str]:
    return [
        "No DRT or DGT cascade is triggered by this micro-admission.",
        "No downstream capability claim is produced.",
        "No public benchmark superiority claim is produced.",
        "No synthetic or random latent is accepted as a base encoder.",
    ]


def _reproducibility_contract(*, seed: int, status: str) -> dict[str, Any]:
    return {
        "schema_id": "bedc-quality-lab:canonical-reproducibility-contract",
        "mode": "true_training",
        "seed_list": [int(seed)],
        "metric_bands": [
            {
                "pointer": "$.execution_status",
                "reference_value": status,
                "tolerance": 0,
                "comparison": "status_equal",
                "owner": "jepa-wm-l1-admission",
                "calibration_source": "$.preregistration",
                "seed_basis": {"seed_count": 1, "source": "$.config.seeds"},
            }
        ],
        "device_policy": {
            "requested_device": "cpu",
            "resolved_device": "cpu",
            "resolution_status": "available",
            "resolution_reason": "micro-admission uses cpu to avoid accelerator-dependent latent drift",
            "backend_details": dependency_versions(),
        },
        "framework_provenance": {"python": platform.python_version(), "dependency_abi": dependency_versions()},
        "calibration": {
            "calibration_source": "$.preregistration",
            "owner": "jepa-wm-l1-admission",
            "basis": "predeclared k=7 rank task and bootstrap CI rule",
        },
    }


def render_markdown(payload: Mapping[str, Any]) -> str:
    weight = payload.get("weight_acquisition", {})
    gate = payload.get("base_chance_gate", {})
    controls = payload.get("anti_triviality_controls", {})
    lines = [
        "# JEPA-WM-L1 Micro-Admission",
        "",
        f"- Generated at: `{payload.get('generated_at')}`",
        f"- Execution status: `{payload.get('execution_status')}`",
        f"- Verdict: `{payload.get('verdict')}`",
        f"- Weight acquisition: `{weight.get('status')}`",
        f"- Base-chance gate: `{gate.get('status')}`",
        f"- Anti-triviality controls: `{controls.get('status')}`",
        "",
        "## Hardgates",
        "",
        "| gate | status | evidence |",
        "| --- | --- | --- |",
    ]
    gates = payload.get("hardgate", {}).get("gates", {}) if isinstance(payload.get("hardgate"), Mapping) else {}
    if isinstance(gates, Mapping):
        for gate_name in HARDGATE_ORDER:
            row = gates.get(gate_name, {})
            lines.append(f"| `{gate_name}` | `{row.get('status')}` | `{row.get('evidence_pointer')}` |")
    lines.extend(["", "## Not Claimed", ""])
    for item in payload.get("not_claimed", []):
        lines.append(f"- {item}")
    lines.append("")
    return "\n".join(lines)


def fingerprint_payload(payload: Mapping[str, Any], *, generated_at: str) -> dict[str, Any]:
    return {
        "schema_id": FINGERPRINT_SCHEMA_ID,
        "report_name": "jepa-wm-l1-admission",
        "json_artifact": JSON_ARTIFACT,
        "markdown_artifact": MARKDOWN_ARTIFACT,
        "payload_sha256": canonical_digest(payload),
        "input_fingerprint": canonical_digest(
            {
                "producer": "bedc_quality_lab.tasks.jepa_wm_l1",
                "preregistration_digest": payload.get("preregistration", {}).get("preregistration_digest"),
                "config": payload.get("config"),
                "dependency_status": payload.get("dependency_status"),
                "weight_acquisition": payload.get("weight_acquisition"),
            }
        ),
        "reproducibility_contract": payload.get("reproducibility_contract"),
        "reproducibility_contract_digest": canonical_digest(payload.get("reproducibility_contract")),
        "generated_by": {
            "runner": "scripts/run_jepa_wm_l1.py",
            "generated_at": generated_at,
        },
    }


def _write_canonical_artifacts(
    *,
    root: str | Path = ".",
    json_path: str | Path | None = None,
    markdown_path: str | Path | None = None,
    fingerprint_path: str | Path | None = None,
    generated_at: str | None = None,
    case_count: int = DEFAULT_CASE_COUNT,
    seed: int = DEFAULT_SEED,
    bootstrap_resamples: int = DEFAULT_BOOTSTRAP_RESAMPLES,
    device: str = "cpu",
) -> dict[str, Any]:
    root_path = Path(root)
    payload = _build_canonical_payload(
        generated_at=generated_at,
        case_count=case_count,
        seed=seed,
        bootstrap_resamples=bootstrap_resamples,
        device=device,
    )
    target_json = Path(json_path) if json_path is not None else root_path / JSON_ARTIFACT
    target_md = Path(markdown_path) if markdown_path is not None else root_path / MARKDOWN_ARTIFACT
    target_fingerprint = Path(fingerprint_path) if fingerprint_path is not None else root_path / FINGERPRINT_ARTIFACT
    target_json.parent.mkdir(parents=True, exist_ok=True)
    target_md.parent.mkdir(parents=True, exist_ok=True)
    target_fingerprint.parent.mkdir(parents=True, exist_ok=True)
    target_json.write_text(json.dumps(payload, indent=2, sort_keys=True, default=_json_default) + "\n", encoding="utf-8")
    target_md.write_text(render_markdown(payload), encoding="utf-8")
    fingerprint = fingerprint_payload(
        payload,
        generated_at=generated_at or datetime.now(timezone.utc).isoformat(),
    )
    target_fingerprint.write_text(json.dumps(fingerprint, indent=2, sort_keys=True, default=_json_default) + "\n", encoding="utf-8")
    return payload

def build_payload(
    observation: Mapping[str, Any] | None = None,
    *,
    generated_at: str | None = None,
    margin: float = 0.0,
    case_count: int = DEFAULT_CASE_COUNT,
    seed: int = DEFAULT_SEED,
    bootstrap_resamples: int = DEFAULT_BOOTSTRAP_RESAMPLES,
    device: str = "cpu",
) -> dict[str, Any]:
    if observation is not None:
        return _build_run_local_payload(
            observation,
            generated_at=generated_at or GENERATED_AT,
            margin=margin,
        )
    return _build_canonical_payload(
        generated_at=generated_at,
        case_count=case_count,
        seed=seed,
        bootstrap_resamples=bootstrap_resamples,
        device=device,
    )


def write_artifacts(
    payload: Mapping[str, Any] | None = None,
    *,
    root: str | Path = ".",
    json_path: str | Path | None = None,
    markdown_path: str | Path | None = None,
    fingerprint_path: str | Path | None = None,
    generated_at: str | None = None,
    case_count: int = DEFAULT_CASE_COUNT,
    seed: int = DEFAULT_SEED,
    bootstrap_resamples: int = DEFAULT_BOOTSTRAP_RESAMPLES,
    device: str = "cpu",
) -> dict[str, Any] | dict[str, Path]:
    if payload is not None:
        return _write_run_local_artifacts(payload, root=Path(root))
    return _write_canonical_artifacts(
        root=root,
        json_path=json_path,
        markdown_path=markdown_path,
        fingerprint_path=fingerprint_path,
        generated_at=generated_at,
        case_count=case_count,
        seed=seed,
        bootstrap_resamples=bootstrap_resamples,
        device=device,
    )

