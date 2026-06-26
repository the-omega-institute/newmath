"""JEPA-WM-L1 micro-admission over public pretrained world-model latents."""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
import re
from typing import Any, Mapping, Sequence

import numpy as np


SCHEMA_ID = "bedc-quality-lab:jepa-wm-l1-admission"
ARTIFACT_ID = "bedc-quality-lab:jepa-wm-l1-admission"
FINGERPRINT_SCHEMA_ID = "bedc-quality-lab:canonical-report-fingerprint"
JSON_ARTIFACT = "reports/canonical/jepa-wm-l1-admission.json"
MARKDOWN_ARTIFACT = "reports/canonical/jepa-wm-l1-admission.md"
DEFAULT_GENERATED_AT = "2026-06-17T00:00:00+00:00"
DEFAULT_SEED = 20260617
DEFAULT_CASE_COUNT = 128
DEFAULT_BOOTSTRAP_RESAMPLES = 512
NEGATIVE_COUNT = 7
CHOICE_COUNT = 1 + NEGATIVE_COUNT
BASE_CHANCE_MARGIN = 0.03
GENERATED_AT = DEFAULT_GENERATED_AT
RUNS_DIR = Path("reports/runs/jepa-wm-l1")
SOURCE_OBSERVATION_KEY = "_source_observation"
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


def _relative_path(root: Path | None, path: Path) -> str:
    if root is None:
        return str(path)
    try:
        return str(path.relative_to(root))
    except ValueError:
        return str(path)


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


def _source_observation(observation: Mapping[str, Any]) -> Mapping[str, Any]:
    return _mapping(observation.get(SOURCE_OBSERVATION_KEY))


def _has_file_observation_source(observation: Mapping[str, Any]) -> bool:
    source = _source_observation(observation)
    digest = source.get("sha256")
    chain = _sequence(source.get("provenance_chain"))
    return (
        source.get("status") == "file-runtime-observation"
        and isinstance(source.get("path"), str)
        and bool(source.get("path"))
        and isinstance(digest, str)
        and re.fullmatch(r"[0-9a-fA-F]{64}", digest) is not None
        and bool(chain)
    )


def _checkpoint_gate(observation: Mapping[str, Any]) -> RunLocalGate:
    provenance = _mapping(_mapping(observation.get("checkpoint")).get("provenance"))
    digest = provenance.get("checkpoint_sha256")
    pretrained = (
        _has_file_observation_source(observation)
        and provenance.get("status") == "pretrained"
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
        "missing observation source, pretrained source, digest, loaded weights, or random-init exclusion",
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
            **(
                dict(_source_observation(observation))
                if _source_observation(observation)
                else {"status": "missing-source-observation"}
            ),
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
    source = _mapping(payload.get("source_observation"))
    source_digest = source.get("sha256")
    source_chain = _sequence(source.get("provenance_chain"))
    valid_source = (
        source.get("status") == "file-runtime-observation"
        and isinstance(source.get("path"), str)
        and bool(source.get("path"))
        and isinstance(source_digest, str)
        and re.fullmatch(r"[0-9a-fA-F]{64}", source_digest) is not None
        and bool(source_chain)
    )
    if status == "PASS" and not valid_source:
        raise ValueError("source observation provenance mismatch")


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


def load_observation(path: Path, *, root: Path | None = None) -> dict[str, Any]:
    input_path = Path(path)
    payload = json.loads(input_path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError("observation input must be a JSON object")
    source_path = _relative_path(root, input_path)
    digest = _sha256(input_path)
    observation = dict(payload)
    observation[SOURCE_OBSERVATION_KEY] = {
        "status": "file-runtime-observation",
        "path": source_path,
        "sha256": digest,
        "provenance_chain": [
            {
                "artifact": source_path,
                "role": "runtime-observation-input",
                "sha256": digest,
            }
        ],
    }
    return observation


@dataclass(frozen=True)
class RankCaseBatch:
    context_videos: np.ndarray
    candidate_videos: np.ndarray
    true_indices: np.ndarray
    metadata: list[dict[str, Any]]


@dataclass(frozen=True)
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
    return RankCaseBatch(
        context_videos=context_videos,
        candidate_videos=candidate_videos,
        true_indices=true_indices,
        metadata=metadata,
    )


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


def evaluate_encoded_rank_cases(batch: RankCaseBatch, surface: EncodedRankSurface) -> dict[str, Any]:
    n = int(batch.true_indices.shape[0])
    context_norm = _l2_normalize(surface.contexts)
    candidate_norm = _l2_normalize(surface.candidates)
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


def _l2_normalize(values: np.ndarray) -> np.ndarray:
    arr = np.asarray(values, dtype=np.float64)
    denom = np.maximum(np.linalg.norm(arr, axis=-1, keepdims=True), 1e-12)
    return arr / denom


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


def build_payload(
    observation: Mapping[str, Any],
    *,
    generated_at: str | None = None,
    margin: float = 0.0,
) -> dict[str, Any]:
    return _build_run_local_payload(
        observation,
        generated_at=generated_at or GENERATED_AT,
        margin=margin,
    )


def write_artifacts(
    payload: Mapping[str, Any],
    *,
    root: str | Path = ".",
) -> dict[str, Path]:
    return _write_run_local_artifacts(payload, root=Path(root))
