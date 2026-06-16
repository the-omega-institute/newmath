"""Run-local JEPA-WM-L1 admission semantics."""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
import re
from typing import Any, Mapping, Sequence


SCHEMA_ID = "bedc-quality-lab:jepa-wm-l1-admission"
ARTIFACT_ID = "bedc-quality-lab:jepa-wm-l1"
PRODUCER = "scripts/run_jepa_wm_l1.py"
OWNER_MODULE = "bedc_quality_lab.tasks.jepa_wm_l1"
GENERATED_AT = "2026-06-17T00:00:00+08:00"
LAB_ROOT = Path(__file__).resolve().parents[2]
RUNS_DIR = Path("reports/runs/jepa-wm-l1")

REQUIRED_K = 7
REQUIRED_CHANCE = 1.0 / 8.0
REQUIRED_ARMS = ("null", "oracle_or_teacher", "base", "larger_base")
REQUIRED_CONTROLS = ("metadata_only", "no_context")
HARDGATE_IDS = tuple(f"JWM-L1-HG{index}" for index in range(1, 8))
STATUS_DOMAIN = ("PASS", "FAIL")
NOT_CLAIMED = (
    "No JEPA-WM-L2 or higher result.",
    "No global model superiority claim.",
    "No canonical dashboard registration.",
    "No production deployment claim.",
    "No training recipe claim beyond the supplied runtime observation.",
)


@dataclass(frozen=True)
class Gate:
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


def _write_json(path: Path, payload: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    tmp.replace(path)


def _write_text(path: Path, text: str) -> None:
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


def _pass_gate(gate_id: str, criterion: str, pointer: str, detail: str) -> Gate:
    return Gate(gate_id=gate_id, status="pass", criterion=criterion, evidence_pointer=pointer, detail=detail)


def _fail_gate(gate_id: str, criterion: str, pointer: str, detail: str) -> Gate:
    return Gate(gate_id=gate_id, status="fail", criterion=criterion, evidence_pointer=pointer, detail=detail)


def _checkpoint_gate(observation: Mapping[str, Any]) -> Gate:
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
        return _pass_gate(
            "JWM-L1-HG1",
            "runtime uses true pretrained checkpoint provenance",
            "$.checkpoint.provenance",
            "pretrained checkpoint provenance supplied",
        )
    return _fail_gate(
        "JWM-L1-HG1",
        "runtime uses true pretrained checkpoint provenance",
        "$.checkpoint.provenance",
        "missing pretrained source, digest, loaded weights, or random-init exclusion",
    )


def _clips_gate(observation: Mapping[str, Any]) -> Gate:
    clips = _sequence(observation.get("clips"))
    non_empty = bool(clips)
    valid_rows = all(isinstance(clip, Mapping) and bool(clip.get("clip_id")) for clip in clips)
    frame_counts = [
        _number(_mapping(clip).get("frame_count"))
        for clip in clips
        if isinstance(clip, Mapping)
    ]
    valid_frames = bool(frame_counts) and all(count is not None and count > 0 for count in frame_counts)
    if non_empty and valid_rows and valid_frames:
        return _pass_gate(
            "JWM-L1-HG2",
            "runtime supplies non-empty evaluated clips",
            "$.clips",
            f"{len(clips)} clip row(s)",
        )
    return _fail_gate(
        "JWM-L1-HG2",
        "runtime supplies non-empty evaluated clips",
        "$.clips",
        "clip rows must be non-empty and carry positive frame counts",
    )


def _k_gate(observation: Mapping[str, Any]) -> Gate:
    k = observation.get("k")
    if k == REQUIRED_K:
        return _pass_gate("JWM-L1-HG3", "benchmark uses k=7", "$.k", "k=7")
    return _fail_gate("JWM-L1-HG3", "benchmark uses k=7", "$.k", f"k={k!r}")


def _chance_gate(observation: Mapping[str, Any]) -> Gate:
    chance = _mapping(observation.get("chance"))
    probability = _number(chance.get("probability"))
    ci_high = _number(chance.get("ci_high"))
    ok = probability == REQUIRED_CHANCE and ci_high is not None
    if ok:
        return _pass_gate(
            "JWM-L1-HG4",
            "chance baseline is exactly 1/8 with an upper confidence bound",
            "$.chance",
            f"chance={probability}",
        )
    return _fail_gate(
        "JWM-L1-HG4",
        "chance baseline is exactly 1/8 with an upper confidence bound",
        "$.chance",
        "chance probability must equal 1/8 and include ci_high",
    )


def _arms_gate(observation: Mapping[str, Any]) -> Gate:
    arms = _mapping(observation.get("arms"))
    missing = [arm_id for arm_id in REQUIRED_ARMS if not isinstance(arms.get(arm_id), Mapping)]
    unexpected = [str(arm_id) for arm_id in arms.keys() if arm_id not in REQUIRED_ARMS]
    incomplete: list[str] = []
    for arm_id in REQUIRED_ARMS:
        row = _mapping(arms.get(arm_id))
        if any(_number(row.get(key)) is None for key in ("score", "ci_low", "ci_high")) or _number(row.get("n")) is None:
            incomplete.append(arm_id)
    if not missing and not unexpected and not incomplete:
        return _pass_gate(
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
    return _fail_gate(
        "JWM-L1-HG5",
        "exactly four admission arms are present with score, CI, and n",
        "$.arms",
        "; ".join(detail),
    )


def _calibration(observation: Mapping[str, Any], *, margin: float) -> dict[str, Any]:
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


def _margin_gate(calibration: Mapping[str, Any]) -> Gate:
    if calibration.get("strict_margin_pass") is True:
        return _pass_gate(
            "JWM-L1-HG6",
            "strict base_CI_low > chance_CI_high + margin",
            "$.calibration",
            "base lower CI clears chance upper CI plus margin",
        )
    return _fail_gate(
        "JWM-L1-HG6",
        "strict base_CI_low > chance_CI_high + margin",
        "$.calibration",
        "base lower CI must be strictly greater than chance upper CI plus margin",
    )


def _controls_gate(observation: Mapping[str, Any]) -> Gate:
    controls = _mapping(observation.get("controls"))
    bad: list[str] = []
    for control_id in REQUIRED_CONTROLS:
        row = _mapping(controls.get(control_id))
        if (
            row.get("status") != "clean"
            or row.get("leak_detected") is not False
            or _number(row.get("ci_high")) is None
        ):
            bad.append(control_id)
    if not bad:
        return _pass_gate(
            "JWM-L1-HG7",
            "metadata_only and no_context controls are clean",
            "$.controls",
            ",".join(REQUIRED_CONTROLS),
        )
    return _fail_gate(
        "JWM-L1-HG7",
        "metadata_only and no_context controls are clean",
        "$.controls",
        f"unclean={','.join(bad)}",
    )


def build_payload(
    observation: Mapping[str, Any],
    *,
    generated_at: str = GENERATED_AT,
    margin: float = 0.0,
) -> dict[str, Any]:
    if margin < 0:
        raise ValueError("margin must be nonnegative")
    calibration = _calibration(observation, margin=margin)
    gates = [
        _checkpoint_gate(observation),
        _clips_gate(observation),
        _k_gate(observation),
        _chance_gate(observation),
        _arms_gate(observation),
        _margin_gate(calibration),
        _controls_gate(observation),
    ]
    hardgates = {gate.gate_id: gate.as_dict() for gate in gates}
    failed = [gate.gate_id for gate in gates if gate.status != "pass"]
    run_id = _slug(observation.get("run_id"))
    run_artifact = RUNS_DIR / run_id / "admission.json"
    payload: dict[str, Any] = {
        "schema_id": SCHEMA_ID,
        "artifact_id": ARTIFACT_ID,
        "generated_at": generated_at,
        "producer": PRODUCER,
        "owner_module": OWNER_MODULE,
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
            "status_domain": list(STATUS_DOMAIN),
            "status": "PASS" if not failed else "FAIL",
            "failed_gates": failed,
            "admission_artifact": str(run_artifact),
        },
        "claim_capsule": {
            "status": "pointer-only",
            "admission_pointer": f"{run_artifact}:$.decision.status",
            "hardgate_pointers": [f"{run_artifact}:$.hardgates.{gate_id}.status" for gate_id in HARDGATE_IDS],
            "not_claimed_pointer": f"{run_artifact}:$.not_claimed",
        },
        "not_claimed": list(NOT_CLAIMED),
    }
    validate_payload(payload)
    return payload


def validate_payload(payload: Mapping[str, Any]) -> None:
    decision = _mapping(payload.get("decision"))
    status = decision.get("status")
    if status not in STATUS_DOMAIN:
        raise ValueError("status domain violation")
    hardgates = _mapping(payload.get("hardgates"))
    if tuple(hardgates.keys()) != HARDGATE_IDS:
        raise ValueError("hardgate order violation")
    failed = [gate_id for gate_id, row in hardgates.items() if _mapping(row).get("status") != "pass"]
    if list(decision.get("failed_gates", [])) != failed:
        raise ValueError("failed gate projection mismatch")
    if (status == "PASS") != (not failed):
        raise ValueError("decision status mismatch")
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


def _report_text(payload: Mapping[str, Any], admission_artifact: str) -> str:
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


def write_artifacts(payload: Mapping[str, Any], *, root: Path | None = None) -> dict[str, Path]:
    validate_payload(payload)
    root = root or LAB_ROOT
    run_id = _slug(payload.get("run_id"))
    relative_dir = RUNS_DIR / run_id
    run_dir = root / relative_dir
    admission_path = run_dir / "admission.json"
    summary_path = run_dir / "summary.json"
    capsule_path = run_dir / "claim_capsule.json"
    report_path = run_dir / "report.md"
    admission_artifact = str(relative_dir / "admission.json")

    _write_json(admission_path, payload)
    _write_json(summary_path, _summary_payload(payload, admission_artifact))
    _write_json(capsule_path, _capsule_payload(payload, admission_artifact))
    _write_text(report_path, _report_text(payload, admission_artifact))

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
    _write_json(fingerprint_path, fingerprint)
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
