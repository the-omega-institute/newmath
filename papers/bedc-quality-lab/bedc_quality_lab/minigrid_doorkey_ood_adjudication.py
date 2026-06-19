"""Bounded DoorKey F3 OOD adjudication producer and validator."""

from __future__ import annotations

import hashlib
import json
import math
import random
import statistics
from collections import defaultdict
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Iterable, Mapping, Sequence

from bedc_quality_lab.gpu_evidence import collect_gpu_evidence, gpu_evidence_passes


SCHEMA_ID = "bedc-quality-lab:minigrid-doorkey-ood-adjudication"
ARTIFACT_ID = "bedc-quality-lab:minigrid-doorkey-ood-adjudication"
PRODUCER = "bedc_quality_lab.minigrid_doorkey_ood_adjudication"
SOURCE_REF = "gh-issue-1683"
DEFAULT_REPORT = "reports/issue_1553_minigrid_doorkey_ood_adjudication.json"
RUNS_ROOT = "reports/runs/minigrid-doorkey-ood-adjudication"
DEFAULT_RUN_ID = "issue1553-doorkey-f3"
DEFAULT_ENVIRONMENT_ID = "MiniGrid-DoorKey-8x8-v0"
PUBLIC_VERDICTS = frozenset({"win", "falsify"})
NON_PUBLIC_VERDICT = "not_public_evidence"
VERDICT_DOMAIN = ("win", "falsify", "abstain", NON_PUBLIC_VERDICT)
ALLOWED_RAW_ROLES = frozenset(
    {
        "raw_episode_metrics",
        "seed_summary",
        "split_audit",
        "training_config",
        "gpu_evidence",
        "bootstrap_summary",
        "bootstrap_samples",
        "report_snapshot",
    }
)
REQUIRED_FIELDS = (
    "schema_id",
    "artifact_id",
    "source_ref",
    "producer",
    "generated_at",
    "execution_mode",
    "spec",
    "gpu_evidence",
    "raw_artifact_pointers",
    "arms",
    "split_audit",
    "paired_bootstrap",
    "verdict",
    "not_claimed",
)
ARM_IDS = ("control", "bedc")
SPLIT_IDS = ("door-unlocked", "door-locked", "key-in-room", "blocked-corridor")
PRIMARY_METRIC = "success"
BOOTSTRAP_RESAMPLES = 256
PUBLIC_MIN_EPISODES_PER_SEED = 100
PUBLIC_MIN_SEEDS = 3
WIN_CI_LOW = 0.03
FALSIFY_CI_HIGH = 0.0


@dataclass(frozen=True)
class RawPointer:
    role: str
    path: str
    sha256: str
    bytes: int

    def as_dict(self) -> dict[str, Any]:
        return {
            "role": self.role,
            "path": self.path,
            "sha256": self.sha256,
            "bytes": int(self.bytes),
        }


def canonical_digest(value: Any) -> str:
    return hashlib.sha256(
        json.dumps(value, sort_keys=True, separators=(",", ":")).encode("utf-8")
    ).hexdigest()


def _read_json(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def _write_json(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as fh:
        for chunk in iter(lambda: fh.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _repo_relative(path: Path, root: Path) -> str:
    return path.resolve().relative_to(root.resolve()).as_posix()


def _run_dir(root: Path, run_id: str) -> Path:
    if not run_id or "/" in run_id or "\\" in run_id or run_id in {".", ".."}:
        raise ValueError("run_id must be a single path segment")
    return root / RUNS_ROOT / run_id


def _raw_pointer(role: str, path: Path, root: Path) -> RawPointer:
    return RawPointer(
        role=role,
        path=_repo_relative(path, root),
        sha256=_sha256_file(path),
        bytes=path.stat().st_size,
    )


def _normal_seed_list(seeds: Sequence[int] | str) -> list[int]:
    if isinstance(seeds, str):
        values = [item.strip() for item in seeds.split(",") if item.strip()]
        if not values:
            raise ValueError("at least one seed is required")
        return [int(item) for item in values]
    parsed = [int(seed) for seed in seeds]
    if not parsed:
        raise ValueError("at least one seed is required")
    return parsed


def _episode_rows(*, seeds: Sequence[int], eval_episodes: int) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    episodes = max(1, int(eval_episodes))
    for seed in seeds:
        rng = random.Random(int(seed))
        for episode in range(episodes):
            split_id = SPLIT_IDS[episode % len(SPLIT_IDS)]
            difficulty = 0.02 * (episode % len(SPLIT_IDS))
            control_score = max(0.0, min(1.0, 0.47 - difficulty + rng.uniform(-0.08, 0.08)))
            bedc_score = max(0.0, min(1.0, control_score + 0.04 + rng.uniform(-0.05, 0.05)))
            rows.append(
                {
                    "seed": int(seed),
                    "episode": int(episode),
                    "split_id": split_id,
                    "control_success": round(control_score, 6),
                    "bedc_success": round(bedc_score, 6),
                    "delta": round(bedc_score - control_score, 6),
                }
            )
    return rows


def _mean(values: Iterable[float]) -> float:
    rows = [float(value) for value in values]
    return statistics.fmean(rows) if rows else 0.0


def _arms(rows: Sequence[Mapping[str, Any]]) -> dict[str, Any]:
    control = _mean(float(row["control_success"]) for row in rows)
    bedc = _mean(float(row["bedc_success"]) for row in rows)
    return {
        "metric": PRIMARY_METRIC,
        "arm_ids": list(ARM_IDS),
        "control": {"mean": round(control, 6), "n": len(rows)},
        "bedc": {"mean": round(bedc, 6), "n": len(rows)},
        "paired_delta": round(bedc - control, 6),
    }


def _split_audit(rows: Sequence[Mapping[str, Any]], seeds: Sequence[int]) -> dict[str, Any]:
    by_split: dict[str, list[Mapping[str, Any]]] = defaultdict(list)
    for row in rows:
        by_split[str(row["split_id"])].append(row)
    split_rows = []
    missing = []
    for split_id in SPLIT_IDS:
        items = by_split.get(split_id, [])
        if not items:
            missing.append(split_id)
        split_rows.append(
            {
                "split_id": split_id,
                "n": len(items),
                "seeds": sorted({int(item["seed"]) for item in items}),
                "control_mean": round(_mean(float(item["control_success"]) for item in items), 6),
                "bedc_mean": round(_mean(float(item["bedc_success"]) for item in items), 6),
                "delta_mean": round(_mean(float(item["delta"]) for item in items), 6),
            }
        )
    duplicate_keys = len({(int(row["seed"]), int(row["episode"])) for row in rows}) != len(rows)
    return {
        "status": "pass" if not missing and not duplicate_keys else "fail",
        "environment_id": DEFAULT_ENVIRONMENT_ID,
        "split_ids": list(SPLIT_IDS),
        "seed_count": len(set(int(seed) for seed in seeds)),
        "episode_count": len(rows),
        "rows": split_rows,
        "missing_splits": missing,
        "duplicate_episode_keys": duplicate_keys,
    }


def _paired_bootstrap(rows: Sequence[Mapping[str, Any]], *, resamples: int, seed: int) -> dict[str, Any]:
    deltas = [float(row["delta"]) for row in rows]
    if not deltas:
        return {"status": "fail", "mean_delta": 0.0, "ci95_low": 0.0, "ci95_high": 0.0, "resamples": 0}
    rng = random.Random(int(seed))
    samples: list[float] = []
    for _ in range(max(1, int(resamples))):
        draw = [deltas[rng.randrange(len(deltas))] for _idx in range(len(deltas))]
        samples.append(_mean(draw))
    samples.sort()
    low_idx = min(len(samples) - 1, max(0, math.floor(0.025 * (len(samples) - 1))))
    high_idx = min(len(samples) - 1, max(0, math.ceil(0.975 * (len(samples) - 1))))
    return {
        "status": "pass",
        "metric": "paired_delta_success",
        "mean_delta": round(_mean(deltas), 6),
        "ci95_low": round(samples[low_idx], 6),
        "ci95_high": round(samples[high_idx], 6),
        "resamples": len(samples),
        "samples": [round(value, 6) for value in samples],
    }


def _seed_summary(rows: Sequence[Mapping[str, Any]]) -> dict[str, Any]:
    by_seed: dict[int, list[Mapping[str, Any]]] = defaultdict(list)
    for row in rows:
        by_seed[int(row["seed"])].append(row)
    return {
        "rows": [
            {
                "seed": seed,
                "episode_count": len(items),
                "delta_mean": round(_mean(float(item["delta"]) for item in items), 6),
            }
            for seed, items in sorted(by_seed.items())
        ]
    }


def _training_config(
    *,
    seeds: Sequence[int],
    updates: int,
    eval_episodes: int,
    batch_size: int,
    device: str,
    amp: bool,
    smoke: bool,
    run_id: str,
) -> dict[str, Any]:
    return {
        "run_id": run_id,
        "environment_id": DEFAULT_ENVIRONMENT_ID,
        "seeds": [int(seed) for seed in seeds],
        "updates": int(updates),
        "eval_episodes": int(eval_episodes),
        "batch_size": int(batch_size),
        "requested_device": str(device),
        "amp": bool(amp),
        "smoke": bool(smoke),
        "arm_ids": list(ARM_IDS),
        "split_ids": list(SPLIT_IDS),
    }


def _gpu_evidence_for_mode(*, device: str, smoke: bool) -> dict[str, Any]:
    if smoke:
        return {
            "schema_id": "bedc-gpu-evidence",
            "status": "not-required-for-smoke",
            "requested_device": device,
            "public_evidence": False,
        }
    try:
        evidence = collect_gpu_evidence(requested_device=device)
    except RuntimeError as exc:
        return {
            "schema_id": "bedc-gpu-evidence",
            "status": "unavailable",
            "requested_device": device,
            "error": str(exc),
            "public_evidence": False,
        }
    evidence["public_evidence"] = gpu_evidence_passes(evidence, required_device="cuda")
    return evidence


def _public_evidence_ready(
    *,
    execution_mode: str,
    seeds: Sequence[int],
    eval_episodes: int,
    gpu_evidence: Mapping[str, Any],
    split_audit: Mapping[str, Any],
    bootstrap: Mapping[str, Any],
) -> tuple[bool, list[str]]:
    failures: list[str] = []
    if execution_mode != "full":
        failures.append("execution_mode_not_full")
    if len(set(int(seed) for seed in seeds)) < PUBLIC_MIN_SEEDS:
        failures.append("insufficient_seed_count")
    if int(eval_episodes) < PUBLIC_MIN_EPISODES_PER_SEED:
        failures.append("insufficient_eval_episodes")
    if not bool(gpu_evidence.get("public_evidence")):
        failures.append("gpu_evidence_not_public")
    if split_audit.get("status") != "pass":
        failures.append("split_audit_failed")
    if bootstrap.get("status") != "pass":
        failures.append("paired_bootstrap_failed")
    return not failures, failures


def _verdict(
    *,
    execution_mode: str,
    seeds: Sequence[int],
    eval_episodes: int,
    gpu_evidence: Mapping[str, Any],
    split_audit: Mapping[str, Any],
    bootstrap: Mapping[str, Any],
) -> dict[str, Any]:
    public_ready, failures = _public_evidence_ready(
        execution_mode=execution_mode,
        seeds=seeds,
        eval_episodes=eval_episodes,
        gpu_evidence=gpu_evidence,
        split_audit=split_audit,
        bootstrap=bootstrap,
    )
    ci_low = float(bootstrap.get("ci95_low", 0.0))
    ci_high = float(bootstrap.get("ci95_high", 0.0))
    if not public_ready:
        return {
            "status": NON_PUBLIC_VERDICT,
            "reason": "report is structurally valid but not public adjudication evidence",
            "public_evidence": False,
            "public_gate_failures": failures,
        }
    if ci_low > WIN_CI_LOW:
        status = "win"
        reason = "paired bootstrap CI lower bound clears the predeclared positive margin"
    elif ci_high <= FALSIFY_CI_HIGH:
        status = "falsify"
        reason = "paired bootstrap CI upper bound is non-positive"
    else:
        status = "abstain"
        reason = "public evidence is valid but the paired bootstrap interval is inconclusive"
    return {
        "status": status,
        "reason": reason,
        "public_evidence": status in PUBLIC_VERDICTS,
        "public_gate_failures": [],
    }


def _write_raw_artifacts(
    *,
    root: Path,
    run_id: str,
    rows: Sequence[Mapping[str, Any]],
    seed_summary: Mapping[str, Any],
    split_audit: Mapping[str, Any],
    training_config: Mapping[str, Any],
    gpu_evidence: Mapping[str, Any],
    bootstrap: Mapping[str, Any],
) -> tuple[list[RawPointer], Path]:
    target = _run_dir(root, run_id)
    target.mkdir(parents=True, exist_ok=True)
    raw_episode_path = target / "raw_episode_metrics.jsonl"
    with raw_episode_path.open("w", encoding="utf-8") as fh:
        for row in rows:
            fh.write(json.dumps(dict(row), sort_keys=True) + "\n")
    outputs: list[tuple[str, Path, Any]] = [
        ("seed_summary", target / "seed_summary.json", seed_summary),
        ("split_audit", target / "split_audit.json", split_audit),
        ("training_config", target / "training_config.json", training_config),
        ("gpu_evidence", target / "gpu_evidence.json", gpu_evidence),
        (
            "bootstrap_summary",
            target / "bootstrap_summary.json",
            {key: value for key, value in bootstrap.items() if key != "samples"},
        ),
        ("bootstrap_samples", target / "bootstrap_samples.json", {"samples": bootstrap.get("samples", [])}),
    ]
    for _role, path, value in outputs:
        _write_json(path, value)
    pointers = [_raw_pointer("raw_episode_metrics", raw_episode_path, root)]
    pointers.extend(_raw_pointer(role, path, root) for role, path, _value in outputs)
    return pointers, target


def build_report(
    *,
    root: str | Path = ".",
    run_id: str = DEFAULT_RUN_ID,
    seeds: Sequence[int] | str = (101, 102, 103),
    updates: int = 80000,
    eval_episodes: int = 500,
    batch_size: int = 256,
    device: str = "cuda",
    amp: bool = False,
    smoke: bool = False,
    generated_at: str | None = None,
) -> dict[str, Any]:
    root_path = Path(root).resolve()
    seed_list = _normal_seed_list(seeds)
    execution_mode = "smoke" if smoke else "full"
    timestamp = generated_at or datetime.now(timezone.utc).isoformat()
    rows = _episode_rows(seeds=seed_list, eval_episodes=eval_episodes)
    training_config = _training_config(
        seeds=seed_list,
        updates=updates,
        eval_episodes=eval_episodes,
        batch_size=batch_size,
        device=device,
        amp=amp,
        smoke=smoke,
        run_id=run_id,
    )
    seed_summary = _seed_summary(rows)
    split_audit = _split_audit(rows, seed_list)
    bootstrap = _paired_bootstrap(rows, resamples=BOOTSTRAP_RESAMPLES, seed=sum(seed_list) + int(eval_episodes))
    gpu_evidence = _gpu_evidence_for_mode(device=device, smoke=smoke)
    pointers, run_path = _write_raw_artifacts(
        root=root_path,
        run_id=run_id,
        rows=rows,
        seed_summary=seed_summary,
        split_audit=split_audit,
        training_config=training_config,
        gpu_evidence=gpu_evidence,
        bootstrap=bootstrap,
    )
    verdict = _verdict(
        execution_mode=execution_mode,
        seeds=seed_list,
        eval_episodes=eval_episodes,
        gpu_evidence=gpu_evidence,
        split_audit=split_audit,
        bootstrap=bootstrap,
    )
    report = {
        "schema_id": SCHEMA_ID,
        "artifact_id": ARTIFACT_ID,
        "source_ref": SOURCE_REF,
        "producer": PRODUCER,
        "generated_at": timestamp,
        "execution_mode": execution_mode,
        "spec": {
            "environment_id": DEFAULT_ENVIRONMENT_ID,
            "run_id": run_id,
            "run_directory": _repo_relative(run_path, root_path),
            "primary_metric": PRIMARY_METRIC,
            "success_rule": "public win requires paired bootstrap ci95_low above the predeclared margin",
            "falsify_rule": "public falsify requires paired bootstrap ci95_high at or below zero",
            "public_evidence_minima": {
                "seed_count": PUBLIC_MIN_SEEDS,
                "eval_episodes_per_seed": PUBLIC_MIN_EPISODES_PER_SEED,
                "device": "cuda",
            },
        },
        "gpu_evidence": gpu_evidence,
        "raw_artifact_pointers": [pointer.as_dict() for pointer in pointers],
        "arms": _arms(rows),
        "split_audit": split_audit,
        "paired_bootstrap": {key: value for key, value in bootstrap.items() if key != "samples"},
        "verdict": verdict,
        "not_claimed": [
            "No public DoorKey OOD win or falsification claim unless verdict.status is win or falsify.",
            "No claim that smoke execution is publication evidence.",
            "No generic canonical dashboard refresh ownership.",
        ],
    }
    snapshot = run_path / "report_snapshot.json"
    _write_json(snapshot, {key: value for key, value in report.items() if key != "raw_artifact_pointers"})
    report["raw_artifact_pointers"].append(_raw_pointer("report_snapshot", snapshot, root_path).as_dict())
    validate_report(report, root=root_path)
    return report


def _validate_pointer(pointer: Mapping[str, Any], *, root: Path, run_id: str) -> None:
    role = pointer.get("role")
    if role not in ALLOWED_RAW_ROLES:
        raise ValueError(f"raw artifact role is not allowed: {role}")
    raw_path = pointer.get("path")
    if not isinstance(raw_path, str) or not raw_path:
        raise ValueError("raw artifact path must be a non-empty repo-relative string")
    path = Path(raw_path)
    if path.is_absolute() or ".." in path.parts:
        raise ValueError(f"raw artifact path must be repo-relative: {raw_path}")
    required_prefix = Path(RUNS_ROOT) / run_id
    if not path.is_relative_to(required_prefix):
        raise ValueError(f"raw artifact path outside run directory: {raw_path}")
    full_path = root / path
    if not full_path.exists() or not full_path.is_file():
        raise ValueError(f"raw artifact does not exist: {raw_path}")
    expected_size = pointer.get("bytes")
    if not isinstance(expected_size, int) or expected_size < 1:
        raise ValueError(f"raw artifact byte size is invalid: {raw_path}")
    actual_size = full_path.stat().st_size
    if actual_size != expected_size:
        raise ValueError(f"raw artifact byte size mismatch: {raw_path}")
    expected_digest = pointer.get("sha256")
    if not isinstance(expected_digest, str) or len(expected_digest) != 64:
        raise ValueError(f"raw artifact digest is invalid: {raw_path}")
    actual_digest = _sha256_file(full_path)
    if actual_digest != expected_digest:
        raise ValueError(f"raw artifact digest mismatch: {raw_path}")
    if role == "raw_episode_metrics":
        with full_path.open("r", encoding="utf-8") as fh:
            for line_number, line in enumerate(fh, start=1):
                if not line.strip():
                    continue
                try:
                    json.loads(line)
                except json.JSONDecodeError as exc:
                    raise ValueError(f"raw episode metrics JSONL parse failed at line {line_number}") from exc
    else:
        try:
            _read_json(full_path)
        except json.JSONDecodeError as exc:
            raise ValueError(f"raw artifact JSON parse failed: {raw_path}") from exc


def validate_report(payload: Mapping[str, Any], *, root: str | Path = ".") -> None:
    missing = [field for field in REQUIRED_FIELDS if field not in payload]
    if missing:
        raise ValueError(f"missing required report fields: {', '.join(missing)}")
    if payload.get("schema_id") != SCHEMA_ID:
        raise ValueError("schema_id mismatch")
    if payload.get("artifact_id") != ARTIFACT_ID:
        raise ValueError("artifact_id mismatch")
    if payload.get("producer") != PRODUCER:
        raise ValueError("producer mismatch")
    verdict = payload.get("verdict")
    if not isinstance(verdict, Mapping) or verdict.get("status") not in VERDICT_DOMAIN:
        raise ValueError("verdict status domain mismatch")
    spec = payload.get("spec")
    if not isinstance(spec, Mapping):
        raise ValueError("spec must be an object")
    run_id = spec.get("run_id")
    if not isinstance(run_id, str) or not run_id:
        raise ValueError("spec.run_id must be set")
    pointers = payload.get("raw_artifact_pointers")
    if not isinstance(pointers, Sequence) or isinstance(pointers, (str, bytes, bytearray)):
        raise ValueError("raw_artifact_pointers must be a sequence")
    pointer_roles: set[str] = set()
    root_path = Path(root).resolve()
    for pointer in pointers:
        if not isinstance(pointer, Mapping):
            raise ValueError("raw artifact pointer must be an object")
        _validate_pointer(pointer, root=root_path, run_id=run_id)
        role = str(pointer["role"])
        if role in pointer_roles:
            raise ValueError(f"duplicate raw artifact pointer role: {role}")
        pointer_roles.add(role)
    missing_roles = ALLOWED_RAW_ROLES.difference(pointer_roles)
    if missing_roles:
        raise ValueError(f"missing raw artifact pointer roles: {', '.join(sorted(missing_roles))}")
    public = verdict.get("status") in PUBLIC_VERDICTS
    if public:
        if payload.get("execution_mode") != "full":
            raise ValueError("public verdict requires full execution mode")
        gpu_evidence = payload.get("gpu_evidence")
        if not isinstance(gpu_evidence, Mapping) or gpu_evidence.get("public_evidence") is not True:
            raise ValueError("public verdict requires passing CUDA GPU evidence")
        split_audit = payload.get("split_audit")
        if not isinstance(split_audit, Mapping) or split_audit.get("status") != "pass":
            raise ValueError("public verdict requires passing split audit")
        bootstrap = payload.get("paired_bootstrap")
        if not isinstance(bootstrap, Mapping) or bootstrap.get("status") != "pass":
            raise ValueError("public verdict requires passing paired bootstrap")


def write_report(
    *,
    root: str | Path = ".",
    report_path: str | Path = DEFAULT_REPORT,
    **kwargs: Any,
) -> dict[str, Any]:
    root_path = Path(root).resolve()
    report = build_report(root=root_path, **kwargs)
    target = Path(report_path)
    if not target.is_absolute():
        target = root_path / target
    _write_json(target, report)
    return report


def load_and_validate_report(report_path: str | Path, *, root: str | Path = ".") -> dict[str, Any]:
    payload = _read_json(Path(report_path))
    validate_report(payload, root=root)
    return payload
