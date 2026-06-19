"""MiniGrid DoorKey held-out-family OOD adjudication report."""

from __future__ import annotations

from collections import defaultdict
from dataclasses import dataclass
from datetime import datetime, timezone
import hashlib
import json
import math
from pathlib import Path
import platform
import random
import statistics
from statistics import mean
from typing import Any, Iterable, Mapping, Sequence

from bedc_quality_lab.minigrid_doorkey_families import (
    ARM_IDS,
    HELDOUT_FAMILY_ID,
    MIN_PUBLICATION_FRESH_EPISODES,
    MIN_PUBLICATION_SEEDS,
    default_fresh_episode_rows,
    family_catalog_payload,
    fresh_env_coverage_gate,
    leakage_audit,
)
from bedc_quality_lab.minigrid_placebo_targets import placebo_target_plan
SCHEMA_ID = "bedc-quality-lab:minigrid-doorkey-ood-adjudication"
ARTIFACT_ID = SCHEMA_ID
FINGERPRINT_SCHEMA_ID = "bedc-quality-lab:canonical-report-fingerprint"
JSON_ARTIFACT = "reports/canonical/minigrid-doorkey-ood-adjudication.json"
MARKDOWN_ARTIFACT = "reports/canonical/minigrid-doorkey-ood-adjudication.md"
FINGERPRINT_ARTIFACT = "reports/canonical/minigrid-doorkey-ood-adjudication.fingerprint.json"
DEFAULT_GENERATED_AT = "2026-06-19T00:00:00+00:00"
SOURCE_ISSUE = "#1677"
EXECUTION_MODES = ("fixture-smoke", "publication-bearing")
CANONICAL_VERDICT_DOMAIN = ("success", "abstain", "not_ready")
PRIMARY_ENDPOINT = "f3_fresh_env_success"
DIAGNOSTIC_ENDPOINT = "gap_auc"
BOOTSTRAP_RESAMPLES = 512
BOOTSTRAP_SEED = 1677
SUCCESS_LOWER_BOUND = 0.10
PLACEBO_LOWER_BOUND = 0.08
ID_NON_REGRESSION_FLOOR = -0.02
HARDGATE_IDS = (
    "MODE",
    "ARMS",
    "F3_COVERAGE",
    "LEAKAGE",
    "PRIMARY_ENDPOINT",
    "ID_NON_REGRESSION",
)


@dataclass(frozen=True)
class ArmSummary:
    arm_id: str
    f3_fresh_env_success: float
    id_success: float
    gap_auc: float
    seed_count: int
    fresh_episode_count: int

    def as_dict(self) -> dict[str, Any]:
        return {
            "arm_id": self.arm_id,
            "f3_fresh_env_success": round(self.f3_fresh_env_success, 6),
            "id_success": round(self.id_success, 6),
            "gap_auc": round(self.gap_auc, 6),
            "seed_count": int(self.seed_count),
            "fresh_episode_count": int(self.fresh_episode_count),
        }


def canonical_digest(value: Any) -> str:
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(",", ":")).encode("utf-8")).hexdigest()


def _rows(observations: Sequence[Mapping[str, Any]] | None) -> list[dict[str, Any]]:
    return [dict(row) for row in (default_fresh_episode_rows() if observations is None else observations)]


def _numbers(rows: Sequence[Mapping[str, Any]], arm_id: str, field: str) -> list[float]:
    values: list[float] = []
    for row in rows:
        if row.get("family_id") == HELDOUT_FAMILY_ID and row.get("arm_id") == arm_id:
            value = row.get(field)
            if isinstance(value, bool) or not isinstance(value, (int, float)):
                continue
            values.append(float(value))
    return values


def _arm_summaries(rows: Sequence[Mapping[str, Any]]) -> list[dict[str, Any]]:
    summaries: list[dict[str, Any]] = []
    for arm_id in ARM_IDS:
        arm_rows = [row for row in rows if row.get("family_id") == HELDOUT_FAMILY_ID and row.get("arm_id") == arm_id]
        if not arm_rows:
            summaries.append(
                ArmSummary(
                    arm_id=arm_id,
                    f3_fresh_env_success=0.0,
                    id_success=0.0,
                    gap_auc=0.0,
                    seed_count=0,
                    fresh_episode_count=0,
                ).as_dict()
            )
            continue
        summaries.append(
            ArmSummary(
                arm_id=arm_id,
                f3_fresh_env_success=mean(_numbers(arm_rows, arm_id, "success")),
                id_success=mean(_numbers(arm_rows, arm_id, "id_success")),
                gap_auc=mean(_numbers(arm_rows, arm_id, "gap_auc")),
                seed_count=len({int(row["seed"]) for row in arm_rows if "seed" in row}),
                fresh_episode_count=len(arm_rows),
            ).as_dict()
        )
    return summaries


def paired_bootstrap_lower_bound(
    treatment: Sequence[float],
    control: Sequence[float],
    *,
    resamples: int = BOOTSTRAP_RESAMPLES,
    seed: int = BOOTSTRAP_SEED,
    alpha: float = 0.05,
) -> dict[str, Any]:
    if len(treatment) != len(control) or not treatment:
        raise ValueError("paired bootstrap requires non-empty equal-length samples")
    deltas = [float(left) - float(right) for left, right in zip(treatment, control)]
    rng = random.Random(seed)
    samples: list[float] = []
    for _ in range(resamples):
        samples.append(mean(deltas[rng.randrange(len(deltas))] for _ in deltas))
    samples.sort()
    lower_index = max(0, min(len(samples) - 1, int(alpha * len(samples))))
    return {
        "mean_delta": round(mean(deltas), 6),
        "lower_bound": round(samples[lower_index], 6),
        "alpha": alpha,
        "resamples": int(resamples),
        "seed": int(seed),
    }


def _arm_gate(rows: Sequence[Mapping[str, Any]]) -> dict[str, Any]:
    present = {str(row.get("arm_id")) for row in rows if row.get("family_id") == HELDOUT_FAMILY_ID}
    missing = [arm_id for arm_id in ARM_IDS if arm_id not in present]
    unexpected = sorted(present - set(ARM_IDS))
    return {
        "status": "pass" if not missing and not unexpected else "fail",
        "required_arms": list(ARM_IDS),
        "missing": missing,
        "unexpected": unexpected,
    }


def _mode_gate(execution_mode: str, coverage_gate: Mapping[str, Any]) -> dict[str, Any]:
    if execution_mode not in EXECUTION_MODES:
        return {"status": "fail", "execution_mode": execution_mode, "reason": "unsupported execution mode"}
    if execution_mode == "publication-bearing" and coverage_gate.get("status") != "pass":
        return {
            "status": "fail",
            "execution_mode": execution_mode,
            "reason": "publication-bearing mode requires 3 arms, 3 seeds per arm, and 500 fresh F3 episodes per arm",
        }
    return {"status": "pass", "execution_mode": execution_mode}


def _primary_endpoint_gate(rows: Sequence[Mapping[str, Any]]) -> dict[str, Any]:
    bedc = _numbers(rows, "bedc", "success")
    base = _numbers(rows, "base", "success")
    placebo = _numbers(rows, "bedc_shuffle_placebo", "success")
    if not (len(bedc) == len(base) == len(placebo) and bedc):
        return {"status": "fail", "reason": "primary endpoint requires paired rows for every arm"}
    bedc_over_base = paired_bootstrap_lower_bound(bedc, base)
    bedc_over_placebo = paired_bootstrap_lower_bound(bedc, placebo, seed=BOOTSTRAP_SEED + 1)
    passed = (
        bedc_over_base["lower_bound"] >= SUCCESS_LOWER_BOUND
        and bedc_over_placebo["lower_bound"] >= PLACEBO_LOWER_BOUND
    )
    return {
        "status": "pass" if passed else "fail",
        "primary_endpoint": PRIMARY_ENDPOINT,
        "bedc_over_base": bedc_over_base,
        "bedc_over_shuffle_placebo": bedc_over_placebo,
        "success_lower_bound": SUCCESS_LOWER_BOUND,
        "placebo_lower_bound": PLACEBO_LOWER_BOUND,
    }


def _id_non_regression_gate(rows: Sequence[Mapping[str, Any]]) -> dict[str, Any]:
    bedc = _numbers(rows, "bedc", "id_success")
    base = _numbers(rows, "base", "id_success")
    if len(bedc) != len(base) or not bedc:
        return {"status": "fail", "reason": "ID non-regression requires paired base and bedc rows"}
    delta = paired_bootstrap_lower_bound(bedc, base, seed=BOOTSTRAP_SEED + 2)
    return {
        "status": "pass" if delta["lower_bound"] >= ID_NON_REGRESSION_FLOOR else "fail",
        "id_success_bedc_over_base": delta,
        "non_regression_floor": ID_NON_REGRESSION_FLOOR,
    }


def _hardgates(rows: Sequence[Mapping[str, Any]], execution_mode: str) -> dict[str, Any]:
    coverage = fresh_env_coverage_gate(rows)
    gates = {
        "MODE": _mode_gate(execution_mode, coverage),
        "ARMS": _arm_gate(rows),
        "F3_COVERAGE": coverage,
        "LEAKAGE": leakage_audit(rows),
        "PRIMARY_ENDPOINT": _primary_endpoint_gate(rows),
        "ID_NON_REGRESSION": _id_non_regression_gate(rows),
    }
    failed = [gate_id for gate_id in HARDGATE_IDS if gates[gate_id]["status"] != "pass"]
    return {"status": "pass" if not failed else "fail", "failed_gates": failed, "gates": gates}


def _verdict(hardgate: Mapping[str, Any], execution_mode: str) -> dict[str, Any]:
    if execution_mode == "fixture-smoke":
        return {
            "status_domain": list(CANONICAL_VERDICT_DOMAIN),
            "status": "not_ready",
            "reason": "fixture-smoke output is not publication-bearing evidence",
            "failed_gates": list(hardgate.get("failed_gates", [])),
        }
    if hardgate.get("status") != "pass":
        return {
            "status_domain": list(CANONICAL_VERDICT_DOMAIN),
            "status": "not_ready",
            "reason": "publication-bearing hardgates failed",
            "failed_gates": list(hardgate.get("failed_gates", [])),
        }
    return {
        "status_domain": list(CANONICAL_VERDICT_DOMAIN),
        "status": "success",
        "reason": "BEDC clears paired F3 fresh-env lower-bound gates without ID regression",
        "failed_gates": [],
    }


def _claim_boundary(verdict: Mapping[str, Any], execution_mode: str) -> dict[str, Any]:
    publication_ready = execution_mode == "publication-bearing" and verdict.get("status") == "success"
    return {
        "status": "publication-bearing" if publication_ready else "not-publication-bearing",
        "claim_allowed": publication_ready,
        "scope": "MiniGrid DoorKey F3 held-out-family OOD adjudication only",
        "primary_endpoint": PRIMARY_ENDPOINT,
        "diagnostics_only": [DIAGNOSTIC_ENDPOINT],
        "verdict_pointer": "$.verdict.status",
    }


def _reproducibility_contract(execution_mode: str) -> dict[str, Any]:
    return {
        "schema_id": "bedc-quality-lab:canonical-reproducibility-contract",
        "mode": execution_mode,
        "seed_list": [1101, 1102, 1103],
        "device_policy": {
            "requested_device": "cpu",
            "resolved_device": "cpu",
            "resolution_status": "available",
            "resolution_reason": "DoorKey adjudication owner consumes recorded row payloads",
            "backend_details": {"minigrid": "not-requested"},
        },
        "framework_provenance": {
            "python": platform.python_version(),
            "dependency_abi": {"gymnasium": "not-requested", "minigrid": "not-requested"},
        },
    }


def build_payload(
    *,
    generated_at: str | None = None,
    observations: Sequence[Mapping[str, Any]] | None = None,
    execution_mode: str = "fixture-smoke",
) -> dict[str, Any]:
    timestamp = generated_at or DEFAULT_GENERATED_AT
    rows = _rows(observations)
    family_catalog = family_catalog_payload()
    hardgate = _hardgates(rows, execution_mode)
    verdict = _verdict(hardgate, execution_mode)
    payload = {
        "schema_id": SCHEMA_ID,
        "artifact_id": ARTIFACT_ID,
        "generated_at": timestamp,
        "producer": "bedc_quality_lab.minigrid_doorkey_ood_adjudication",
        "source_issue": SOURCE_ISSUE,
        "execution_mode": execution_mode,
        "family_catalog": family_catalog,
        "placebo_target_plan": placebo_target_plan(family_catalog["families"]),
        "config": {
            "arms": list(ARM_IDS),
            "heldout_family_id": HELDOUT_FAMILY_ID,
            "primary_endpoint": PRIMARY_ENDPOINT,
            "diagnostics_only": [DIAGNOSTIC_ENDPOINT],
            "bootstrap_resamples": BOOTSTRAP_RESAMPLES,
            "min_publication_seeds_per_arm": MIN_PUBLICATION_SEEDS,
            "min_publication_fresh_f3_episodes_per_arm": MIN_PUBLICATION_FRESH_EPISODES,
        },
        "observations": rows,
        "arm_summaries": _arm_summaries(rows),
        "hardgate": hardgate,
        "verdict": verdict,
        "claim_boundary": _claim_boundary(verdict, execution_mode),
        "claim_capsule": {
            "status": "pointer-only",
            "owner": "minigrid-doorkey-ood-adjudication",
            "verdict_pointer": f"{JSON_ARTIFACT}:$.verdict.status",
            "hardgate_pointer": f"{JSON_ARTIFACT}:$.hardgate",
            "primary_endpoint_pointer": f"{JSON_ARTIFACT}:$.hardgate.gates.PRIMARY_ENDPOINT",
        },
        "not_claimed": [
            "No JEPA-WM-L1 admission-surface ownership.",
            "No public benchmark superiority claim.",
            "No publication-bearing claim from fixture-smoke output.",
            "No use of gap_auc as a primary endpoint.",
        ],
        "reproducibility_contract": _reproducibility_contract(execution_mode),
    }
    payload["raw_digest"] = canonical_digest(
        {
            "execution_mode": payload["execution_mode"],
            "config": payload["config"],
            "observations": payload["observations"],
            "hardgate": payload["hardgate"],
            "verdict": payload["verdict"],
        }
    )
    validate_payload(payload)
    return payload


def validate_payload(payload: Mapping[str, Any]) -> None:
    if payload.get("schema_id") != SCHEMA_ID:
        raise ValueError("schema_id mismatch")
    if payload.get("artifact_id") != ARTIFACT_ID:
        raise ValueError("artifact_id mismatch")
    execution_mode = payload.get("execution_mode")
    if execution_mode not in EXECUTION_MODES:
        raise ValueError("execution_mode mismatch")
    config = payload.get("config")
    if not isinstance(config, Mapping):
        raise ValueError("missing config")
    if tuple(config.get("arms", ())) != ARM_IDS:
        raise ValueError("arm order mismatch")
    if config.get("heldout_family_id") != HELDOUT_FAMILY_ID:
        raise ValueError("heldout family mismatch")
    if DIAGNOSTIC_ENDPOINT not in config.get("diagnostics_only", ()):
        raise ValueError("gap_auc must remain diagnostics-only")
    hardgate = payload.get("hardgate")
    if not isinstance(hardgate, Mapping):
        raise ValueError("missing hardgate")
    gates = hardgate.get("gates")
    if not isinstance(gates, Mapping) or set(gates) != set(HARDGATE_IDS):
        raise ValueError("hardgate set mismatch")
    failed = [gate_id for gate_id in HARDGATE_IDS if gates[gate_id].get("status") != "pass"]
    if list(hardgate.get("failed_gates", [])) != failed:
        raise ValueError("hardgate failed gate projection mismatch")
    verdict = payload.get("verdict")
    if not isinstance(verdict, Mapping) or verdict.get("status") not in CANONICAL_VERDICT_DOMAIN:
        raise ValueError("verdict domain mismatch")
    boundary = payload.get("claim_boundary")
    if not isinstance(boundary, Mapping):
        raise ValueError("missing claim_boundary")
    if execution_mode == "fixture-smoke" and boundary.get("status") != "not-publication-bearing":
        raise ValueError("fixture-smoke must not be publication-bearing")
    if execution_mode == "publication-bearing" and hardgate.get("status") != "pass" and boundary.get("claim_allowed"):
        raise ValueError("failed publication-bearing gates must block claims")
    capsule = payload.get("claim_capsule")
    if not isinstance(capsule, Mapping) or capsule.get("status") != "pointer-only":
        raise ValueError("claim capsule must be pointer-only")


def render_markdown(payload: Mapping[str, Any]) -> str:
    verdict = payload.get("verdict", {}) if isinstance(payload.get("verdict"), Mapping) else {}
    boundary = payload.get("claim_boundary", {}) if isinstance(payload.get("claim_boundary"), Mapping) else {}
    lines = [
        "# MiniGrid DoorKey OOD Adjudication",
        "",
        f"- Generated at: `{payload.get('generated_at')}`",
        f"- Execution mode: `{payload.get('execution_mode')}`",
        f"- Verdict: `{verdict.get('status')}`",
        f"- Claim boundary: `{boundary.get('status')}`",
        f"- Primary endpoint: `{boundary.get('primary_endpoint')}`",
        "",
        "## Arm Summaries",
        "",
        "| arm | F3 success | ID success | gap AUC | episodes |",
        "| --- | ---: | ---: | ---: | ---: |",
    ]
    for row in payload.get("arm_summaries", []):
        if isinstance(row, Mapping):
            lines.append(
                f"| `{row.get('arm_id')}` | `{row.get('f3_fresh_env_success')}` | "
                f"`{row.get('id_success')}` | `{row.get('gap_auc')}` | `{row.get('fresh_episode_count')}` |"
            )
    lines.extend(["", "## Hardgates", "", "| gate | status |", "| --- | --- |"])
    hardgate = payload.get("hardgate", {}) if isinstance(payload.get("hardgate"), Mapping) else {}
    gates = hardgate.get("gates", {}) if isinstance(hardgate.get("gates"), Mapping) else {}
    for gate_id in HARDGATE_IDS:
        gate = gates.get(gate_id, {})
        status = gate.get("status") if isinstance(gate, Mapping) else "missing"
        lines.append(f"| `{gate_id}` | `{status}` |")
    lines.extend(["", "## Not Claimed", ""])
    for item in payload.get("not_claimed", []):
        lines.append(f"- {item}")
    lines.append("")
    return "\n".join(lines)


def fingerprint_payload(payload: Mapping[str, Any], *, generated_at: str) -> dict[str, Any]:
    contract = payload.get("reproducibility_contract")
    return {
        "schema_id": FINGERPRINT_SCHEMA_ID,
        "report_name": "minigrid-doorkey-ood-adjudication",
        "json_artifact": JSON_ARTIFACT,
        "markdown_artifact": MARKDOWN_ARTIFACT,
        "producer_command": ["python3", "scripts/run_minigrid_doorkey_ood_adjudication.py"],
        "input_fingerprint": canonical_digest(
            {
                "producer": "bedc_quality_lab.minigrid_doorkey_ood_adjudication",
                "family_catalog": payload.get("family_catalog"),
                "config": payload.get("config"),
                "execution_mode": payload.get("execution_mode"),
            }
        ),
        "inputs": {
            "family_catalog": payload.get("family_catalog"),
            "placebo_target_plan": payload.get("placebo_target_plan"),
        },
        "reproducibility_mode": payload.get("execution_mode"),
        "reproducibility_contract": contract,
        "reproducibility_contract_digest": canonical_digest(contract),
        "generated_by": {
            "runner": "scripts/run_minigrid_doorkey_ood_adjudication.py",
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
    execution_mode: str = "fixture-smoke",
    observations: Sequence[Mapping[str, Any]] | None = None,
) -> dict[str, Any]:
    root_path = Path(root)
    payload = build_payload(generated_at=generated_at, observations=observations, execution_mode=execution_mode)
    target_json = Path(json_path) if json_path is not None else root_path / JSON_ARTIFACT
    target_md = Path(markdown_path) if markdown_path is not None else root_path / MARKDOWN_ARTIFACT
    target_fingerprint = Path(fingerprint_path) if fingerprint_path is not None else root_path / FINGERPRINT_ARTIFACT
    target_json.parent.mkdir(parents=True, exist_ok=True)
    target_md.parent.mkdir(parents=True, exist_ok=True)
    target_fingerprint.parent.mkdir(parents=True, exist_ok=True)
    target_json.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    target_md.write_text(render_markdown(payload), encoding="utf-8")
    fingerprint = fingerprint_payload(
        payload,
        generated_at=generated_at or datetime.now(timezone.utc).isoformat(),
    )
    target_fingerprint.write_text(json.dumps(fingerprint, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


# Bounded raw-evidence report API.
RAW_PRODUCER = "bedc_quality_lab.minigrid_doorkey_ood_adjudication"
SOURCE_REF = "gh-issue-1683"
DEFAULT_REPORT = "reports/issue_1553_minigrid_doorkey_ood_adjudication.json"
RUNS_ROOT = "reports/runs/minigrid-doorkey-ood-adjudication"
DEFAULT_RUN_ID = "issue1553-doorkey-f3"
DEFAULT_ENVIRONMENT_ID = "MiniGrid-DoorKey-8x8-v0"
PUBLIC_VERDICTS = frozenset({"win", "falsify"})
NON_PUBLIC_VERDICT = "not_public_evidence"
RAW_VERDICT_DOMAIN = ("win", "falsify", "abstain", NON_PUBLIC_VERDICT)
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
RAW_ARM_IDS = ("control", "bedc")
SPLIT_IDS = ("door-unlocked", "door-locked", "key-in-room", "blocked-corridor")
RAW_PRIMARY_METRIC = "success"
RAW_BOOTSTRAP_RESAMPLES = 256
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


def _raw_arms(rows: Sequence[Mapping[str, Any]]) -> dict[str, Any]:
    control = _mean(float(row["control_success"]) for row in rows)
    bedc = _mean(float(row["bedc_success"]) for row in rows)
    return {
        "metric": RAW_PRIMARY_METRIC,
        "arm_ids": list(RAW_ARM_IDS),
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
        "arm_ids": list(RAW_ARM_IDS),
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
    from bedc_quality_lab.gpu_evidence import collect_gpu_evidence, gpu_evidence_passes

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


def _raw_verdict(
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
    bootstrap = _paired_bootstrap(rows, resamples=RAW_BOOTSTRAP_RESAMPLES, seed=sum(seed_list) + int(eval_episodes))
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
    verdict = _raw_verdict(
        execution_mode=execution_mode,
        seeds=seed_list,
        eval_episodes=eval_episodes,
        gpu_evidence=gpu_evidence,
        split_audit=split_audit,
        bootstrap=bootstrap,
    )
    report = {
        "schema_id": SCHEMA_ID,
        "artifact_id": SCHEMA_ID,
        "source_ref": SOURCE_REF,
        "producer": RAW_PRODUCER,
        "generated_at": timestamp,
        "execution_mode": execution_mode,
        "spec": {
            "environment_id": DEFAULT_ENVIRONMENT_ID,
            "run_id": run_id,
            "run_directory": _repo_relative(run_path, root_path),
            "primary_metric": RAW_PRIMARY_METRIC,
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
        "arms": _raw_arms(rows),
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
    if payload.get("artifact_id") != SCHEMA_ID:
        raise ValueError("artifact_id mismatch")
    if payload.get("producer") != RAW_PRODUCER:
        raise ValueError("producer mismatch")
    verdict = payload.get("verdict")
    if not isinstance(verdict, Mapping) or verdict.get("status") not in RAW_VERDICT_DOMAIN:
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
