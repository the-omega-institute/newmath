"""Cache equivalence helpers for canonical cache-backed reports."""

from __future__ import annotations

from dataclasses import asdict, dataclass
import hashlib
import json
from pathlib import Path
from typing import Any, Callable, Iterable, Literal, Mapping, Sequence


SCHEMA_ID = "bedc-quality-lab:canonical-cache-equivalence"
ARTIFACT_ID = "bedc-quality-lab:canonical-cache-equivalence"
CANONICAL_ROLE = "cache_equivalence_owner"
OWNER_ARTIFACT = "reports/canonical/cache-equivalence.json"
ROOT_PREFIX = "papers/bedc-quality-lab"

CACHE_HARDGATES = {
    "CACHE-HG1": "Every compared surface uses sha256 content digests.",
    "CACHE-HG2": "Every cache-backed target has equivalent cold and cache outputs, and the cache leg observes a real hit.",
    "CACHE-HG3": "The cache root used by the audit is outside .refactor-loop.",
}


@dataclass(frozen=True)
class CacheEquivalenceTarget:
    target_id: str
    owner_module: str
    producer_command: tuple[str, ...]
    json_artifact: str
    fingerprint_artifact: str
    summary_artifact: str
    raw_artifacts: tuple[str, ...]


@dataclass(frozen=True)
class SurfaceSpec:
    surface_id: str
    artifact_kind: Literal["single", "multi"]
    artifacts: tuple[str, ...]


CACHE_BACKED_TARGETS: tuple[CacheEquivalenceTarget, ...] = (
    CacheEquivalenceTarget(
        target_id="dgt-l0-controls",
        owner_module="bedc_quality_lab.dgt_l0_controls",
        producer_command=("python3", "scripts/run_dgt_l0_controls.py"),
        json_artifact="reports/canonical/dgt-l0-controls.json",
        fingerprint_artifact="reports/canonical/dgt-l0-controls.fingerprint.json",
        summary_artifact="reports/runs/discovery-gated-transformer/l0-toy-controls/summary.json",
        raw_artifacts=("reports/runs/discovery-gated-transformer/l0-toy-controls/raw_metrics.jsonl",),
    ),
    CacheEquivalenceTarget(
        target_id="dgt-l1-controls",
        owner_module="bedc_quality_lab.dgt_l1_controls",
        producer_command=("python3", "scripts/run_dgt_l1_controls.py"),
        json_artifact="reports/canonical/dgt-l1-controls.json",
        fingerprint_artifact="reports/canonical/dgt-l1-controls.fingerprint.json",
        summary_artifact="reports/runs/discovery-gated-transformer/l1-tiny-sequence-controls/summary.json",
        raw_artifacts=(
            "reports/runs/discovery-gated-transformer/l1-tiny-sequence-controls/raw_metrics.jsonl",
            "reports/runs/discovery-gated-transformer/l1-tiny-sequence-controls/probe_metrics.jsonl",
        ),
    ),
)


def target_registry_rows() -> list[dict[str, Any]]:
    return [asdict(target) for target in CACHE_BACKED_TARGETS]


def targets_by_id() -> dict[str, CacheEquivalenceTarget]:
    return {target.target_id: target for target in CACHE_BACKED_TARGETS}


def select_targets(only: str | None) -> tuple[CacheEquivalenceTarget, ...]:
    if only is None:
        return CACHE_BACKED_TARGETS
    by_id = targets_by_id()
    target = by_id.get(only)
    if target is None:
        return ()
    return (target,)


def unsupported_row(target_id: str) -> dict[str, Any]:
    return {
        "target_id": target_id,
        "status": "unsupported",
        "cache_backed": False,
        "failure_reasons": ["target is not registered as a cache-backed canonical producer"],
        "surfaces": {},
        "cache_observation": {
            "cache_hit_observed": False,
            "events": [],
        },
    }


def surface_specs(target: CacheEquivalenceTarget) -> tuple[SurfaceSpec, ...]:
    return (
        SurfaceSpec("canonical_json", "single", (target.json_artifact,)),
        SurfaceSpec("raw_metrics", "multi", target.raw_artifacts),
        SurfaceSpec("summary", "single", (target.summary_artifact,)),
        SurfaceSpec("fingerprint", "single", (target.fingerprint_artifact,)),
    )


def _json_digest(payload: Any) -> str:
    return hashlib.sha256(
        json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode("utf-8")
    ).hexdigest()


def _path_digest(path: Path) -> dict[str, Any]:
    if not path.is_file():
        return {
            "exists": False,
            "sha256": None,
            "byte_size": None,
        }
    data = path.read_bytes()
    return {
        "exists": True,
        "sha256": hashlib.sha256(data).hexdigest(),
        "byte_size": len(data),
    }


def surface_manifest(root: Path, spec: SurfaceSpec) -> dict[str, Any]:
    files = []
    for artifact in spec.artifacts:
        files.append({"artifact": artifact, **_path_digest(root / artifact)})
    all_present = all(row["exists"] for row in files)
    aggregate_inputs = [
        {
            "artifact": row["artifact"],
            "sha256": row["sha256"],
            "byte_size": row["byte_size"],
        }
        for row in files
    ]
    return {
        "surface_id": spec.surface_id,
        "artifact_kind": spec.artifact_kind,
        "algorithm": "sha256",
        "status": "present" if all_present else "missing",
        "sha256": _json_digest(aggregate_inputs) if all_present else None,
        "files": files,
    }


def surface_manifests(root: Path, target: CacheEquivalenceTarget) -> dict[str, dict[str, Any]]:
    return {spec.surface_id: surface_manifest(root, spec) for spec in surface_specs(target)}


def compare_surfaces(cold: Mapping[str, Mapping[str, Any]], cached: Mapping[str, Mapping[str, Any]]) -> dict[str, dict[str, Any]]:
    rows: dict[str, dict[str, Any]] = {}
    for surface_id in sorted(set(cold) | set(cached)):
        cold_row = dict(cold.get(surface_id, {}))
        cache_row = dict(cached.get(surface_id, {}))
        equivalent = (
            cold_row.get("status") == "present"
            and cache_row.get("status") == "present"
            and cold_row.get("sha256") == cache_row.get("sha256")
        )
        rows[surface_id] = {
            "surface_id": surface_id,
            "status": "pass" if equivalent else "fail",
            "equivalent": equivalent,
            "cold": cold_row,
            "cache": cache_row,
        }
    return rows


def cache_root_policy(cache_root: Path) -> dict[str, Any]:
    expanded = cache_root.expanduser()
    blocked = ".refactor-loop" in expanded.parts
    return {
        "status": "fail" if blocked else "pass",
        "hardgate_id": "CACHE-HG3",
        "root_contains_refactor_loop": blocked,
        "root_policy": "no .refactor-loop path component",
    }


def cache_hit_observed(events: Sequence[Mapping[str, Any]]) -> bool:
    return any(
        event.get("leg") == "cache"
        and event.get("event") == "cache-return"
        and event.get("status") == "hit"
        for event in events
    )


def fold_target_row(
    target: CacheEquivalenceTarget,
    *,
    cold_result: Mapping[str, Any],
    cache_result: Mapping[str, Any],
    cold_surfaces: Mapping[str, Mapping[str, Any]],
    cache_surfaces: Mapping[str, Mapping[str, Any]],
    events: Sequence[Mapping[str, Any]],
) -> dict[str, Any]:
    surface_rows = compare_surfaces(cold_surfaces, cache_surfaces)
    surface_failures = [
        surface_id
        for surface_id, row in surface_rows.items()
        if row["status"] != "pass"
    ]
    hit = cache_hit_observed(events)
    failure_reasons = [f"surface mismatch: {surface_id}" for surface_id in surface_failures]
    if not hit:
        failure_reasons.append("cache leg did not observe a producer cache hit")
    return {
        "target_id": target.target_id,
        "status": "pass" if not failure_reasons else "fail",
        "cache_backed": True,
        "producer_command": list(target.producer_command),
        "cold_result": {
            "status": cold_result.get("status"),
            "producer_status": cold_result.get("producer_status"),
            "fingerprint_status": cold_result.get("fingerprint_status"),
            "fingerprint_reason": cold_result.get("fingerprint_reason"),
        },
        "cache_result": {
            "status": cache_result.get("status"),
            "producer_status": cache_result.get("producer_status"),
            "fingerprint_status": cache_result.get("fingerprint_status"),
            "fingerprint_reason": cache_result.get("fingerprint_reason"),
        },
        "surfaces": surface_rows,
        "cache_observation": {
            "cache_hit_observed": hit,
            "events": [dict(event) for event in events],
        },
        "failure_reasons": failure_reasons,
    }


def hardgate_rows(target_rows: Sequence[Mapping[str, Any]], policy: Mapping[str, Any]) -> dict[str, dict[str, Any]]:
    all_surfaces_digest_backed = all(
        surface.get("cold", {}).get("algorithm") == "sha256"
        and surface.get("cache", {}).get("algorithm") == "sha256"
        for row in target_rows
        if row.get("cache_backed")
        for surface in row.get("surfaces", {}).values()
    )
    all_targets_pass = bool(target_rows) and all(row.get("status") == "pass" for row in target_rows)
    return {
        "CACHE-HG1": {
            "status": "pass" if all_surfaces_digest_backed else "fail",
            "criterion": CACHE_HARDGATES["CACHE-HG1"],
        },
        "CACHE-HG2": {
            "status": "pass" if all_targets_pass else "fail",
            "criterion": CACHE_HARDGATES["CACHE-HG2"],
        },
        "CACHE-HG3": {
            "status": policy.get("status", "fail"),
            "criterion": CACHE_HARDGATES["CACHE-HG3"],
        },
    }


def build_owner_payload(
    *,
    generated_at: str,
    target_rows: Sequence[Mapping[str, Any]],
    policy: Mapping[str, Any],
    cache_root_source: Literal["temporary", "explicit"],
    selected_targets: Sequence[str],
) -> dict[str, Any]:
    gates = hardgate_rows(target_rows, policy)
    status = "pass" if all(row["status"] == "pass" for row in gates.values()) else "fail"
    rows = [dict(row) for row in target_rows]
    return {
        "schema_id": SCHEMA_ID,
        "artifact_id": ARTIFACT_ID,
        "canonical_role": CANONICAL_ROLE,
        "generated_at": generated_at,
        "status": status,
        "root": ROOT_PREFIX,
        "owner_artifact": OWNER_ARTIFACT,
        "cache_root_policy": {
            **dict(policy),
            "cache_root_source": cache_root_source,
        },
        "hardgates": gates,
        "target_registry": target_registry_rows(),
        "selected_targets": list(selected_targets),
        "summary": {
            "target_count": len(rows),
            "pass_count": sum(1 for row in rows if row.get("status") == "pass"),
            "fail_count": sum(1 for row in rows if row.get("status") == "fail"),
            "unsupported_count": sum(1 for row in rows if row.get("status") == "unsupported"),
        },
        "targets": rows,
        "not_claimed": [
            "This artifact checks byte-level output equivalence for registered cache-backed canonical producers only.",
            "Unsupported canonical producers are not counted as cache-equivalence passes.",
        ],
    }


def validate_owner_payload(payload: Mapping[str, Any]) -> None:
    if payload.get("schema_id") != SCHEMA_ID:
        raise ValueError("cache equivalence schema mismatch")
    if payload.get("artifact_id") != ARTIFACT_ID:
        raise ValueError("cache equivalence artifact id mismatch")
    if payload.get("canonical_role") != CANONICAL_ROLE:
        raise ValueError("cache equivalence canonical role mismatch")
    targets = payload.get("targets")
    if not isinstance(targets, list) or not targets:
        raise ValueError("cache equivalence targets missing")
    gates = payload.get("hardgates")
    if not isinstance(gates, Mapping) or set(gates) != set(CACHE_HARDGATES):
        raise ValueError("cache equivalence hardgates mismatch")
    expected_status = "pass" if all(row.get("status") == "pass" for row in gates.values()) else "fail"
    if payload.get("status") != expected_status:
        raise ValueError("cache equivalence status mismatch")
    for gate_id, row in gates.items():
        if row.get("criterion") != CACHE_HARDGATES[gate_id]:
            raise ValueError(f"cache equivalence criterion mismatch: {gate_id}")
    for row in targets:
        if not isinstance(row, Mapping):
            raise ValueError("cache equivalence target row must be an object")
        if row.get("status") == "pass" and row.get("cache_backed") is not True:
            raise ValueError("unsupported target cannot pass cache equivalence")
        if row.get("cache_backed") is True:
            surfaces = row.get("surfaces")
            if not isinstance(surfaces, Mapping) or set(surfaces) != {"canonical_json", "fingerprint", "raw_metrics", "summary"}:
                raise ValueError("cache equivalence surfaces mismatch")
            if row.get("status") == "pass" and not row.get("cache_observation", {}).get("cache_hit_observed"):
                raise ValueError("passing cache equivalence row lacks cache hit evidence")
            for surface in surfaces.values():
                if surface.get("status") == "pass" and (
                    surface.get("cold", {}).get("algorithm") != "sha256"
                    or surface.get("cache", {}).get("algorithm") != "sha256"
                ):
                    raise ValueError("cache equivalence surface lacks sha256 evidence")


RunTarget = Callable[
    [CacheEquivalenceTarget, Literal["cold", "cache"], str, Path, list[dict[str, Any]]],
    Mapping[str, Any],
]


def run_equivalence_audit(
    *,
    root: Path,
    generated_at: str,
    targets: Sequence[CacheEquivalenceTarget],
    unsupported_targets: Iterable[str] = (),
    cache_root: Path,
    cache_root_source: Literal["temporary", "explicit"],
    run_target: RunTarget,
) -> dict[str, Any]:
    unsupported = list(unsupported_targets)
    policy = cache_root_policy(cache_root)
    target_rows: list[dict[str, Any]] = [unsupported_row(target_id) for target_id in unsupported]
    for target in targets:
        events: list[dict[str, Any]] = []
        cold_result = run_target(target, "cold", generated_at, cache_root, events)
        cold_surfaces = surface_manifests(root, target)
        cache_result = run_target(target, "cache", generated_at, cache_root, events)
        cache_surfaces = surface_manifests(root, target)
        target_rows.append(
            fold_target_row(
                target,
                cold_result=cold_result,
                cache_result=cache_result,
                cold_surfaces=cold_surfaces,
                cache_surfaces=cache_surfaces,
                events=events,
            )
        )
    payload = build_owner_payload(
        generated_at=generated_at,
        target_rows=target_rows,
        policy=policy,
        cache_root_source=cache_root_source,
        selected_targets=[target.target_id for target in targets] + unsupported,
    )
    validate_owner_payload(payload)
    return payload


def write_owner_payload(path: Path, payload: Mapping[str, Any]) -> None:
    validate_owner_payload(payload)
    path.parent.mkdir(parents=True, exist_ok=True)
    temp = path.with_suffix(path.suffix + ".tmp")
    temp.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    temp.replace(path)
