"""DGT training replay run-local projection."""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
import statistics
from typing import Any, Iterable, Mapping, Sequence

from bedc_quality_lab.discovery_compiler.capsule import CLAIM_CAPSULE_RUN_LOCAL_SCHEMA_ID
from bedc_quality_lab.discovery_compiler.pointers import pointer_value, resolve_artifact_pointer


SCHEMA_ID = "bedc-quality-lab:discovery-gated-transformer-training-replay"
ARTIFACT_ID = "bedc-quality-lab:discovery-gated-transformer-training-replay"
PRODUCER = "scripts/run_discovery_gated_transformer_training.py"
PROJECTOR = "bedc_quality_lab.discovery_gated_transformer_training"
DEFAULT_RUN_ID = "training-replay"
RUN_ROOT = "reports/runs/discovery_gated_transformer/training-replay/training_replay"
TRAINING_REPLAY_ARTIFACT = f"{RUN_ROOT}/training_replay.json"
RAW_METRICS_ARTIFACT = f"{RUN_ROOT}/raw_metrics.jsonl"
COMPUTE_LEDGER_ARTIFACT = f"{RUN_ROOT}/compute_ledger.json"
CLAIM_CAPSULE_ARTIFACT = f"{RUN_ROOT}/claim_capsule.json"
EVIDENCE_ENVELOPE_ARTIFACT = f"{RUN_ROOT}/evidence_envelope.json"
REPORT_ARTIFACT = f"{RUN_ROOT}/report.md"
SUMMARY_ARTIFACT = f"{RUN_ROOT}/summary.json"
ARMS = (
    "task_only",
    "lat",
    "cga",
    "drt",
    "dgt_full",
    "dgt_matched_random",
    "dgt_no_discovery_loss",
    "dgt_no_ledger_loss",
    "dgt_no_certificate_loss",
)
CONTROL_FAMILIES = {
    "task_only": "baseline",
    "lat": "component",
    "cga": "component",
    "drt": "component",
    "dgt_full": "candidate",
    "dgt_matched_random": "structural_random_control",
    "dgt_no_discovery_loss": "loss_ablation",
    "dgt_no_ledger_loss": "loss_ablation",
    "dgt_no_certificate_loss": "loss_ablation",
}
METRIC_KEYS = ("uer", "false_ledger_rate", "benefit", "debt", "classifier_shift")
NOT_CLAIMED = (
    "broad architecture superiority",
    "production deployment readiness",
    "full benchmark closure",
    "downstream terminal claim publication",
)


def artifact_pointer(pointer: str, *, artifact: str = TRAINING_REPLAY_ARTIFACT) -> str:
    return f"{artifact}:{pointer}"


def public_training_replay_ref(payload: Mapping[str, Any]) -> dict[str, str]:
    artifact = str(payload.get("run_artifacts", {}).get("training_replay", TRAINING_REPLAY_ARTIFACT))
    return {"artifact": artifact, "pointer": "$"}


def _status(value: bool) -> str:
    return "pass" if value else "fail"


def _mean(values: Iterable[float]) -> float:
    return round(float(statistics.fmean(float(value) for value in values)), 6)


def _finite_number(value: Any) -> float | None:
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        return None
    result = float(value)
    if result != result or result in (float("inf"), float("-inf")):
        return None
    return result


def _canonical_json(value: Any) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True)


def _digest(value: Any) -> str:
    return hashlib.sha256(_canonical_json(value).encode("utf-8")).hexdigest()


def _recursive_has_key(value: Any, forbidden: set[str]) -> bool:
    if isinstance(value, Mapping):
        return any(key in forbidden or _recursive_has_key(item, forbidden) for key, item in value.items())
    if isinstance(value, (list, tuple)):
        return any(_recursive_has_key(item, forbidden) for item in value)
    return False


def _raw_metric_records(records: Sequence[Mapping[str, Any]]) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for index, row in enumerate(records):
        arm = str(row.get("arm_id", row.get("arm", "")))
        seed = int(row.get("seed", 0))
        if arm not in ARMS:
            raise ValueError(f"unknown DGT training arm: {arm}")
        metrics = {
            key: _finite_number(row.get(key))
            for key in METRIC_KEYS
        }
        if any(value is None for value in metrics.values()):
            raise ValueError(f"DGT training row has missing metric: {arm}/{seed}")
        rows.append(
            {
                "row_id": f"{arm}:{seed}",
                "arm_id": arm,
                "seed": seed,
                "control_family": CONTROL_FAMILIES[arm],
                "metrics": {key: round(float(value), 6) for key, value in metrics.items()},
                "config_pointer": f"$.config.arm_configs.{arm}",
                "cost_pointer": f"$.compute_ledger.rows[{index}]",
                "ledger_pointer": f"$.compute_ledger.rows[{index}]",
                "evidence_pointer": f"$.records[{index}].metrics",
            }
        )
    return sorted(rows, key=lambda item: (int(item["seed"]), ARMS.index(str(item["arm_id"]))))


def _group_by_arm(records: Sequence[Mapping[str, Any]]) -> dict[str, list[Mapping[str, Any]]]:
    grouped = {arm: [] for arm in ARMS}
    for row in records:
        grouped[str(row["arm_id"])].append(row)
    return grouped


def _metric_means(records: Sequence[Mapping[str, Any]]) -> dict[str, dict[str, float]]:
    grouped = _group_by_arm(records)
    return {
        arm: {
            key: _mean(float(row["metrics"][key]) for row in rows)
            for key in METRIC_KEYS
        }
        for arm, rows in grouped.items()
        if rows
    }


def _normalize_compute_ledger(
    records: Sequence[Mapping[str, Any]],
    compute_ledger: Mapping[str, Any],
) -> dict[str, Any]:
    rows_by_key = {
        (str(row.get("arm_id", row.get("arm", ""))), int(row.get("seed", 0))): dict(row)
        for row in compute_ledger.get("rows", [])
        if isinstance(row, Mapping)
    }
    normalized_rows: list[dict[str, Any]] = []
    for index, row in enumerate(records):
        key = (str(row["arm_id"]), int(row["seed"]))
        ledger = rows_by_key.get(key, {})
        normalized_rows.append(
            {
                "arm_id": key[0],
                "seed": key[1],
                "train_steps": int(ledger.get("train_steps", 24)),
                "device": str(ledger.get("device", "deterministic-cpu")),
                "dtype": str(ledger.get("dtype", "float32")),
                "cost_units": round(float(ledger.get("cost_units", 1.0)), 6),
                "cost_protocol_pointer": "$.compute_ledger.cost_protocol",
                "raw_metric_pointer": f"$.records[{index}]",
            }
        )
    return {
        "schema_id": "bedc-quality-lab:dgt-training-compute-ledger",
        "cost_protocol": dict(compute_ledger.get("cost_protocol", {"name": "local deterministic replay"})),
        "rows": normalized_rows,
    }


def _sidecar_pointer_payload(run_artifacts: Mapping[str, str]) -> dict[str, str]:
    return {
        "claim_capsule": f"{run_artifacts['claim_capsule']}:$",
        "evidence_envelope": f"{run_artifacts['evidence_envelope']}:$",
        "cost_protocol": f"{run_artifacts['compute_ledger']}:$.cost_protocol",
        "not_claimed": f"{run_artifacts['training_replay']}:$.not_claimed",
    }


@dataclass(frozen=True)
class DiscoveryGatedTransformerTrainingReplay:
    config: Mapping[str, Any]
    records: Sequence[Mapping[str, Any]]
    compute_ledger: Mapping[str, Any]
    generated_at: str
    run_artifacts: Mapping[str, str]

    def build(self) -> dict[str, Any]:
        normalized_records = _raw_metric_records(self.records)
        ledger = _normalize_compute_ledger(normalized_records, self.compute_ledger)
        config = dict(self.config)
        config.setdefault("seeds", sorted({int(row["seed"]) for row in normalized_records}))
        config.setdefault("arms", list(ARMS))
        config.setdefault(
            "arm_configs",
            {arm: {"arm_id": arm, "control_family": CONTROL_FAMILIES[arm]} for arm in ARMS},
        )
        summary = {
            "metric_means": _metric_means(normalized_records),
            "control_families": dict(CONTROL_FAMILIES),
            "record_count": len(normalized_records),
            "seed_count": len(config["seeds"]),
            "arm_count": len(ARMS),
        }
        replay_digest = _digest(
            {
                "config": config,
                "records": normalized_records,
                "compute_ledger": ledger,
            }
        )
        payload = {
            "schema_id": SCHEMA_ID,
            "artifact_id": ARTIFACT_ID,
            "generated_at": self.generated_at,
            "producer": PRODUCER,
            "projector": PROJECTOR,
            "run_id": str(config.get("run_id", DEFAULT_RUN_ID)),
            "status": "present-but-fail-closed",
            "run_artifacts": dict(self.run_artifacts),
            "source_artifacts": {
                "raw_metrics": self.run_artifacts["raw_metrics"],
                "compute_ledger": self.run_artifacts["compute_ledger"],
                "claim_capsule": self.run_artifacts["claim_capsule"],
                "evidence_envelope": self.run_artifacts["evidence_envelope"],
                "producer_sources": [
                    "bedc_quality_lab/discovery_gated_transformer_training.py",
                    "scripts/run_discovery_gated_transformer_training.py",
                ],
            },
            "config": config,
            "records": normalized_records,
            "compute_ledger": ledger,
            "summary": summary,
            "replay_digest": replay_digest,
            "sidecar_pointers": _sidecar_pointer_payload(self.run_artifacts),
            "not_claimed": list(NOT_CLAIMED),
        }
        payload["hardgates"] = evaluate_training_hardgates(payload)
        payload["overall_state"] = (
            "pass"
            if all(row["status"] == "pass" for row in payload["hardgates"].values())
            else "present-but-fail-closed"
        )
        if _recursive_has_key(payload, {"terminal_verdict", "host.env"}):
            raise ValueError("DGT training replay emitted a forbidden key")
        return payload


def build_replay(
    config: Mapping[str, Any],
    records: Sequence[Mapping[str, Any]],
    compute_ledger: Mapping[str, Any],
    generated_at: str,
    run_artifacts: Mapping[str, str] | None = None,
) -> dict[str, Any]:
    artifacts = run_artifacts or {
        "training_replay": TRAINING_REPLAY_ARTIFACT,
        "raw_metrics": RAW_METRICS_ARTIFACT,
        "compute_ledger": COMPUTE_LEDGER_ARTIFACT,
        "claim_capsule": CLAIM_CAPSULE_ARTIFACT,
        "evidence_envelope": EVIDENCE_ENVELOPE_ARTIFACT,
        "report": REPORT_ARTIFACT,
        "summary": SUMMARY_ARTIFACT,
    }
    return DiscoveryGatedTransformerTrainingReplay(
        config=config,
        records=records,
        compute_ledger=compute_ledger,
        generated_at=generated_at,
        run_artifacts=artifacts,
    ).build()


def _local_pointer_resolves(payload: Mapping[str, Any], pointer: str) -> bool:
    if pointer == "$":
        return True
    return pointer_value(payload, pointer) is not None


def _gate(status: bool, *, evidence_pointer: str, **extra: Any) -> dict[str, Any]:
    row = {"status": _status(status), "evidence_pointer": evidence_pointer}
    row.update(extra)
    return row


def evaluate_training_hardgates(payload: Mapping[str, Any]) -> dict[str, Any]:
    records = list(payload.get("records", []))
    ledger = payload.get("compute_ledger", {})
    config = payload.get("config", {})
    means = payload.get("summary", {}).get("metric_means", {})
    seeds = {int(seed) for seed in config.get("seeds", [])}
    by_arm = _group_by_arm(records)
    expected_pairs = {(arm, seed) for arm in ARMS for seed in seeds}
    actual_pairs = {(str(row.get("arm_id")), int(row.get("seed", 0))) for row in records}
    ledger_pairs = {
        (str(row.get("arm_id")), int(row.get("seed", 0)))
        for row in ledger.get("rows", [])
        if isinstance(row, Mapping)
    }
    digest = _digest(
        {
            "config": config,
            "records": records,
            "compute_ledger": ledger,
        }
    )
    full = means.get("dgt_full", {})
    task = means.get("task_only", {})
    lat = means.get("lat", {})
    cga = means.get("cga", {})
    drt = means.get("drt", {})
    matched = means.get("dgt_matched_random", {})
    sidecars = payload.get("sidecar_pointers", {})
    return {
        "TRAIN-HG1": _gate(
            digest == payload.get("replay_digest"),
            evidence_pointer="$.replay_digest",
            recomputed_digest=digest,
        ),
        "TRAIN-HG2": _gate(
            ledger_pairs == expected_pairs
            and all(
                isinstance(row, Mapping)
                and _local_pointer_resolves(payload, str(row.get("cost_protocol_pointer")))
                and _local_pointer_resolves(payload, str(row.get("raw_metric_pointer")))
                for row in ledger.get("rows", [])
            ),
            evidence_pointer="$.compute_ledger.rows",
            expected_row_count=len(expected_pairs),
            row_count=len(ledger.get("rows", [])),
        ),
        "TRAIN-HG3": _gate(
            actual_pairs == expected_pairs
            and all(
                _local_pointer_resolves(payload, str(row.get("config_pointer")))
                and _local_pointer_resolves(payload, str(row.get("cost_pointer")))
                and _local_pointer_resolves(payload, str(row.get("ledger_pointer")))
                for row in records
            ),
            evidence_pointer="$.records",
            expected_pairs=len(expected_pairs),
            actual_pairs=len(actual_pairs),
        ),
        "TRAIN-HG4": _gate(
            CONTROL_FAMILIES["dgt_matched_random"] == "structural_random_control"
            and by_arm["dgt_matched_random"][0]["control_family"] == "structural_random_control"
            and {
                row["control_family"]
                for arm in ("dgt_no_discovery_loss", "dgt_no_ledger_loss", "dgt_no_certificate_loss")
                for row in by_arm[arm]
            }
            == {"loss_ablation"},
            evidence_pointer="$.summary.control_families",
        ),
        "TRAIN-HG5": _gate(
            all(_local_pointer_resolves(payload, f"$.summary.metric_means.{arm}.uer") for arm in ("dgt_full", "task_only", "lat", "cga", "drt", "dgt_matched_random"))
            and float(full.get("uer", 1.0)) < min(float(task.get("uer", 1.0)), float(lat.get("uer", 1.0)), float(cga.get("uer", 1.0)), float(drt.get("uer", 1.0)), float(matched.get("uer", 1.0))),
            evidence_pointer="$.summary.metric_means.dgt_full.uer",
        ),
        "TRAIN-HG6": _gate(
            float(full.get("false_ledger_rate", 1.0)) <= float(task.get("false_ledger_rate", -1.0))
            and float(full.get("false_ledger_rate", 1.0)) <= float(matched.get("false_ledger_rate", -1.0)),
            evidence_pointer="$.summary.metric_means.dgt_full.false_ledger_rate",
        ),
        "TRAIN-HG7": _gate(
            float(full.get("benefit", -1.0)) >= float(task.get("benefit", 2.0))
            and float(full.get("benefit", -1.0)) >= float(matched.get("benefit", 2.0))
            and float(full.get("debt", 2.0)) < float(task.get("debt", -1.0))
            and float(full.get("debt", 2.0)) < float(matched.get("debt", -1.0)),
            evidence_pointer="$.summary.metric_means.dgt_full.benefit",
            debt_pointer="$.summary.metric_means.dgt_full.debt",
        ),
        "TRAIN-HG8": _gate(
            _local_pointer_resolves(payload, "$.summary.metric_means.dgt_full.classifier_shift")
            and float(full.get("classifier_shift", 0.0)) > 0.0,
            evidence_pointer="$.summary.metric_means.dgt_full.classifier_shift",
        ),
        "TRAIN-HG9": _gate(
            all(isinstance(sidecars.get(key), str) for key in ("claim_capsule", "evidence_envelope", "cost_protocol", "not_claimed")),
            evidence_pointer="$.sidecar_pointers",
            claim_capsule_pointer=sidecars.get("claim_capsule"),
            evidence_envelope_pointer=sidecars.get("evidence_envelope"),
            cost_protocol_pointer=sidecars.get("cost_protocol"),
            not_claimed_pointer=sidecars.get("not_claimed"),
        ),
        "TRAIN-HG10": _gate(
            not _recursive_has_key(payload, {"terminal_verdict", "host.env"})
            and public_training_replay_ref(payload) == {
                "artifact": payload["run_artifacts"]["training_replay"],
                "pointer": "$",
            },
            evidence_pointer="$.run_artifacts.training_replay",
            canonical_pointer=public_training_replay_ref(payload),
        ),
    }


def claim_capsule_payload(payload: Mapping[str, Any]) -> dict[str, Any]:
    failed = next((gate for gate, row in payload["hardgates"].items() if row["status"] != "pass"), None)
    return {
        "schema_id": CLAIM_CAPSULE_RUN_LOCAL_SCHEMA_ID,
        "artifact_id": f"{ARTIFACT_ID}:claim-capsule",
        "run_id": payload["run_id"],
        "generated_at": payload["generated_at"],
        "producer": PROJECTOR,
        "claim_status": "training-replay-recorded" if failed is None else "failed",
        "failed_gate": failed,
        "source_artifacts": {
            "training_replay": payload["run_artifacts"]["training_replay"],
            "raw_metrics": payload["run_artifacts"]["raw_metrics"],
            "compute_ledger": payload["run_artifacts"]["compute_ledger"],
        },
        "not_claimed": list(NOT_CLAIMED),
        "hardgate_pointers": {
            gate: f"{payload['run_artifacts']['training_replay']}:$.hardgates.{gate}"
            for gate in payload["hardgates"]
        },
    }


def evidence_envelope_payload(payload: Mapping[str, Any]) -> dict[str, Any]:
    return {
        "schema_id": "bedc-quality-lab:dgt-training-evidence-envelope",
        "artifact_id": f"{ARTIFACT_ID}:evidence-envelope",
        "run_id": payload["run_id"],
        "generated_at": payload["generated_at"],
        "evidence_owner": payload["run_artifacts"]["training_replay"],
        "metric_pointers": {
            key: f"{payload['run_artifacts']['training_replay']}:$.summary.metric_means.dgt_full.{key}"
            for key in METRIC_KEYS
        },
        "not_claimed_pointer": f"{payload['run_artifacts']['training_replay']}:$.not_claimed",
    }


def render_training_replay_markdown(payload: Mapping[str, Any]) -> str:
    lines = [
        "# Discovery-Gated Transformer Training Replay",
        "",
        f"- run_id: `{payload['run_id']}`",
        f"- schema_id: `{payload['schema_id']}`",
        f"- replay digest: `{payload['replay_digest']}`",
        f"- overall state: `{payload['overall_state']}`",
        "",
        "## TRAIN-HG",
        "",
    ]
    for gate, row in payload["hardgates"].items():
        lines.append(f"- `{gate}`: `{row['status']}` at `{row['evidence_pointer']}`")
    lines.extend(["", "## Run Artifacts", ""])
    for key, artifact in payload["run_artifacts"].items():
        lines.append(f"- {key}: `{artifact}`")
    return "\n".join(lines) + "\n"


def summary_payload(payload: Mapping[str, Any]) -> dict[str, Any]:
    failed = next((gate for gate, row in payload["hardgates"].items() if row["status"] != "pass"), None)
    return {
        "schema_id": "bedc-quality-lab:dgt-training-replay-summary",
        "artifact_id": f"{ARTIFACT_ID}:summary",
        "run_id": payload["run_id"],
        "generated_at": payload["generated_at"],
        "status": payload["overall_state"],
        "training_replay_ref": public_training_replay_ref(payload),
        "hardgate_pointer": f"{payload['run_artifacts']['training_replay']}:$.hardgates",
        "failed_gate_pointer": None
        if failed is None
        else f"{payload['run_artifacts']['training_replay']}:$.hardgates.{failed}",
        "claim_capsule_ref": {"artifact": payload["run_artifacts"]["claim_capsule"], "pointer": "$"},
        "evidence_envelope_ref": {"artifact": payload["run_artifacts"]["evidence_envelope"], "pointer": "$"},
        "cost_protocol_ref": {"artifact": payload["run_artifacts"]["compute_ledger"], "pointer": "$.cost_protocol"},
        "not_claimed_ref": {"artifact": payload["run_artifacts"]["training_replay"], "pointer": "$.not_claimed"},
    }


def resolve_training_pointer(root: Path, cell: str) -> Any:
    if ":$" in cell:
        return resolve_artifact_pointer(root, cell)
    return None
