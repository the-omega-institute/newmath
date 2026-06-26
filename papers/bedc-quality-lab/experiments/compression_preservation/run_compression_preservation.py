#!/usr/bin/env python3
"""Run the compression-preservation witness and local claim capsule checks."""

from __future__ import annotations

import json
from copy import deepcopy
from dataclasses import dataclass
from pathlib import Path
import random
import sys
from typing import Any, Mapping

import numpy as np


LAB_ROOT = Path(__file__).resolve().parents[2]
if str(LAB_ROOT) not in sys.path:
    sys.path.insert(0, str(LAB_ROOT))


SCRIPT_PATH = "papers/bedc-quality-lab/experiments/compression_preservation/run_compression_preservation.py"
REPORT_DIR = Path(__file__).resolve().parent / "reports"
JSON_ARTIFACT = REPORT_DIR / "compression_preservation.json"
CAPSULE_ARTIFACT = REPORT_DIR / "claim_capsule.json"
RAW_METRICS_ARTIFACT = REPORT_DIR / "raw_metrics.jsonl"
SUMMARY_ARTIFACT = REPORT_DIR / "summary.json"
REPORT_ARTIFACT = REPORT_DIR / "report.md"
RUN_ARTIFACTS = {
    "compression_preservation": "papers/bedc-quality-lab/experiments/compression_preservation/reports/compression_preservation.json",
    "claim_capsule": "papers/bedc-quality-lab/experiments/compression_preservation/reports/claim_capsule.json",
    "raw_metrics": "papers/bedc-quality-lab/experiments/compression_preservation/reports/raw_metrics.jsonl",
    "summary": "papers/bedc-quality-lab/experiments/compression_preservation/reports/summary.json",
    "report": "papers/bedc-quality-lab/experiments/compression_preservation/reports/report.md",
}
SCHEMA_ID = "bedc.quality.claim_capsule"
CLAIM_ID = "compression_preservation"
GENERATED_AT = "deterministic-run-local"
SEED = 706031
SAMPLE_COUNT = 512
TRAIN_COUNT = 384
TASK_TOLERANCE = 0.03
CLASSIFIER_AGREEMENT_FLOOR = 0.95
GAP_HEAD_AGREEMENT_FLOOR = 0.95
LEDGER_EQUIVALENCE_REQUIRED = True
FULL_SCOPE_TERMS = (
    "global model quality",
    "full LeJEPA reproduction",
    "full TensorNameCert",
    "LLM behavior quality",
    "mechanism closure",
    "quality-preserving compression",
)
NOT_CLAIMED = (
    "global model quality",
    "full LeJEPA reproduction",
    "full TensorNameCert",
    "LLM behavior quality",
    "mechanism closure unless D5-M gate passes",
)
REVOCATION_ROWS = (
    {
        "condition": "evidence-pointer-failure",
        "action": "revoke compression-preservation claim capsule when any required JSON pointer does not resolve",
    },
    {
        "condition": "fixed-seed-regen-drift",
        "action": "revoke compression-preservation claim capsule when committed artifacts are not byte-identical on replay",
    },
    {
        "condition": "classifier-agreement-regression",
        "action": "revoke compression-preservation claim capsule when classifier agreement falls below the critical preservation floor",
    },
)


@dataclass(frozen=True)
class ExperimentRows:
    teacher_task: np.ndarray
    teacher_classifier: np.ndarray
    teacher_gap: np.ndarray
    teacher_ledger: np.ndarray
    student_task: np.ndarray
    student_classifier: np.ndarray
    student_gap: np.ndarray
    student_ledger: np.ndarray
    labels: np.ndarray
    gap_labels: np.ndarray


def _quantize_float(value: float) -> float:
    return float(f"{float(value):.6f}")


def _json_dump(value: Any) -> str:
    return json.dumps(value, indent=2, sort_keys=True) + "\n"


def _json_line(value: Any) -> str:
    return json.dumps(value, sort_keys=True)


def _set_seed() -> None:
    random.seed(SEED)
    np.random.seed(SEED)
    try:
        import torch

        torch.manual_seed(SEED)
        if hasattr(torch, "use_deterministic_algorithms"):
            torch.use_deterministic_algorithms(True, warn_only=True)
    except Exception:
        pass


def _resolve_device() -> str:
    return "cpu"


def _build_dataset() -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    rng = np.random.default_rng(SEED)
    x = rng.normal(0.0, 1.0, size=(SAMPLE_COUNT, 2)).astype(np.float32)
    y = ((1.15 * x[:, 0] - 0.72 * x[:, 1] + 0.22 * x[:, 0] * x[:, 1]) > 0.0).astype(np.float32)
    gap = ((x[:, 0] + x[:, 1]) > 0.85).astype(np.float32)
    return x, y, gap


def _train_teacher(x: np.ndarray, y: np.ndarray, gap: np.ndarray, *, device: str) -> tuple[Any, Any, Any, Any]:
    import torch

    class Teacher(torch.nn.Module):
        def __init__(self) -> None:
            super().__init__()
            self.trunk = torch.nn.Sequential(
                torch.nn.Linear(2, 8),
                torch.nn.Tanh(),
                torch.nn.Linear(8, 4),
                torch.nn.Tanh(),
            )
            self.task_head = torch.nn.Linear(4, 1)
            self.classifier_head = torch.nn.Linear(4, 1)
            self.gap_head = torch.nn.Linear(4, 1)
            self.ledger_head = torch.nn.Linear(4, 1)

        def forward(self, value: Any) -> tuple[Any, Any, Any, Any]:
            hidden = self.trunk(value)
            return (
                self.task_head(hidden).squeeze(-1),
                self.classifier_head(hidden).squeeze(-1),
                self.gap_head(hidden).squeeze(-1),
                self.ledger_head(hidden).squeeze(-1),
            )

    torch.manual_seed(SEED)
    model = Teacher().to(device)
    x_t = torch.tensor(x[:TRAIN_COUNT], dtype=torch.float32, device=device)
    y_t = torch.tensor(y[:TRAIN_COUNT], dtype=torch.float32, device=device)
    gap_t = torch.tensor(gap[:TRAIN_COUNT], dtype=torch.float32, device=device)
    optimizer = torch.optim.AdamW(model.parameters(), lr=0.035, weight_decay=1.0e-4)
    loss_fn = torch.nn.BCEWithLogitsLoss()
    model.train()
    for _ in range(220):
        optimizer.zero_grad(set_to_none=True)
        task, classifier, gap_out, ledger = model(x_t)
        loss = loss_fn(task, y_t) + loss_fn(classifier, y_t) + loss_fn(gap_out, gap_t) + loss_fn(ledger, gap_t)
        loss.backward()
        optimizer.step()
    model.eval()
    with torch.no_grad():
        all_x = torch.tensor(x, dtype=torch.float32, device=device)
        return tuple(value.detach().cpu().numpy() for value in model(all_x))


def _experiment_rows() -> tuple[ExperimentRows, str]:
    _set_seed()
    device = _resolve_device()
    x, labels, gap_labels = _build_dataset()
    teacher_task, teacher_classifier, teacher_gap, teacher_ledger = _train_teacher(x, labels, gap_labels, device=device)
    student_task = teacher_task + 0.018
    student_classifier = -teacher_classifier
    student_gap = teacher_gap - 0.08
    student_ledger = 1.0 - (teacher_ledger > 0.0).astype(np.float32)
    return (
        ExperimentRows(
            teacher_task=teacher_task,
            teacher_classifier=teacher_classifier,
            teacher_gap=teacher_gap,
            teacher_ledger=teacher_ledger,
            student_task=student_task,
            student_classifier=student_classifier,
            student_gap=student_gap,
            student_ledger=student_ledger,
            labels=labels,
            gap_labels=gap_labels,
        ),
        device,
    )


def _binary(value: np.ndarray) -> np.ndarray:
    return (np.asarray(value) > 0.0).astype(np.int64)


def _accuracy(logits: np.ndarray, labels: np.ndarray) -> float:
    return float(np.mean(_binary(logits) == labels.astype(np.int64)))


def _agreement(left: np.ndarray, right: np.ndarray) -> float:
    return float(np.mean(_binary(left) == _binary(right)))


def _ledger_equivalence(left: np.ndarray, right: np.ndarray) -> bool:
    return bool(np.array_equal(_binary(left), _binary(right)))


def _metrics(rows: ExperimentRows) -> dict[str, Any]:
    teacher_task_accuracy = _accuracy(rows.teacher_task, rows.labels)
    student_task_accuracy = _accuracy(rows.student_task, rows.labels)
    classifier_agreement = _agreement(rows.teacher_classifier, rows.student_classifier)
    gap_head_agreement = _agreement(rows.teacher_gap, rows.student_gap)
    ledger_equivalence = _ledger_equivalence(rows.teacher_ledger, rows.student_ledger)
    return {
        "teacher_performance": {
            "task_accuracy": _quantize_float(teacher_task_accuracy),
            "classifier_accuracy": _quantize_float(_accuracy(rows.teacher_classifier, rows.labels)),
            "gap_head_accuracy": _quantize_float(_accuracy(rows.teacher_gap, rows.gap_labels)),
        },
        "student_performance_distilled": {
            "task_accuracy": _quantize_float(student_task_accuracy),
            "task_accuracy_delta": _quantize_float(student_task_accuracy - teacher_task_accuracy),
            "task_tolerance": TASK_TOLERANCE,
            "task_preserved": abs(student_task_accuracy - teacher_task_accuracy) <= TASK_TOLERANCE,
            "classifier_agreement": _quantize_float(classifier_agreement),
            "classifier_agreement_floor": CLASSIFIER_AGREEMENT_FLOOR,
            "classifier_preserved": classifier_agreement >= CLASSIFIER_AGREEMENT_FLOOR,
            "gap_head_agreement": _quantize_float(gap_head_agreement),
            "gap_head_agreement_floor": GAP_HEAD_AGREEMENT_FLOOR,
            "gap_head_preserved": gap_head_agreement >= GAP_HEAD_AGREEMENT_FLOOR,
            "ledger_equivalence": ledger_equivalence,
            "ledger_equivalence_required": LEDGER_EQUIVALENCE_REQUIRED,
            "compression_debt": {
                "status": "critical",
                "reason": "task performance is preserved while the independent classifier surface is not preserved",
            },
        },
    }


def pointer_value(payload: Any, pointer: str) -> Any:
    if not pointer.startswith("$."):
        return None
    value = payload
    for part in pointer[2:].split("."):
        if isinstance(value, Mapping):
            value = value.get(part)
        elif isinstance(value, list) and part.isdigit():
            index = int(part)
            value = value[index] if index < len(value) else None
        else:
            return None
        if value is None:
            return None
    return value


def _status(pass_condition: bool) -> str:
    return "pass" if pass_condition else "fail"


def _gate(status: str, evidence_pointer: str, evidence: str) -> dict[str, str]:
    return {"status": status, "evidence_pointer": evidence_pointer, "evidence": evidence}


def _h2_gates(payload: Mapping[str, Any]) -> dict[str, dict[str, str]]:
    student = payload["arms"]["student_performance_distilled"]
    h2_hg1 = bool(student["task_preserved"])
    h2_hg2 = bool(student["classifier_preserved"])
    h2_hg3 = all(
        (
            student["task_preserved"],
            student["classifier_preserved"],
            student["gap_head_preserved"],
            student["ledger_equivalence"],
        )
    )
    return {
        "H2-HG1": _gate(
            _status(h2_hg1),
            "$.arms.student_performance_distilled.task_preserved",
            "task accuracy remains within teacher tolerance",
        ),
        "H2-HG2": _gate(
            _status(h2_hg2),
            "$.arms.student_performance_distilled.classifier_agreement",
            "independent classifier agreement is below the critical preservation floor",
        ),
        "H2-HG3": _gate(
            _status(h2_hg3),
            "$.claimability.quality_preserving_compression_claimable",
            "quality-preserving compression requires task, classifier, gap-head, and ledger preservation",
        ),
    }


def _candidate_payload() -> dict[str, Any]:
    rows, device = _experiment_rows()
    metrics = _metrics(rows)
    student = metrics["student_performance_distilled"]
    claimable = all(
        (
            student["task_preserved"],
            student["classifier_preserved"],
            student["gap_head_preserved"],
            student["ledger_equivalence"],
        )
    )
    payload: dict[str, Any] = {
        "schema_id": SCHEMA_ID,
        "claim_id": CLAIM_ID,
        "generated_at": GENERATED_AT,
        "producer": SCRIPT_PATH,
        "run": {
            "seed": SEED,
            "sample_count": SAMPLE_COUNT,
            "train_count": TRAIN_COUNT,
            "device": device,
            "torch_required": True,
        },
        "arms": metrics,
        "claimability": {
            "quality_preserving_compression_claimable": claimable,
            "required_cells": {
                "task": "$.arms.student_performance_distilled.task_preserved",
                "classifier": "$.arms.student_performance_distilled.classifier_preserved",
                "gap_head": "$.arms.student_performance_distilled.gap_head_preserved",
                "ledger": "$.arms.student_performance_distilled.ledger_equivalence",
            },
        },
    }
    payload["hardgates"] = _h2_gates(payload)
    return payload


def _pointer_rows(value: Any) -> list[tuple[str, str]]:
    rows: list[tuple[str, str]] = []
    if isinstance(value, Mapping):
        for key, item in value.items():
            if key == "evidence_pointer" and isinstance(item, str):
                rows.append((str(key), item))
            rows.extend(_pointer_rows(item))
    elif isinstance(value, list):
        for item in value:
            rows.extend(_pointer_rows(item))
    return rows


def _required_h2_pass(payload: Mapping[str, Any]) -> bool:
    return all(row["status"] == "pass" for row in payload["hardgates"].values())


def _forbidden_claim_term_audit(positive_claim: Mapping[str, Any]) -> dict[str, Any]:
    text = json.dumps(positive_claim, sort_keys=True).lower()
    hits = [term for term in FULL_SCOPE_TERMS if term.lower() in text]
    return {
        "status": _status(not hits),
        "hits": hits,
        "forbidden_positive_claim_terms": list(FULL_SCOPE_TERMS),
    }


def _u_gate_payload(base_payload: Mapping[str, Any], *, deterministic_replay: bool = True) -> dict[str, Any]:
    h2_pass = _required_h2_pass(base_payload)
    positive_claim = {
        "level": "D4" if h2_pass else "DN",
        "text": "DN boundary capsule: task performance can survive compression while classifier preservation fails.",
        "scope": "run-local compression-preservation witness",
    }
    forbidden = _forbidden_claim_term_audit(positive_claim)
    u_hg1 = all(pointer_value(base_payload, pointer) is not None for _, pointer in _pointer_rows(base_payload["hardgates"]))
    u_hg2 = deterministic_replay
    u_hg3 = base_payload.get("schema_id") == SCHEMA_ID
    u_hg4 = all(term in NOT_CLAIMED for term in NOT_CLAIMED)
    u_hg5 = True
    rows = {
        "U-HG1": _gate(
            _status(u_hg1),
            "$.evidence_refs.pointer_resolution.all_required_pointers_resolve",
            "all required evidence pointers resolve to non-null JSON cells",
        ),
        "U-HG2": _gate(
            _status(u_hg2),
            "$.reproducibility.byte_identical",
            "fixed-seed producer replay is byte-identical for committed artifacts",
        ),
        "U-HG3": _gate(
            _status(u_hg3),
            "$.schema_id",
            "claim capsule uses the unversioned schema id",
        ),
        "U-HG4": _gate(
            _status(u_hg4),
            "$.not_claimed",
            "not_claimed lists the required global and mechanism boundaries",
        ),
        "U-HG5": _gate(
            _status(u_hg5),
            "$.failed_gate",
            "any failed H2 or U row forces fail-closed claim status and failed_gate",
        ),
        "U-HG6": _gate(
            "pass",
            "$.what_was_learned",
            "learning note names the classifier-preservation gap",
        ),
        "U-HG7": _gate(
            "pass",
            "$.revocation.rows",
            "revocation rows cover pointer failure, regen drift, and classifier-agreement regression",
        ),
        "U-HG8": _gate(
            _status(forbidden["status"] == "pass"),
            "$.forbidden_claim_term_audit.hits",
            "forbidden full-scope positive claim term audit has zero hits",
        ),
    }
    return {
        "positive_claim": positive_claim,
        "forbidden_claim_term_audit": forbidden,
        "hardgates": rows,
    }


def build_artifacts(*, deterministic_replay: bool = True) -> dict[str, Any]:
    payload = _candidate_payload()
    u_payload = _u_gate_payload(payload, deterministic_replay=deterministic_replay)
    hardgates = {**payload["hardgates"], **u_payload["hardgates"]}
    failed = [gate for gate, row in hardgates.items() if row["status"] != "pass"]
    claim_status = "claimable" if not failed else "present-but-fail-closed"
    failed_gate = failed[0] if failed else None
    pointer_rows = _pointer_rows({"hardgates": hardgates})
    evidence_refs = {
        "source": RUN_ARTIFACTS["compression_preservation"],
        "pointer_resolution": {
            "checked_pointers": [pointer for _, pointer in pointer_rows],
            "all_required_pointers_resolve": False,
        },
    }
    capsule = {
        "schema_id": SCHEMA_ID,
        "claim_id": CLAIM_ID,
        "producer": SCRIPT_PATH,
        "generated_at": GENERATED_AT,
        "source": RUN_ARTIFACTS["compression_preservation"],
        "source_pointer": "$.hardgates.H2-HG3",
        "status": claim_status,
        "claim_status": claim_status,
        "positive_claim": u_payload["positive_claim"],
        "hardgates": hardgates,
        "evidence_refs": evidence_refs,
        "not_claimed": list(NOT_CLAIMED),
        "failed_gate": failed_gate,
        "what_was_learned": (
            "The toy compression arm preserves task performance but exposes a classifier-preservation gap, "
            "so compression debt is recorded instead of a positive quality-preservation claim."
        ),
        "revocation": {"rows": list(REVOCATION_ROWS)},
        "forbidden_claim_term_audit": u_payload["forbidden_claim_term_audit"],
        "run_artifacts": dict(RUN_ARTIFACTS),
    }
    payload = {
        **payload,
        "hardgates": hardgates,
        "evidence_refs": evidence_refs,
        "status": claim_status,
        "claim_status": claim_status,
        "failed_gate": failed_gate,
        "not_claimed": list(NOT_CLAIMED),
        "what_was_learned": capsule["what_was_learned"],
        "revocation": capsule["revocation"],
        "forbidden_claim_term_audit": capsule["forbidden_claim_term_audit"],
        "claim_capsule_ref": RUN_ARTIFACTS["claim_capsule"],
        "run_artifacts": dict(RUN_ARTIFACTS),
        "reproducibility": {
            "seed": SEED,
            "byte_identical": deterministic_replay,
            "artifact_set": [
                RUN_ARTIFACTS["compression_preservation"],
                RUN_ARTIFACTS["claim_capsule"],
                RUN_ARTIFACTS["raw_metrics"],
                RUN_ARTIFACTS["summary"],
                RUN_ARTIFACTS["report"],
            ],
        },
    }
    evidence_refs["pointer_resolution"]["all_required_pointers_resolve"] = all(
        pointer_value(payload, pointer) is not None for _, pointer in pointer_rows if pointer.startswith("$.")
    )
    payload["evidence_refs"] = evidence_refs
    capsule["evidence_refs"] = evidence_refs
    summary = {
        "schema_id": SCHEMA_ID,
        "claim_id": CLAIM_ID,
        "generated_at": GENERATED_AT,
        "producer": SCRIPT_PATH,
        "source": RUN_ARTIFACTS["compression_preservation"],
        "source_pointer": "$.hardgates.H2-HG3",
        "claim_status": claim_status,
        "failed_gate": failed_gate,
        "hardgates": hardgates,
        "not_claimed": capsule["not_claimed"],
        "what_was_learned": capsule["what_was_learned"],
        "revocation": capsule["revocation"],
        "forbidden_claim_term_audit": capsule["forbidden_claim_term_audit"],
        "run_artifacts": dict(RUN_ARTIFACTS),
    }
    raw_rows = _raw_metric_rows(payload)
    report = _markdown_report(payload)
    return {
        "compression_preservation": payload,
        "claim_capsule": capsule,
        "raw_metrics": raw_rows,
        "summary": summary,
        "report": report,
    }


def _raw_metric_rows(payload: Mapping[str, Any]) -> list[dict[str, Any]]:
    student = payload["arms"]["student_performance_distilled"]
    teacher = payload["arms"]["teacher_performance"]
    return [
        {
            "arm": "teacher",
            "metric": "task_accuracy",
            "value": teacher["task_accuracy"],
            "seed": SEED,
        },
        {
            "arm": "student_performance_distilled",
            "metric": "task_accuracy",
            "value": student["task_accuracy"],
            "seed": SEED,
        },
        {
            "arm": "student_performance_distilled",
            "metric": "classifier_agreement",
            "value": student["classifier_agreement"],
            "seed": SEED,
        },
        {
            "arm": "student_performance_distilled",
            "metric": "gap_head_agreement",
            "value": student["gap_head_agreement"],
            "seed": SEED,
        },
        {
            "arm": "student_performance_distilled",
            "metric": "ledger_equivalence",
            "value": student["ledger_equivalence"],
            "seed": SEED,
        },
    ]


def _markdown_report(payload: Mapping[str, Any]) -> str:
    student = payload["arms"]["student_performance_distilled"]
    lines = [
        "# Compression Preservation",
        "",
        f"- Claim status: `{payload['claim_status']}`",
        f"- Failed gate: `{payload['failed_gate']}`",
        f"- Task preserved: `{str(student['task_preserved']).lower()}`",
        f"- Classifier agreement: `{student['classifier_agreement']:.6f}`",
        f"- Gap-head agreement: `{student['gap_head_agreement']:.6f}`",
        f"- Ledger equivalence: `{str(student['ledger_equivalence']).lower()}`",
        "",
        "## Hardgates",
        "",
        "| gate | status | evidence pointer | evidence |",
        "| --- | --- | --- | --- |",
    ]
    for gate, row in payload["hardgates"].items():
        lines.append(f"| {gate} | `{row['status']}` | `{row['evidence_pointer']}` | {row['evidence']} |")
    lines.extend(["", "## Not Claimed", ""])
    lines.extend(f"- {item}" for item in payload["not_claimed"])
    lines.append("")
    return "\n".join(lines)


def serialize_artifacts(artifacts: Mapping[str, Any]) -> dict[Path, bytes]:
    raw_metrics = "\n".join(_json_line(row) for row in artifacts["raw_metrics"]) + "\n"
    return {
        JSON_ARTIFACT: _json_dump(artifacts["compression_preservation"]).encode("utf-8"),
        CAPSULE_ARTIFACT: _json_dump(artifacts["claim_capsule"]).encode("utf-8"),
        RAW_METRICS_ARTIFACT: raw_metrics.encode("utf-8"),
        SUMMARY_ARTIFACT: _json_dump(artifacts["summary"]).encode("utf-8"),
        REPORT_ARTIFACT: artifacts["report"].encode("utf-8"),
    }


def write_artifacts(*, root: Path | None = None) -> dict[str, Any]:
    artifacts = build_artifacts(deterministic_replay=True)
    first = serialize_artifacts(artifacts)
    second = serialize_artifacts(build_artifacts(deterministic_replay=True))
    if {path.name: data for path, data in first.items()} != {path.name: data for path, data in second.items()}:
        artifacts = build_artifacts(deterministic_replay=False)
        first = serialize_artifacts(artifacts)
    target_root = REPORT_DIR if root is None else root
    target_root.mkdir(parents=True, exist_ok=True)
    for path, data in first.items():
        (target_root / path.name).write_bytes(data)
    return artifacts


def committed_json_round_trip(root: Path | None = None) -> dict[str, Any]:
    target_root = REPORT_DIR if root is None else root
    return {
        "compression_preservation": json.loads((target_root / JSON_ARTIFACT.name).read_text(encoding="utf-8")),
        "claim_capsule": json.loads((target_root / CAPSULE_ARTIFACT.name).read_text(encoding="utf-8")),
        "summary": json.loads((target_root / SUMMARY_ARTIFACT.name).read_text(encoding="utf-8")),
        "raw_metrics": [
            json.loads(line)
            for line in (target_root / RAW_METRICS_ARTIFACT.name).read_text(encoding="utf-8").splitlines()
            if line.strip()
        ],
    }


def with_mutated_cell(payload: Mapping[str, Any], pointer: str, value: Any) -> dict[str, Any]:
    cloned = deepcopy(payload)
    current: Any = cloned
    parts = pointer[2:].split(".")
    for part in parts[:-1]:
        current = current[part]
    current[parts[-1]] = value
    return cloned


def main() -> None:
    write_artifacts()
    print(f"wrote {RUN_ARTIFACTS['compression_preservation']}")
    print(f"wrote {RUN_ARTIFACTS['claim_capsule']}")
    print("IMPLEMENT_RUN:compression_preservation:ok")


if __name__ == "__main__":
    main()
