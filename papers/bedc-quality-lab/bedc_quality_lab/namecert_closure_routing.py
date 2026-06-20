"""Package-owned NameCert closure-routing benchmark record."""

from __future__ import annotations

from dataclasses import asdict, dataclass, replace
from datetime import datetime, timezone
import json
from pathlib import Path
from typing import Any, Literal, Mapping, Sequence

import torch


SCHEMA_ID = "bedc-quality-lab:namecert-closure-routing"
ARTIFACT_ID = SCHEMA_ID
PRODUCER = "bedc_quality_lab.namecert_closure_routing"
GENERATED_AT = "2026-06-20T00:00:00+00:00"
DEFAULT_TOLERANCE = 0.0
REPORT_ROOT = "reports"

ProfileId = Literal[
    "smoke_closure_routing",
    "smoke_closure_verify",
    "smoke_authswap",
    "smoke_audit",
]


@dataclass(frozen=True)
class NameCertClosureRoutingProfile:
    profile_id: ProfileId
    report_stem: str
    train_max_depth: int = 3
    heldout_depth: int = 4
    repeats: int = 4
    epochs: int = 64
    learning_rate: float = 0.75
    analytic_bayes: float = 1.0
    analytic_tolerance: float = DEFAULT_TOLERANCE
    admission_eligible: bool = False

    @property
    def json_artifact(self) -> str:
        return f"{REPORT_ROOT}/{self.report_stem}.json"

    @property
    def markdown_artifact(self) -> str:
        return f"{REPORT_ROOT}/{self.report_stem}.md"


@dataclass(frozen=True)
class NameCertClosureRoutingRecord:
    schema_id: str
    artifact_id: str
    generated_at: str
    producer: str
    profile: dict[str, Any]
    device_policy: dict[str, Any]
    source_scope: dict[str, Any]
    metrics: dict[str, Any]
    hardgates: dict[str, Any]
    analytic_ceiling: dict[str, Any]
    admission: dict[str, Any]
    json_artifact: str
    markdown_artifact: str

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)


PROFILES: dict[str, NameCertClosureRoutingProfile] = {
    "smoke_closure_routing": NameCertClosureRoutingProfile(
        profile_id="smoke_closure_routing",
        report_stem="namecert_closure_routing",
    ),
    "smoke_closure_verify": NameCertClosureRoutingProfile(
        profile_id="smoke_closure_verify",
        report_stem="namecert_closure_verify",
    ),
    "smoke_authswap": NameCertClosureRoutingProfile(
        profile_id="smoke_authswap",
        report_stem="namecert_authswap",
    ),
    "smoke_audit": NameCertClosureRoutingProfile(
        profile_id="smoke_audit",
        report_stem="namecert_audit",
    ),
}


def build_record(
    profile: str | NameCertClosureRoutingProfile,
    *,
    root: Path | str | None = None,
    device: str = "auto",
    generated_at: str | None = None,
    train_max_depth: int | None = None,
    epochs: int | None = None,
) -> NameCertClosureRoutingRecord:
    active_profile = resolve_profile(profile, train_max_depth=train_max_depth, epochs=epochs)
    device_policy = resolve_device_policy(device)
    torch_device = torch.device(device_policy["selected"])
    metrics = run_profile_metrics(active_profile, torch_device)
    hardgates = evaluate_hardgates(metrics, active_profile)
    analytic_ceiling = {
        "analytic_bayes": active_profile.analytic_bayes,
        "tolerance": active_profile.analytic_tolerance,
        "learned_accuracy": metrics["learned"]["accuracy"],
        "status": "pass"
        if metrics["learned"]["accuracy"] <= active_profile.analytic_bayes + active_profile.analytic_tolerance
        else "fail",
    }
    hardgates["analytic_ceiling"] = {
        "status": analytic_ceiling["status"],
        "predicate": "learned_accuracy <= analytic_bayes + tolerance",
        "observed": metrics["learned"]["accuracy"],
        "limit": active_profile.analytic_bayes + active_profile.analytic_tolerance,
    }
    admission = {
        "admission_gate": bool(active_profile.admission_eligible and all(row["status"] == "pass" for row in hardgates.values())),
        "eligible": active_profile.admission_eligible,
        "not_claimed": [
            "not a formal BEDC NameCert",
            "not Lean verification",
            "not a paper closurestatus",
            "not an external benchmark superiority claim",
        ],
    }
    return NameCertClosureRoutingRecord(
        schema_id=SCHEMA_ID,
        artifact_id=ARTIFACT_ID,
        generated_at=generated_at or GENERATED_AT,
        producer=PRODUCER,
        profile={
            "profile_id": active_profile.profile_id,
            "train_max_depth": active_profile.train_max_depth,
            "heldout_depth": active_profile.heldout_depth,
            "repeats": active_profile.repeats,
            "epochs": active_profile.epochs,
            "learning_rate": active_profile.learning_rate,
        },
        device_policy=device_policy,
        source_scope={
            "semantics": "lab-local NameCert closure-routing construct-validity smoke",
            "matched_twin": True,
            "serialization_adversary": True,
            "heldout_depth": True,
            "bounded_pattern_control": True,
        },
        metrics=metrics,
        hardgates=hardgates,
        analytic_ceiling=analytic_ceiling,
        admission=admission,
        json_artifact=active_profile.json_artifact,
        markdown_artifact=active_profile.markdown_artifact,
    )


def run_and_write(
    profile: str | NameCertClosureRoutingProfile,
    *,
    root: Path | str | None = None,
    device: str = "auto",
    generated_at: str | None = None,
    train_max_depth: int | None = None,
    epochs: int | None = None,
    write_markdown: bool = True,
) -> dict[str, Any]:
    active_root = Path.cwd() if root is None else Path(root)
    record = build_record(
        profile,
        root=active_root,
        device=device,
        generated_at=generated_at,
        train_max_depth=train_max_depth,
        epochs=epochs,
    )
    payload = record.to_dict()
    write_json(active_root / record.json_artifact, payload)
    if write_markdown:
        write_text(active_root / record.markdown_artifact, render_markdown(payload))
    return payload


def resolve_profile(
    profile: str | NameCertClosureRoutingProfile,
    *,
    train_max_depth: int | None = None,
    epochs: int | None = None,
) -> NameCertClosureRoutingProfile:
    if isinstance(profile, NameCertClosureRoutingProfile):
        active = profile
    else:
        try:
            active = PROFILES[profile]
        except KeyError as exc:
            raise ValueError(f"unknown NameCert closure-routing profile: {profile}") from exc
    if train_max_depth is not None:
        if train_max_depth < 1:
            raise ValueError("train_max_depth must be positive")
        active = replace(active, train_max_depth=train_max_depth, heldout_depth=train_max_depth + 1)
    if epochs is not None:
        if epochs < 1:
            raise ValueError("epochs must be positive")
        active = replace(active, epochs=epochs)
    return active


def resolve_device_policy(requested: str = "auto") -> dict[str, Any]:
    normalized = requested.strip().lower()
    if normalized not in {"auto", "cpu", "cuda"}:
        raise ValueError("device must be one of: auto, cpu, cuda")
    cuda_available = bool(torch.cuda.is_available())
    if normalized == "cuda" and not cuda_available:
        raise RuntimeError("requested cuda device is not available")
    selected = "cuda" if normalized == "auto" and cuda_available else normalized
    if selected == "auto":
        selected = "cpu"
    return {
        "requested": normalized,
        "selected": selected,
        "cuda_available": cuda_available,
        "owner": PRODUCER,
    }


def run_profile_metrics(profile: NameCertClosureRoutingProfile, device: torch.device) -> dict[str, Any]:
    train = _make_dataset(range(1, profile.train_max_depth + 1), repeats=profile.repeats, device=device)
    heldout = _make_dataset((profile.heldout_depth,), repeats=profile.repeats, device=device)
    full_weights = _fit_logistic(train["full"], train["labels"], epochs=profile.epochs, learning_rate=profile.learning_rate)
    blind_weights = _fit_logistic(train["closure_blind"], train["labels"], epochs=profile.epochs, learning_rate=profile.learning_rate)
    serialization_weights = _fit_logistic(train["serialization_only"], train["labels"], epochs=profile.epochs, learning_rate=profile.learning_rate)
    learned_train = _evaluate(full_weights, train["full"], train["labels"])
    learned_heldout = _evaluate(full_weights, heldout["full"], heldout["labels"])
    closure_blind = _evaluate(blind_weights, train["closure_blind"], train["labels"])
    serialization_only = _evaluate(serialization_weights, train["serialization_only"], train["labels"])
    bounded_pattern = _bounded_pattern_control(train, heldout)
    return {
        "learned": learned_train,
        "matched_twin_closure_blind": closure_blind,
        "serialization_only_adversary": serialization_only,
        "heldout_depth": {
            **learned_heldout,
            "depth": profile.heldout_depth,
            "train_max_depth": profile.train_max_depth,
        },
        "bounded_pattern_control": bounded_pattern,
    }


def evaluate_hardgates(metrics: Mapping[str, Any], profile: NameCertClosureRoutingProfile) -> dict[str, Any]:
    learned = _metric(metrics, "learned")
    closure_blind = _metric(metrics, "matched_twin_closure_blind")
    serialization_only = _metric(metrics, "serialization_only_adversary")
    heldout = _metric(metrics, "heldout_depth")
    bounded = _metric(metrics, "bounded_pattern_control")
    return {
        "matched_twin_closure_blind_chance": _gate(
            _ci_contains(closure_blind, 0.5),
            "matched-twin closure-blind CI contains chance",
            closure_blind,
        ),
        "learned_above_chance": _gate(
            float(learned.get("accuracy", 0.0)) > 0.5,
            "learned route classifier is above chance",
            learned,
        ),
        "serialization_only_adversary_chance": _gate(
            _ci_contains(serialization_only, 0.5),
            "serialization-only adversary CI contains chance",
            serialization_only,
        ),
        "heldout_depth_above_chance": _gate(
            int(heldout.get("depth", 0)) > profile.train_max_depth and float(heldout.get("accuracy", 0.0)) > 0.5,
            "held-out depth exceeds train max depth and remains above chance",
            heldout,
        ),
        "bounded_pattern_chance": _gate(
            _ci_contains(bounded, 0.5),
            "bounded-pattern control CI contains chance",
            bounded,
        ),
    }


def render_markdown(payload: Mapping[str, Any]) -> str:
    profile = _mapping(payload.get("profile"))
    metrics = _mapping(payload.get("metrics"))
    gates = _mapping(payload.get("hardgates"))
    lines = [
        "# NameCert Closure-Routing Benchmark",
        "",
        f"- profile: `{profile.get('profile_id')}`",
        f"- json artifact: `{payload.get('json_artifact')}`",
        f"- admission gate: `{_mapping(payload.get('admission')).get('admission_gate')}`",
        "",
        "## Metrics",
        "",
    ]
    for key in (
        "learned",
        "matched_twin_closure_blind",
        "serialization_only_adversary",
        "heldout_depth",
        "bounded_pattern_control",
    ):
        row = _mapping(metrics.get(key))
        lines.append(f"- `{key}` accuracy `{row.get('accuracy')}` ci `{row.get('ci')}`")
    lines.extend(["", "## Hardgates", ""])
    for key, row_value in gates.items():
        row = _mapping(row_value)
        lines.append(f"- `{key}`: `{row.get('status')}`")
    return "\n".join(lines) + "\n"


def write_json(path: Path, payload: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    tmp.replace(path)


def write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(text, encoding="utf-8")
    tmp.replace(path)


def _make_dataset(depths: Sequence[int] | range, *, repeats: int, device: torch.device) -> dict[str, torch.Tensor]:
    rows: list[list[float]] = []
    labels: list[float] = []
    depth_values: list[int] = []
    for depth in depths:
        for _repeat in range(repeats):
            for route_signal in (-1.0, 1.0):
                for authority in (-1.0, 1.0):
                    for serial in (-1.0, 1.0):
                        rows.append([route_signal, depth / 10.0, authority, serial, 1.0])
                        labels.append(1.0 if route_signal > 0 else 0.0)
                        depth_values.append(depth)
    data = torch.tensor(rows, dtype=torch.float32, device=device)
    return {
        "full": data,
        "closure_blind": data[:, 1:],
        "serialization_only": data[:, 3:4],
        "labels": torch.tensor(labels, dtype=torch.float32, device=device),
        "depths": torch.tensor(depth_values, dtype=torch.int64, device=device),
    }


def _fit_logistic(features: torch.Tensor, labels: torch.Tensor, *, epochs: int, learning_rate: float) -> torch.Tensor:
    weights = torch.zeros(features.shape[1], dtype=features.dtype, device=features.device, requires_grad=True)
    for _epoch in range(epochs):
        loss = torch.nn.functional.binary_cross_entropy_with_logits(features.mv(weights), labels)
        loss.backward()
        with torch.no_grad():
            weights -= learning_rate * weights.grad
            weights.grad.zero_()
    return weights.detach()


def _evaluate(weights: torch.Tensor, features: torch.Tensor, labels: torch.Tensor) -> dict[str, Any]:
    logits = features.mv(weights)
    predicted = (torch.sigmoid(logits) >= 0.5).to(labels.dtype)
    correct = int((predicted == labels).sum().item())
    total = int(labels.numel())
    accuracy = correct / total
    return {
        "accuracy": accuracy,
        "correct": correct,
        "total": total,
        "ci": _normal_ci(correct, total),
    }


def _bounded_pattern_control(train: Mapping[str, torch.Tensor], heldout: Mapping[str, torch.Tensor]) -> dict[str, Any]:
    train_depths = train["depths"].detach().cpu().tolist()
    train_labels = train["labels"].detach().cpu().tolist()
    majority_by_depth: dict[int, float] = {}
    for depth in sorted(set(train_depths)):
        cells = [label for observed_depth, label in zip(train_depths, train_labels) if observed_depth == depth]
        majority_by_depth[depth] = 1.0 if sum(cells) > len(cells) / 2 else 0.0
    heldout_depths = heldout["depths"].detach().cpu().tolist()
    heldout_labels = heldout["labels"].detach().cpu().tolist()
    predictions = [majority_by_depth.get(depth, 0.0) for depth in heldout_depths]
    correct = sum(1 for predicted, label in zip(predictions, heldout_labels) if predicted == label)
    total = len(heldout_labels)
    return {
        "accuracy": correct / total,
        "correct": correct,
        "total": total,
        "ci": _normal_ci(correct, total),
        "predictor": "train-depth-majority",
    }


def _normal_ci(correct: int, total: int) -> list[float]:
    if total <= 0:
        return [0.0, 0.0]
    p = correct / total
    radius = 1.96 * ((p * (1.0 - p) / total) ** 0.5)
    return [max(0.0, p - radius), min(1.0, p + radius)]


def _metric(metrics: Mapping[str, Any], key: str) -> Mapping[str, Any]:
    value = metrics.get(key)
    if not isinstance(value, Mapping):
        return {}
    return value


def _mapping(value: Any) -> Mapping[str, Any]:
    if isinstance(value, Mapping):
        return value
    return {}


def _ci_contains(metric: Mapping[str, Any], value: float) -> bool:
    ci = metric.get("ci")
    if not isinstance(ci, Sequence) or len(ci) != 2:
        return False
    try:
        low = float(ci[0])
        high = float(ci[1])
    except (TypeError, ValueError):
        return False
    return low <= value <= high


def _gate(passed: bool, predicate: str, observed: Mapping[str, Any]) -> dict[str, Any]:
    return {
        "status": "pass" if passed else "fail",
        "predicate": predicate,
        "observed": dict(observed),
    }


def current_timestamp() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat()
