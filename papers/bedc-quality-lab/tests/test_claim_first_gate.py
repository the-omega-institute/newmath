import json
from pathlib import Path
from tempfile import TemporaryDirectory

from bedc_quality_lab.experiment_stack import (
    EXPERIMENT_STACK_CARDS,
    build_experiment_stack_payload,
    evaluate_claim_first_gate,
)


EXPECTED_CARD_IDS = (
    "claim-card",
    "task-target-card",
    "data-card",
    "feature-access-card",
    "baseline-validity-card",
    "ood-solvability-card",
    "metric-provenance-card",
    "training-authenticity-card",
    "statistical-evidence-card",
    "ablation-causal-evidence-card",
    "artifact-reproducibility-card",
    "model-card",
    "risk-scope-review-card",
    "release-readiness-board",
)
EXPECTED_PREFLIGHT_CARD_IDS = (
    EXPECTED_CARD_IDS[0],
    EXPECTED_CARD_IDS[1],
    EXPECTED_CARD_IDS[3],
    EXPECTED_CARD_IDS[4],
    EXPECTED_CARD_IDS[5],
    EXPECTED_CARD_IDS[6],
)


def _pointer_tokens(pointer: str) -> list[str | int]:
    assert pointer.startswith("$.")
    tokens: list[str | int] = []
    for part in pointer[2:].split("."):
        while "[" in part and part.endswith("]"):
            key, bracket = part.split("[", 1)
            if key:
                tokens.append(key)
            tokens.append(int(bracket[:-1]))
            part = ""
        if part:
            tokens.append(part)
    return tokens


def _set_pointer_value(payload: dict[str, object], pointer: str, value: dict[str, object]) -> None:
    tokens = _pointer_tokens(pointer)
    cursor: object = payload
    for index, token in enumerate(tokens):
        last = index == len(tokens) - 1
        if isinstance(token, str):
            assert isinstance(cursor, dict)
            if last:
                existing = cursor.get(token)
                if isinstance(existing, dict):
                    existing.update(value)
                else:
                    cursor[token] = dict(value)
                return
            next_token = tokens[index + 1]
            cursor = cursor.setdefault(token, [] if isinstance(next_token, int) else {})
            continue
        assert isinstance(cursor, list)
        while len(cursor) <= token:
            cursor.append({})
        if last:
            existing = cursor[token]
            if isinstance(existing, dict):
                existing.update(value)
            else:
                cursor[token] = dict(value)
            return
        next_token = tokens[index + 1]
        if not isinstance(cursor[token], (dict, list)):
            cursor[token] = [] if isinstance(next_token, int) else {}
        cursor = cursor[token]


def _write_owner_artifacts(root: Path, card_ids: tuple[str, ...]) -> None:
    specs = {spec.card_id: spec for spec in EXPERIMENT_STACK_CARDS}
    payloads: dict[str, dict[str, object]] = {}
    for card_id in card_ids:
        spec = specs[card_id]
        payload = payloads.setdefault(
            spec.owner_artifact,
            {"schema_id": spec.schema_id, "artifact_id": spec.schema_id},
        )
        for pointer in (spec.source_pointer, spec.summary_pointer, spec.demotion_rule_pointer):
            artifact, json_pointer = pointer.split(":", 1)
            assert artifact == spec.owner_artifact
            _set_pointer_value(payload, json_pointer, {"fixture": card_id})
    for artifact, payload in payloads.items():
        path = root / artifact
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _projected_cards(root: Path, card_ids: tuple[str, ...]) -> list[dict[str, object]]:
    payload = build_experiment_stack_payload(root=root, generated_at="fixture")
    rows = {row["card_id"]: row for row in payload["cards"]}
    return [rows[card_id] for card_id in card_ids]


def test_claim_first_gate_contract_uses_fixed_card_inventory():
    payload = build_experiment_stack_payload(root=Path("."), generated_at="fixture")

    assert tuple(spec.card_id for spec in EXPERIMENT_STACK_CARDS) == EXPECTED_CARD_IDS
    assert tuple(payload["card_ids"]) == EXPECTED_CARD_IDS
    assert tuple(payload["claim_first_gate"]["required_preflight_cards"]) == EXPECTED_PREFLIGHT_CARD_IDS


def test_claim_first_gate_blocks_training_result_without_preflight_cards():
    decision = evaluate_claim_first_gate(
        {
            "claim_kind": "promoted_training",
            "experiment_stack": {"cards": []},
            "training_result_refs": [
                {"ref": "reports/canonical/discovery-gated-transformer.json:$.scaling_ladder"},
            ],
        }
    )

    assert decision.status == "blocked"
    assert set(decision.failed_card_ids) == set(EXPECTED_PREFLIGHT_CARD_IDS)
    assert decision.blocked_training_result_refs == (
        "reports/canonical/discovery-gated-transformer.json:$.scaling_ladder",
    )
    assert "task-target-card" in decision.pointer_reasons
    assert "baseline-validity-card" in decision.pointer_reasons


def test_claim_first_gate_negative_fixture():
    passing_subset = (
        "claim-card",
        "feature-access-card",
        "ood-solvability-card",
        "metric-provenance-card",
    )
    with TemporaryDirectory() as raw_root:
        root = Path(raw_root)
        _write_owner_artifacts(root, passing_subset)
        fixture = {
            "root": root,
            "claim_kind": "promoted_training",
            "experiment_stack": {"cards": _projected_cards(root, passing_subset)},
            "training_result_refs": [
                {
                    "artifact_pointer": "reports/canonical/model-comparison.json:$.models[0].metrics",
                    "metric": "quality_q",
                }
            ],
        }

        decision = evaluate_claim_first_gate(fixture)

    assert decision.status == "blocked"
    assert "task-target-card" in decision.failed_card_ids
    assert "baseline-validity-card" in decision.failed_card_ids
    assert "label-function" in decision.pointer_reasons["task-target-card"]
    assert decision.blocked_training_result_refs == (
        "reports/canonical/model-comparison.json:$.models[0].metrics",
    )


def test_claim_first_gate_passes_after_preflight_cards():
    with TemporaryDirectory() as raw_root:
        root = Path(raw_root)
        _write_owner_artifacts(root, EXPECTED_PREFLIGHT_CARD_IDS)
        context = {
            "root": root,
            "claim_kind": "promoted_training",
            "experiment_stack": {"cards": _projected_cards(root, EXPECTED_PREFLIGHT_CARD_IDS)},
            "training_result_refs": ["reports/canonical/model-comparison.json:$.models[0].metrics"],
        }

        decision = evaluate_claim_first_gate(context)

    assert decision.status == "pass"
    assert decision.failed_card_ids == ()
    assert decision.blocked_training_result_refs == ()


def test_claim_first_gate_rejects_stub_pass_cards():
    cards = [
        {
            "card_id": card_id,
            "status": "pass",
            "owner_artifact_status": "missing",
            "source_pointer_status": "missing",
            "summary_pointer_status": "missing",
            "demotion_rule_pointer_status": "missing",
        }
        for card_id in EXPECTED_PREFLIGHT_CARD_IDS
    ]

    decision = evaluate_claim_first_gate(
        {
            "claim_kind": "promoted_training",
            "experiment_stack": {"cards": cards},
            "training_result_refs": ["reports/canonical/model-comparison.json:$.models[0].metrics"],
        }
    )

    assert decision.status == "blocked"
    assert set(decision.failed_card_ids) == set(EXPECTED_PREFLIGHT_CARD_IDS)
    assert "owner_artifact_status-not-resolved" in decision.pointer_reasons["claim-card"]


def test_claim_first_gate_not_applicable_without_training_promotion():
    decision = evaluate_claim_first_gate({"experiment_stack": {"cards": []}})

    assert decision.status == "not-applicable"
    assert decision.failed_card_ids == ()
