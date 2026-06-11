import copy
import json
from pathlib import Path

from bedc_quality_lab import dgt_model_card as card


def _write_json(root: Path, artifact: str, payload: dict) -> None:
    path = root / artifact
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _source_fixture(root: Path) -> None:
    _write_json(
        root,
        "reports/canonical/dgt-l0-controls.json",
        {
            "l0_toy_projection": {
                "status": "pass",
                "review_status": "pass",
                "not_claimed": ["bounded only"],
            }
        },
    )
    _write_json(
        root,
        "reports/canonical/dgt-l1-controls.json",
        {
            "task_spec": {"task": "tiny-sequence"},
            "training_arms": {"dgt_l1": {"status": "present"}},
            "l1_tiny_sequence_projection": {
                "status": "pass",
                "review_status": "pass",
                "ood_generalization_claim": "not-claimed",
                "ood_boundary": {
                    "chance_accuracy": 0.0625,
                    "dgt_ood_accuracy_ci95_low": 0.06309,
                },
                "boundary_ledger": [{"status": "scoped-boundary"}],
            },
        },
    )
    _write_json(
        root,
        "reports/canonical/dgt-base-undertraining-audit.json",
        {
            "base_undertraining_audit": {
                "verdict": "construct-boundary",
                "claim_action": "defer-to-fair-reconstruction",
                "construct_validity": {
                    "status": "construct-boundary",
                    "bayes_upper_bound_accuracy": 0.0625,
                    "source_pointers": {"fair_reconstruction": "https://github.com/the-omega-institute/newmath/issues/1196"},
                },
            }
        },
    )
    _write_json(
        root,
        "reports/canonical/dgt-ablation-null-decomposition.json",
        {
            "null_decomposition": {
                "analysis_status": "pass",
                "verdict": "mixed",
            }
        },
    )
    _write_json(
        root,
        "reports/canonical/discovery-gated-transformer.json",
        {
            "model_id": "discovery-gated-transformer",
            "not_claimed": ["bounded deterministic toy evidence only"],
        },
    )
    _write_json(
        root,
        "reports/canonical/index.json",
        {
            "evidence_provenance": {
                "source_type": "canonical-owner-index",
                "evidence_type": "pointer-only",
            }
        },
    )


def _build(root: Path) -> dict:
    _source_fixture(root)
    return card.build_dgt_model_card(root=root, generated_at="2030-01-01T00:00:00+00:00")


def _errors(payload: dict, root: Path) -> list[str]:
    return [error.gate_id for error in card.validate_dgt_model_card(payload, root)]


def test_not_intended_literals_are_exact(tmp_path):
    payload = _build(tmp_path)
    literals = [row["literal"] for row in payload["not_intended_use"]]

    assert literals == list(card.REQUIRED_NOT_INTENDED_LITERALS)
    assert payload["card_hardgates"]["gates"]["CARD-HG2"]["status"] == "pass"


def test_not_intended_literal_rewrite_fails(tmp_path):
    payload = _build(tmp_path)
    payload["not_intended_use"][3]["literal"] = "not broad Transformer superiority"

    errors = _errors(payload, tmp_path)

    assert "CARD-HG2" in errors


def test_card_numeric_cells_are_pointer_backed(tmp_path):
    payload = _build(tmp_path)
    payload["training_facts"]["metric_cells"].append({"metric": "unowned", "value": 7})

    errors = _errors(payload, tmp_path)

    assert "CARD-HG3" in errors


def test_l0_status_is_derived_from_owner_pointer(tmp_path):
    payload = _build(tmp_path)
    l0 = next(row for row in payload["evaluation_boundaries"] if row["source_owner"] == "dgt-l0-controls")
    l0["status"] = "pass-by-hand"

    errors = _errors(payload, tmp_path)

    assert "CARD-HG4" in errors


def test_l1_construct_invalid_and_fair_decision_are_separate(tmp_path):
    payload = _build(tmp_path)
    fair = next(row for row in payload["evaluation_boundaries"] if row["boundary"] == "fair architecture comparison")

    assert fair["construct_validity_status"] == "construct-boundary"
    assert fair["status"] == "defer-to-fair-reconstruction"
    assert fair["claim"] == "no architecture advantage"
    assert "architecture advantage" not in json.dumps(payload["intended_use"], sort_keys=True)

    fair["claim"] = "architecture advantage"
    assert "CARD-HG5" in _errors(payload, tmp_path)


def test_ablation_null_rendered_as_boundary_not_positive(tmp_path):
    payload = _build(tmp_path)

    assert any(row["source_owner"] == "dgt-ablation-null-decomposition" for row in payload["known_failure_modes"])
    assert "ablation" not in json.dumps(payload["intended_use"], sort_keys=True).lower()

    payload["intended_use"].append(
        {
            "scope": "ablation null positive",
            "source_owner": "dgt-ablation-null-decomposition",
            "source_pointer": "reports/canonical/dgt-ablation-null-decomposition.json:$.null_decomposition",
        }
    )
    assert "CARD-HG6" in _errors(payload, tmp_path)


def test_evidence_class_and_metric_provenance_consumed_from_index_owner(tmp_path):
    payload = _build(tmp_path)

    provenance = payload["training_facts"]["evidence_provenance"]
    assert provenance["source_pointer"] == card.INDEX_EVIDENCE_PROVENANCE_POINTER
    assert provenance["source_type"] == "canonical-owner-index"
    assert provenance["evidence_type"] == "pointer-only"

    provenance["evidence_type"] = "local-card-enum"
    assert "CARD-HG7" in _errors(payload, tmp_path)


def test_owner_flip_without_regen_fails_stale(tmp_path):
    payload = _build(tmp_path)
    source_path = tmp_path / "reports/canonical/dgt-l1-controls.json"
    source = json.loads(source_path.read_text(encoding="utf-8"))
    source["l1_tiny_sequence_projection"]["status"] = "blocked"
    source_path.write_text(json.dumps(source, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    errors = _errors(payload, tmp_path)

    assert "CARD-HG9" in errors


def test_card_regen_idempotent(tmp_path):
    _source_fixture(tmp_path)
    first = card.write_dgt_model_card(root=tmp_path, generated_at="2030-01-01T00:00:00+00:00")
    first_json = (tmp_path / card.CANONICAL_JSON_ARTIFACT).read_text(encoding="utf-8")
    first_md = (tmp_path / card.CANONICAL_MARKDOWN_ARTIFACT).read_text(encoding="utf-8")
    second = card.write_dgt_model_card(root=tmp_path, generated_at="2030-01-01T00:00:00+00:00")
    second_json = (tmp_path / card.CANONICAL_JSON_ARTIFACT).read_text(encoding="utf-8")
    second_md = (tmp_path / card.CANONICAL_MARKDOWN_ARTIFACT).read_text(encoding="utf-8")

    assert first == second
    assert first_json == second_json
    assert first_md == second_md


def test_markdown_is_rendered_from_json(tmp_path):
    payload = _build(tmp_path)
    markdown = card.render_dgt_model_card_markdown(payload)

    assert card.validate_dgt_model_card_markdown(payload, markdown) == []
    assert card.validate_dgt_model_card_markdown(payload, markdown.replace("not production model", "production model"))
    assert card.render_dgt_model_card_markdown(copy.deepcopy(payload)) == markdown
