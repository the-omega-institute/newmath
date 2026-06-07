import json
from pathlib import Path

import pytest

from bedc_quality_lab.dgt_character_transition import (
    CHARACTER_TRANSITION_POINTER,
    REQUIRED_RERUN_POINTER_KEYS,
    build_character_lm_transition,
)


def _write_json(root: Path, artifact: str, payload: dict) -> None:
    path = root / artifact
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, sort_keys=True) + "\n", encoding="utf-8")


def _write_character_evidence(root: Path) -> None:
    _write_json(
        root,
        "reports/canonical/character_evidence.json",
        {
            "char_lm_run": {"target_surface": "character-level-lm", "status": "complete"},
            "heads": {
                "ledger": {"target_surface": "character-level-lm", "status": "pass"},
                "gap": {"target_surface": "character-level-lm", "status": "pass"},
                "certificate": {"target_surface": "character-level-lm", "status": "pass"},
            },
            "drt": {
                "target_surface": "character-level-lm",
                "character_surface_rerun": True,
                "status": "pass",
            },
            "classifier_surface_delta": {
                "target_surface": "character-level-lm",
                "net_positive_signal": True,
            },
        },
    )


def _valid_pointers() -> dict[str, str]:
    artifact = "reports/canonical/character_evidence.json"
    return {
        "char_lm_run": f"{artifact}:$.char_lm_run",
        "ledger_head_evidence": f"{artifact}:$.heads.ledger",
        "gap_head_evidence": f"{artifact}:$.heads.gap",
        "certificate_head_evidence": f"{artifact}:$.heads.certificate",
        "drt_rerun_evidence": f"{artifact}:$.drt",
        "classifier_surface_delta": f"{artifact}:$.classifier_surface_delta",
    }


def _transition(root: Path, pointers: dict[str, str] | None = None) -> dict:
    _write_character_evidence(root)
    return build_character_lm_transition(
        toy_antecedent_pointer="reports/canonical/toy_safety_boundary.json:$.discovery_map_signal",
        required_rerun_pointers=pointers or _valid_pointers(),
        root=root,
    )


def test_character_transition_blocks_toy_d4_inheritance(tmp_path):
    pointers = _valid_pointers()
    pointers["char_lm_run"] = "reports/canonical/toy_safety_boundary.json:$.d4_status"
    _write_json(tmp_path, "reports/canonical/toy_safety_boundary.json", {"d4_status": {"level": "D4"}})

    transition = _transition(tmp_path, pointers)

    assert transition["status"] == "present-but-fail-closed"
    assert transition["hardgate"]["DGT-CHAR-HG1"]["failed_reason"] == "toy-evidence-is-antecedent-only"
    assert transition["discovery_map_signal"]["level_candidate"] == "DN"


def test_character_transition_requires_exact_rerun_pointer_set(tmp_path):
    pointers = _valid_pointers()
    pointers["extra"] = "reports/canonical/character_evidence.json:$.extra"

    with pytest.raises(ValueError, match="rerun pointer set"):
        _transition(tmp_path, pointers)

    assert tuple(_valid_pointers()) == REQUIRED_RERUN_POINTER_KEYS


def test_character_transition_rejects_non_canonical_required_pointer(tmp_path):
    pointers = _valid_pointers()
    pointers["ledger_head_evidence"] = "reports/local/character_evidence.json:$.heads.ledger"

    transition = _transition(tmp_path, pointers)

    assert transition["hardgate"]["DGT-CHAR-HG1"]["status"] == "fail"
    assert transition["hardgate"]["DGT-CHAR-HG1"]["failed_reason"] == "non-canonical-or-invalid-pointer"
    assert transition["hardgate"]["DGT-CHAR-HG1"]["failed_pointer"] == pointers["ledger_head_evidence"]
    assert transition["discovery_map_signal"]["level_candidate"] == "DN"


def test_character_transition_rejects_existing_drt_substitution(tmp_path):
    pointers = _valid_pointers()
    pointers["drt_rerun_evidence"] = "reports/canonical/discovery-regularized-training.json:$.training_mechanism_cert"
    _write_json(
        tmp_path,
        "reports/canonical/discovery-regularized-training.json",
        {"training_mechanism_cert": {"target_surface": "toy-surface", "character_surface_rerun": False}},
    )

    transition = _transition(tmp_path, pointers)

    assert transition["hardgate"]["DGT-CHAR-HG1"]["status"] == "fail"
    assert transition["hardgate"]["DGT-CHAR-HG1"]["failed_reason"] == "drt-rerun-is-not-character-surface"
    assert transition["discovery_map_signal"]["level_candidate"] == "DN"


def test_character_transition_rejects_existing_drt_in_non_rerun_slot(tmp_path):
    pointers = _valid_pointers()
    pointers["ledger_head_evidence"] = "reports/canonical/existing-drt-evidence.json:$.training_mechanism_cert"
    _write_json(
        tmp_path,
        "reports/canonical/existing-drt-evidence.json",
        {"training_mechanism_cert": {"target_surface": "toy-surface", "character_surface_rerun": False}},
    )

    transition = _transition(tmp_path, pointers)

    assert transition["hardgate"]["DGT-CHAR-HG1"]["status"] == "fail"
    assert transition["hardgate"]["DGT-CHAR-HG1"]["failed_reason"] == "existing-drt-evidence-is-not-character-rerun"
    assert transition["hardgate"]["DGT-CHAR-HG1"]["failed_pointer"] == pointers["ledger_head_evidence"]
    assert transition["discovery_map_signal"]["level_candidate"] == "DN"


def test_character_transition_rejects_character_surface_without_rerun_flag(tmp_path):
    pointers = _valid_pointers()
    pointers["drt_rerun_evidence"] = "reports/canonical/character-surface-drt-disabled.json:$.drt"
    _write_json(
        tmp_path,
        "reports/canonical/character-surface-drt-disabled.json",
        {"drt": {"target_surface": "character-level-lm", "character_surface_rerun": False}},
    )

    transition = _transition(tmp_path, pointers)

    assert transition["hardgate"]["DGT-CHAR-HG1"]["status"] == "fail"
    assert transition["hardgate"]["DGT-CHAR-HG1"]["failed_reason"] == "drt-rerun-is-not-character-surface"
    assert transition["hardgate"]["DGT-CHAR-HG1"]["failed_pointer"] == pointers["drt_rerun_evidence"]
    assert transition["discovery_map_signal"]["level_candidate"] == "DN"


def test_character_transition_requires_net_positive_classifier_delta(tmp_path):
    _write_character_evidence(tmp_path)
    payload_path = tmp_path / "reports/canonical/character_evidence.json"
    payload = json.loads(payload_path.read_text(encoding="utf-8"))
    payload["classifier_surface_delta"]["net_positive_signal"] = False
    payload_path.write_text(json.dumps(payload, sort_keys=True) + "\n", encoding="utf-8")

    transition = build_character_lm_transition(
        toy_antecedent_pointer=None,
        required_rerun_pointers=_valid_pointers(),
        root=tmp_path,
    )

    assert transition["hardgate"]["DGT-CHAR-HG1"]["failed_reason"] == "classifier-surface-delta-not-net-positive"
    assert transition["discovery_map_signal"]["net_positive_signal"] is False
    assert transition["discovery_map_signal"]["level_candidate"] == "DN"


def test_character_transition_is_pointer_only(tmp_path):
    transition = _transition(tmp_path)
    text = json.dumps(transition, sort_keys=True)

    assert transition["status"] == "pass"
    assert transition["discovery_map_signal"]["level_candidate"] == "D4"
    assert transition["discovery_map_signal"]["evidence_pointer"] == _valid_pointers()["classifier_surface_delta"]
    assert "metrics" not in text
    assert "raw_metrics" not in text
    assert ".refactor-loop" not in text
    assert "discovery_projection" not in text


def test_character_transition_demotes_missing_character_evidence_to_dn(tmp_path):
    pointers = _valid_pointers()
    pointers["gap_head_evidence"] = "reports/canonical/character_evidence.json:$.heads.missing"

    transition = _transition(tmp_path, pointers)

    assert transition["status"] == "present-but-fail-closed"
    assert transition["hardgate"]["DGT-CHAR-HG1"]["failed_reason"] == "unresolved-pointer"
    assert transition["hardgate"]["DGT-CHAR-HG1"]["failed_pointer"] == pointers["gap_head_evidence"]
    assert transition["discovery_map_signal"]["level_candidate"] == "DN"


def test_no_character_dgt_sidecar_or_unpinned_dgt_owner_registration():
    root = Path.cwd()
    canonical_runner = (root / "scripts/run_canonical_reports.py").read_text(encoding="utf-8")

    assert CHARACTER_TRANSITION_POINTER == "<dgt-owner>.json:$.character_lm_transition"
    assert "character-dgt" not in canonical_runner
    assert "character_lm_transition" not in canonical_runner
    assert not (root / "reports/canonical/character-dgt.json").exists()
    assert not (root / "reports/canonical/character-dgt.md").exists()
