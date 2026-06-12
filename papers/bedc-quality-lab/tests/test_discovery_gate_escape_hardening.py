import json
from pathlib import Path

import pytest

from scripts import run_canonical_reports as canonical
from tools import quality_discovery_escape_hardening as hardening


ROOT = Path(__file__).resolve().parents[1]
REGISTRY_PATH = ROOT / hardening.REGISTRY_ARTIFACT
DEMOTIONS_PATH = ROOT / hardening.DEMOTIONS_ARTIFACT


def _walk_keys(value):
    if isinstance(value, dict):
        for key, cell in value.items():
            yield key
            yield from _walk_keys(cell)
    elif isinstance(value, list):
        for cell in value:
            yield from _walk_keys(cell)


def _checked_in_registry():
    return json.loads(REGISTRY_PATH.read_text(encoding="utf-8"))


def _checked_in_demotions():
    return json.loads(DEMOTIONS_PATH.read_text(encoding="utf-8"))


def test_checked_in_registry_is_pointer_only_and_declares_active_kinds():
    payload = _checked_in_registry()

    assert payload["artifact_id"] == "bedc-quality-lab:discovery-gate-escape-registry"
    assert payload["status"] == "pointer-only"
    assert payload["producer"] == "tools/quality_discovery_escape_hardening.py"
    assert payload["active_kinds"] == [
        "mechanism_ablation_fail_but_d5m_claim",
        "scale_only_overclaim",
    ]
    assert [row["kind"] for row in payload["deferred_kinds"]] == [
        "single_threshold_positive_only",
    ]
    assert "metadata_leakage_detector" not in json.dumps(payload, sort_keys=True)
    assert payload["capacity"] == {
        "max_escape_rows": 32,
        "max_rows_per_kind": 4,
        "admission_order": ["kind", "source_pointer", "recipe_pointer", "recipe_digest"],
        "overflow_policy": "fail-closed",
    }
    assert payload["escape_semantics"] == "escaped positive is gate failure evidence, not discovery evidence"

    keys = set(_walk_keys(payload))
    assert keys.isdisjoint(hardening.FORBIDDEN_SIDECAR_FIELDS)
    for forbidden in ("total_score", "rank", "grade", "hidden_cost_weight"):
        assert forbidden not in keys


def test_static_witnesses_remain_fail_closed_under_escape_hardening():
    payload = _checked_in_registry()
    audit = payload["static_witness_audit"]

    assert audit["source"] == "reports/canonical/discovery_negative_witnesses.json"
    assert audit["expected_kind_count"] == 9
    assert audit["fail_closed"] is True
    assert len(audit["witnesses"]) == 9
    assert all(row["fail_closed"] is True for row in audit["witnesses"])
    assert {row["discovery_level"] for row in audit["witnesses"]}.isdisjoint({"D4", "D5-O", "D5-M"})


def test_unmocked_producer_matches_checked_in_escape_sidecars():
    checked_registry = _checked_in_registry()
    checked_demotions = _checked_in_demotions()

    registry = hardening.build_escape_registry(
        root=ROOT,
        generated_at=checked_registry["generated_at"],
    )
    demotions = hardening.build_demotions(
        registry,
        generated_at=checked_demotions["generated_at"],
    )

    assert registry == checked_registry
    assert demotions == checked_demotions


@pytest.mark.parametrize("kind", hardening.ACTIVE_KINDS)
def test_active_pseudo_escape_rows_are_captured(kind):
    payload = _checked_in_registry()
    rows = {row["kind"]: row for row in payload["escaped_rows"]}
    row = rows[kind]

    assert row["escaped"] is True
    assert row["escaped_positive_is_discovery_evidence"] is False
    assert row["terminal_verdict"] == "positive-discovery"
    assert row["recipe_pointer"].startswith("recipe://discovery-gate-escape-hardening/")
    assert len(row["recipe_digest"]) == 64
    assert row["source_pointer"].startswith("reports/canonical/")
    assert row["gate_basis_summary"]["net_positive_signal"] is True
    assert row["gate_basis_summary"]["scorecard_ready"] is True
    assert row["gate_basis_summary"]["forbidden_claim_term_hits"] == []


def test_each_escaped_row_has_exactly_one_proposed_demote_row():
    registry = _checked_in_registry()
    demotions = _checked_in_demotions()

    assert demotions["artifact_id"] == "bedc-quality-lab:discovery-gate-demotions"
    assert demotions["source_registry"] == hardening.REGISTRY_ARTIFACT
    assert len(demotions["demotions"]) == len(registry["escaped_rows"])
    assert len({row["basis_pointer"] for row in demotions["demotions"]}) == len(registry["escaped_rows"])
    for index, row in enumerate(demotions["demotions"]):
        assert row == {
            "gate": "discovery-gate",
            "demote_status": "proposed",
            "basis_pointer": f"{hardening.REGISTRY_ARTIFACT}:$.escaped_rows[{index}]",
            "regression_pointer": (
                "tests/test_discovery_gate_escape_hardening.py::"
                f"test_active_pseudo_escape_rows_are_captured[{registry['escaped_rows'][index]['kind']}]"
            ),
            "source_policy": "witness-registry-and-tests-only",
        }


def test_weak_mock_gate_escape_still_emits_demote_pointer(monkeypatch):
    class Projection:
        discovery_level = "D4"
        reasons = ("mock positive level",)

    def fake_verdict(certificate_payload, evidence_payload, *, timestamp_iso):
        return {
            "verdict": "accepted",
            "reason": "mock-weak-gate",
            "evidence_basis": {"scorecard_ready": True, "net_positive_signal": False},
        }

    monkeypatch.setattr(hardening, "synthesize_certification_verdict", fake_verdict)
    monkeypatch.setattr(hardening, "assign_discovery_level", lambda decision: Projection())

    registry = hardening.build_escape_registry(root=ROOT, generated_at="2030-01-01T00:00:00+00:00")
    demotions = hardening.build_demotions(registry, generated_at=registry["generated_at"])

    assert len(registry["escaped_rows"]) == len(hardening.ACTIVE_KINDS)
    assert {row["terminal_verdict"] for row in registry["escaped_rows"]} == {"accepted"}
    assert {row["discovery_level"] for row in registry["escaped_rows"]} == {"D4"}
    assert len(demotions["demotions"]) == len(registry["escaped_rows"])
    assert all(row["demote_status"] == "proposed" for row in demotions["demotions"])


@pytest.mark.parametrize("discovery_level", ["D5-O", "D5-M"])
def test_d5_split_level_only_projection_is_escaped_positive(monkeypatch, discovery_level):
    candidate = hardening.PseudoCandidate(
        kind="level_only_projection",
        source_pointer="reports/canonical/claim_verdicts.jsonl:0",
        recipe_pointer="recipe://level-only-projection",
        recipe_digest="1" * 64,
        gate="discovery-gate",
        certificate_payload={},
        evidence_payload={},
    )

    class Projection:
        reasons = ("mock level-only projection",)

        def __init__(self, level):
            self.discovery_level = level

    monkeypatch.setattr(
        hardening,
        "synthesize_certification_verdict",
        lambda certificate_payload, evidence_payload, *, timestamp_iso: {
            "verdict": "accepted",
            "reason": "mock-level-only",
            "evidence_basis": {},
        },
    )
    monkeypatch.setattr(hardening, "assign_discovery_level", lambda decision: Projection(discovery_level))

    row = hardening._evaluate_candidate(candidate)

    assert row["escaped"] is True
    assert row["escaped_positive_is_discovery_evidence"] is False
    assert row["terminal_verdict"] == "accepted"
    assert row["discovery_level"] == discovery_level


def test_capacity_overflow_fails_closed_with_deterministic_admission(monkeypatch):
    base = hardening.PseudoCandidate(
        kind="mechanism_ablation_fail_but_d5m_claim",
        source_pointer="reports/canonical/claim_verdicts.jsonl:0",
        recipe_pointer="recipe://overflow",
        recipe_digest="0" * 64,
        gate="discovery-gate",
        certificate_payload={},
        evidence_payload={},
    )
    candidates = [
        hardening.PseudoCandidate(
            kind=base.kind,
            source_pointer=base.source_pointer,
            recipe_pointer=f"{base.recipe_pointer}-{index}",
            recipe_digest=f"{index:064x}"[-64:],
            gate=base.gate,
            certificate_payload=base.certificate_payload,
            evidence_payload=base.evidence_payload,
        )
        for index in range(hardening.MAX_ROWS_PER_KIND + 1)
    ]

    class Projection:
        discovery_level = "D4"
        reasons = ("mock overflow",)

    monkeypatch.setattr(hardening, "pseudo_candidates", lambda root: candidates)
    monkeypatch.setattr(
        hardening,
        "synthesize_certification_verdict",
        lambda certificate_payload, evidence_payload, *, timestamp_iso: {
            "verdict": "accepted",
            "reason": "mock-overflow",
            "evidence_basis": {},
        },
    )
    monkeypatch.setattr(hardening, "assign_discovery_level", lambda decision: Projection())

    with pytest.raises(RuntimeError, match="max_rows_per_kind"):
        hardening.build_escape_registry(root=ROOT)


def test_global_escape_capacity_overflow_fails_closed(monkeypatch):
    candidates = [
        hardening.PseudoCandidate(
            kind=f"overflow_kind_{index // hardening.MAX_ROWS_PER_KIND:02d}",
            source_pointer=f"reports/canonical/claim_verdicts.jsonl:{index}",
            recipe_pointer=f"recipe://global-overflow/{index:02d}",
            recipe_digest=f"{index:064x}"[-64:],
            gate="discovery-gate",
            certificate_payload={},
            evidence_payload={},
        )
        for index in range(hardening.MAX_ESCAPE_ROWS + 1)
    ]

    class Projection:
        discovery_level = "D4"
        reasons = ("mock global overflow",)

    monkeypatch.setattr(hardening, "pseudo_candidates", lambda root: candidates)
    monkeypatch.setattr(
        hardening,
        "synthesize_certification_verdict",
        lambda certificate_payload, evidence_payload, *, timestamp_iso: {
            "verdict": "accepted",
            "reason": "mock-global-overflow",
            "evidence_basis": {},
        },
    )
    monkeypatch.setattr(hardening, "assign_discovery_level", lambda decision: Projection())

    with pytest.raises(RuntimeError, match=r"max_escape_rows=32"):
        hardening.build_escape_registry(root=ROOT)


def test_sidecars_stay_out_of_canonical_reports_and_source_schema_exports():
    json_artifacts = {spec.json_artifact for spec in canonical.CANONICAL_REPORTS}

    assert hardening.REGISTRY_ARTIFACT not in json_artifacts
    assert hardening.DEMOTIONS_ARTIFACT not in json_artifacts
    assert "escape_registry" not in {Path(spec.json_artifact).stem for spec in canonical.CANONICAL_REPORTS}
    assert "gate_demotions" not in {Path(spec.json_artifact).stem for spec in canonical.CANONICAL_REPORTS}

    import bedc_quality_lab
    from bedc_quality_lab.schema import SCHEMA_ID

    assert bedc_quality_lab.__all__ == ["QualityEvidenceEnvelope"]
    assert SCHEMA_ID == "bedc-quality-lab:evidence-envelope"


def test_write_scope_is_limited_to_two_sidecars(tmp_path, monkeypatch):
    writes = []

    def fake_write(target, payload):
        writes.append(target.relative_to(tmp_path).as_posix())

    monkeypatch.setattr(hardening, "_write_json", fake_write)
    registry, demotions = hardening.write_sidecars(root=tmp_path, generated_at="2030-01-01T00:00:00+00:00")

    assert writes == [hardening.REGISTRY_ARTIFACT, hardening.DEMOTIONS_ARTIFACT]
    assert len(demotions["demotions"]) == len(registry["escaped_rows"])


def test_write_sidecars_reuses_existing_registry_timestamp(tmp_path):
    sentinel = "2027-07-07T07:07:07+00:00"
    registry_path = tmp_path / hardening.REGISTRY_ARTIFACT
    registry_path.parent.mkdir(parents=True)
    registry_path.write_text(json.dumps({"generated_at": sentinel}) + "\n", encoding="utf-8")

    registry, demotions = hardening.write_sidecars(root=tmp_path)

    written_registry = json.loads(registry_path.read_text(encoding="utf-8"))
    written_demotions = json.loads((tmp_path / hardening.DEMOTIONS_ARTIFACT).read_text(encoding="utf-8"))
    written_files = sorted(path.relative_to(tmp_path).as_posix() for path in tmp_path.rglob("*") if path.is_file())

    assert registry["generated_at"] == sentinel
    assert demotions["generated_at"] == sentinel
    assert written_registry["generated_at"] == sentinel
    assert written_demotions["generated_at"] == sentinel
    assert written_files == [hardening.DEMOTIONS_ARTIFACT, hardening.REGISTRY_ARTIFACT]
