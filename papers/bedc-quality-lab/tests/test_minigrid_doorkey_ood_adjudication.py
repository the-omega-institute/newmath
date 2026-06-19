from __future__ import annotations

import json

import pytest

from bedc_quality_lab import minigrid_doorkey_ood_adjudication as ood
from bedc_quality_lab.minigrid_doorkey_families import default_fresh_episode_rows


def _rows() -> list[dict[str, object]]:
    return [dict(row) for row in default_fresh_episode_rows()]


def _publication_rows() -> list[dict[str, object]]:
    rows: list[dict[str, object]] = []
    seeds = (1101, 1102, 1103)
    metrics = {
        "base": (0.50, 0.70, 0.60),
        "bedc": (0.72, 0.72, 0.78),
        "bedc_shuffle_placebo": (0.48, 0.68, 0.55),
    }
    for arm_id, (success, id_success, gap_auc) in metrics.items():
        for episode_index in range(500):
            rows.append(
                {
                    "family_id": "F3",
                    "fresh_env_id": f"doorkey-f3-fresh-{episode_index + 1}",
                    "seed": seeds[episode_index % len(seeds)],
                    "episode_index": episode_index,
                    "arm_id": arm_id,
                    "success": success,
                    "id_success": id_success,
                    "gap_auc": gap_auc,
                }
            )
    return rows


def test_fixture_smoke_payload_is_not_publication_bearing() -> None:
    payload = ood.build_payload(generated_at="fixture")

    ood.validate_payload(payload)
    assert payload["schema_id"] == ood.SCHEMA_ID
    assert payload["execution_mode"] == "fixture-smoke"
    assert payload["hardgate"]["status"] == "fail"
    assert payload["hardgate"]["gates"]["MODE"]["status"] == "pass"
    assert payload["hardgate"]["failed_gates"] == ["F3_COVERAGE"]
    assert payload["verdict"]["status"] == "not_ready"
    assert payload["claim_boundary"]["status"] == "not-publication-bearing"
    assert payload["claim_boundary"]["claim_allowed"] is False


def test_gap_auc_is_diagnostics_only_not_primary_endpoint() -> None:
    payload = ood.build_payload(generated_at="fixture")

    assert payload["config"]["primary_endpoint"] == "f3_fresh_env_success"
    assert payload["claim_boundary"]["primary_endpoint"] == "f3_fresh_env_success"
    assert payload["claim_boundary"]["diagnostics_only"] == ["gap_auc"]


def test_primary_endpoint_uses_paired_lower_bound_against_base_and_placebo() -> None:
    payload = ood.build_payload(generated_at="fixture")
    gate = payload["hardgate"]["gates"]["PRIMARY_ENDPOINT"]

    assert gate["status"] == "pass"
    assert gate["bedc_over_base"]["lower_bound"] >= gate["success_lower_bound"]
    assert gate["bedc_over_shuffle_placebo"]["lower_bound"] >= gate["placebo_lower_bound"]


def test_id_non_regression_failure_blocks_publication_gate() -> None:
    rows = _rows()
    for row in rows:
        if row["arm_id"] == "bedc":
            row["id_success"] = 0.40

    payload = ood.build_payload(generated_at="fixture", observations=rows, execution_mode="publication-bearing")

    assert "ID_NON_REGRESSION" in payload["hardgate"]["failed_gates"]
    assert payload["verdict"]["status"] == "not_ready"
    assert payload["claim_boundary"]["claim_allowed"] is False


def test_publication_bearing_mode_fails_closed_on_fixture_coverage() -> None:
    payload = ood.build_payload(generated_at="fixture", execution_mode="publication-bearing")

    assert payload["execution_mode"] == "publication-bearing"
    assert payload["hardgate"]["status"] == "fail"
    assert "F3_COVERAGE" in payload["hardgate"]["failed_gates"]
    assert payload["claim_boundary"]["status"] == "not-publication-bearing"


def test_publication_bearing_success_authorizes_claim_boundary() -> None:
    payload = ood.build_payload(
        generated_at="fixture",
        observations=_publication_rows(),
        execution_mode="publication-bearing",
    )

    ood.validate_payload(payload)
    assert payload["hardgate"]["status"] == "pass"
    assert payload["hardgate"]["failed_gates"] == []
    assert payload["verdict"]["status"] == "success"
    assert payload["claim_boundary"]["status"] == "publication-bearing"
    assert payload["claim_boundary"]["claim_allowed"] is True
    assert {
        row["arm_id"]: row["fresh_episode_count"]
        for row in payload["arm_summaries"]
    } == {
        "base": 500,
        "bedc": 500,
        "bedc_shuffle_placebo": 500,
    }


def test_missing_arm_fails_closed() -> None:
    rows = [row for row in _rows() if row["arm_id"] != "bedc_shuffle_placebo"]

    payload = ood.build_payload(generated_at="fixture", observations=rows)

    assert "ARMS" in payload["hardgate"]["failed_gates"]
    assert "PRIMARY_ENDPOINT" in payload["hardgate"]["failed_gates"]
    assert payload["claim_boundary"]["claim_allowed"] is False


def test_validate_payload_rejects_gap_auc_primary_endpoint_drift() -> None:
    payload = ood.build_payload(generated_at="fixture")
    payload["config"] = {**payload["config"], "diagnostics_only": []}

    with pytest.raises(ValueError, match="gap_auc"):
        ood.validate_payload(payload)


def test_write_artifacts_outputs_json_markdown_and_fingerprint(tmp_path) -> None:
    payload = ood.write_artifacts(root=tmp_path, generated_at="fixture")

    json_path = tmp_path / ood.JSON_ARTIFACT
    markdown_path = tmp_path / ood.MARKDOWN_ARTIFACT
    fingerprint_path = tmp_path / ood.FINGERPRINT_ARTIFACT
    assert json_path.exists()
    assert markdown_path.exists()
    assert fingerprint_path.exists()
    persisted = json.loads(json_path.read_text(encoding="utf-8"))
    ood.validate_payload(persisted)
    assert persisted["raw_digest"] == payload["raw_digest"]
    assert "# MiniGrid DoorKey OOD Adjudication" in markdown_path.read_text(encoding="utf-8")
    fingerprint = json.loads(fingerprint_path.read_text(encoding="utf-8"))
    assert fingerprint["report_name"] == "minigrid-doorkey-ood-adjudication"
    assert fingerprint["json_artifact"] == ood.JSON_ARTIFACT
    assert fingerprint["reproducibility_mode"] == "fixture-smoke"
