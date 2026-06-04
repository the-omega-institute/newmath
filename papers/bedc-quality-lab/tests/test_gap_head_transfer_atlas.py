import json

import bedc_quality_lab
from bedc_quality_lab.schema import SCHEMA_ID
from scripts import run_canonical_reports as canonical
from scripts import run_gap_head_transfer_atlas as atlas


def _stats(mean, low=None, high=None):
    low = mean if low is None else low
    high = mean if high is None else high
    return {
        "n": 1,
        "mean": float(mean),
        "std": 0.0,
        "ci95_half_width": 0.0,
        "ci95_low": float(low),
        "ci95_high": float(high),
    }


def _fake_surface_result(spec, status="pass"):
    learned_auroc = _stats(0.92 if status == "pass" else 0.54, 0.90 if status == "pass" else 0.50, 0.94)
    matched_auroc = _stats(0.50, 0.48, 0.52)
    learned_reduction = _stats(0.22 if status == "pass" else 0.01, 0.20 if status == "pass" else -0.02, 0.24)
    matched_reduction = _stats(0.02, 0.00, 0.04)
    hardgates = {
        "A2-HG1": {
            "status": "pass" if status == "pass" else "fail",
            "learned_auroc": learned_auroc,
            "matched_random_auroc": matched_auroc,
        },
        "A2-HG2": {
            "status": "pass" if status == "pass" else "fail",
            "learned_uer_reduction": learned_reduction,
            "matched_random_uer_reduction": matched_reduction,
        },
        "A2-HG3": {"status": "pass", "matched_random_positive": False},
        "A2-HG4": {"status": "pass", "forbidden_column_audit": {"status": "pass"}},
    }
    verdict = atlas._surface_verdict(spec, hardgates)
    return {
        "surface_id": spec.surface_id,
        "label": spec.label,
        "surface_kind": spec.surface_kind,
        "countable_for_multi_surface_d5_o": spec.countable_for_multi_surface_d5_o,
        "sample_count": spec.sample_count,
        "seed_count": len(spec.seeds),
        "seeds": list(spec.seeds),
        "rho": spec.rho,
        "arms": list(atlas.ARMS),
        "transition_kernel": {},
        "latent_distribution": {},
        "mixing": spec.mixing,
        "metrics": {
            "vanilla": {
                "AUROC": _stats(0.50),
                "UnloggedErrorRate": _stats(0.40),
                "CriticalUnloggedErrorRate": _stats(0.20),
                "PredictionErrorRate": _stats(0.30),
            },
            "learned_gap_head_on_h": {
                "AUROC": learned_auroc,
                "UnloggedErrorRate": _stats(0.18),
                "CriticalUnloggedErrorRate": _stats(0.08),
                "PredictionErrorRate": _stats(0.30),
            },
            atlas.producer.MATCHED_RANDOM_ARM: {
                "AUROC": matched_auroc,
                "UnloggedErrorRate": _stats(0.38),
                "CriticalUnloggedErrorRate": _stats(0.18),
                "PredictionErrorRate": _stats(0.30),
            },
        },
        "uer_reduction_vs_vanilla": {
            "learned_gap_head_on_h": learned_reduction,
            atlas.producer.MATCHED_RANDOM_ARM: matched_reduction,
        },
        "MatchedRandomPositive": False,
        "ForbiddenColumnAudit": {"status": "pass"},
        "SurfaceDeltaCount": 2,
        "NetInformation": 0.62,
        "DiscoveryLevel": atlas._discovery_level(spec, verdict),
        "hardgates": hardgates,
        "verdict": verdict,
        "source_evidence": spec.source_evidence(),
    }


def _pointer_value(payload, pointer):
    assert pointer.startswith("$.")
    cursor = payload
    for part in pointer[2:].split("."):
        if isinstance(cursor, dict):
            cursor = cursor[part]
        elif isinstance(cursor, list):
            cursor = cursor[int(part)]
        else:
            raise AssertionError(f"unresolved pointer: {pointer}")
    return cursor


def _collect_named_pointers(value):
    if isinstance(value, dict):
        for key, cell in value.items():
            if (
                key.endswith("_pointer")
                and isinstance(cell, str)
                and (cell.startswith("$.") or ":$." in cell)
            ):
                yield cell
            yield from _collect_named_pointers(cell)
    elif isinstance(value, list):
        for cell in value:
            yield from _collect_named_pointers(cell)


def test_surface_registry_has_thirteen_ordered_surfaces_and_three_arms():
    registry = atlas.surface_registry()

    assert [(spec.surface_id, spec.label) for spec in registry] == [
        ("S0", "clean_gaussian_ou"),
        ("S1", "sample_count_1024"),
        ("S2", "sample_count_256"),
        ("S3", "anisotropic_rho_0p95_0p30"),
        ("S4", "anisotropic_rho_0p90_0p60"),
        ("S5", "laplace_latent"),
        ("S6", "student_t_df3_latent"),
        ("S7", "uniform_latent"),
        ("S8", "generalized_normal_alpha_0p5"),
        ("S9", "generalized_normal_alpha_4"),
        ("S10", "mixing_shift_spiral"),
        ("S11", "mixing_shift_realnvp"),
        ("S12", "optimizer_undertraining"),
    ]
    assert atlas.ARMS == ("vanilla", "learned_gap_head_on_h", "matched_random_gap_head")
    assert registry[0].countable_for_multi_surface_d5_o is False
    assert sum(1 for spec in registry if spec.countable_for_multi_surface_d5_o) == 12


def test_surface_hardgates_cover_a2_hg1_to_hg4():
    metrics = {
        "learned_gap_head_on_h": {"AUROC": _stats(0.90, 0.86, 0.94)},
        atlas.producer.MATCHED_RANDOM_ARM: {"AUROC": _stats(0.50, 0.48, 0.52)},
    }
    reductions = {
        "learned_gap_head_on_h": _stats(0.30, 0.25, 0.35),
        atlas.producer.MATCHED_RANDOM_ARM: _stats(0.04, 0.01, 0.07),
    }

    gates = atlas._surface_hardgates(
        metrics=metrics,
        uer_reductions=reductions,
        forbidden_audit={"status": "pass"},
    )

    assert set(gates) == {"A2-HG1", "A2-HG2", "A2-HG3", "A2-HG4"}
    assert {gate["status"] for gate in gates.values()} == {"pass"}
    assert gates["A2-HG3"]["matched_random_positive"] is False

    failed = atlas._surface_hardgates(
        metrics=metrics,
        uer_reductions={
            "learned_gap_head_on_h": _stats(0.03, 0.01, 0.05),
            atlas.producer.MATCHED_RANDOM_ARM: _stats(0.10, 0.08, 0.12),
        },
        forbidden_audit={"status": "fail"},
    )
    assert failed["A2-HG2"]["status"] == "fail"
    assert failed["A2-HG3"]["matched_random_positive"] is True
    assert failed["A2-HG4"]["status"] == "fail"


def test_payload_records_a2_hg5_to_hg7_boundary_and_prior_evidence(monkeypatch):
    fail_labels = {"laplace_latent", "uniform_latent"}

    def fake_result(spec):
        return _fake_surface_result(spec, "failed" if spec.label in fail_labels else "pass")

    monkeypatch.setattr(atlas, "_surface_result", fake_result)

    payload = atlas.build_payload(run_id="fixture-run", generated_at="fixture-time")

    assert payload["multi_surface_d5_o"]["decision"] == "pass"
    assert payload["multi_surface_d5_o"]["pass_surface_count"] == 10
    assert payload["multi_surface_d5_o"]["clean_surface_counted"] is False
    assert payload["hardgate_evidence"]["A2-HG1"]["status"] == "pass"
    assert payload["hardgate_evidence"]["A2-HG2"]["status"] == "pass"
    assert payload["hardgate_evidence"]["A2-HG3"]["status"] == "pass"
    assert payload["hardgate_evidence"]["A2-HG4"]["status"] == "pass"
    assert payload["hardgate_evidence"]["A2-HG5"]["status"] == "pass"
    assert "clean_gaussian_ou" not in payload["hardgate_evidence"]["A2-HG5"]["pass_surface_ids"]
    assert payload["hardgate_evidence"]["A2-HG6"]["status"] == "pass"
    assert payload["hardgate_evidence"]["A2-HG7"]["status"] == "pass"
    row_by_label = {row["label"]: row for row in payload["boundary_ledger"]}
    assert set(row_by_label) == fail_labels
    assert row_by_label["laplace_latent"]["source_evidence"]["packet_pointer"] == "$.prior_observation_packet"
    assert (
        row_by_label["laplace_latent"]["source_evidence"]["observation_pointer"]
        == "$.prior_observation_packet.observations.laplace_latent"
    )
    assert row_by_label["laplace_latent"]["current_a2_metrics"]["learned_auroc"]["mean"] == 0.54
    for row in payload["boundary_ledger"]:
        pointers = row["evidence_pointer"]
        assert set(pointers) == set(row["failed_gates"])
        for gate in row["failed_gates"]:
            assert _pointer_value(payload, pointers[gate])["status"] == "fail"


def test_hg7_detects_missing_laplace_boundary_row(monkeypatch):
    original_boundary = atlas._boundary_ledger

    def fake_result(spec):
        return _fake_surface_result(spec, "failed" if spec.label == "laplace_latent" else "pass")

    def omit_laplace(surfaces):
        return [row for row in original_boundary(surfaces) if row["label"] != "laplace_latent"]

    monkeypatch.setattr(atlas, "_surface_result", fake_result)
    monkeypatch.setattr(atlas, "_boundary_ledger", omit_laplace)

    payload = atlas.build_payload(run_id="fixture-run", generated_at="fixture-time")

    assert payload["hardgate_evidence"]["A2-HG6"]["status"] == "fail"
    assert payload["hardgate_evidence"]["A2-HG7"]["status"] == "fail"
    assert payload["multi_surface_d5_o"]["decision"] == "failed"
    assert payload["multi_surface_d5_o"]["discovery_level"] == "DN"
    assert set(payload["multi_surface_d5_o"]["failed_gates"]) == {"A2-HG6", "A2-HG7"}


def test_claim_capsule_records_prior_observation_packet_as_not_pass_evidence(monkeypatch):
    monkeypatch.setattr(atlas, "_surface_result", lambda spec: _fake_surface_result(spec, "pass"))
    payload = atlas.build_payload(run_id="fixture-run", generated_at="fixture-time")
    capsule = atlas.build_claim_capsule(payload)

    assert capsule["schema_id"] == "bedc.quality.claim_capsule"
    assert capsule["claim"]["name"] == "multi_surface_d5_o"
    assert capsule["source_evidence"]["status"] == "prior_observation"
    assert capsule["source_evidence"]["counts_as_a2_hg_pass_evidence"] is False
    assert (
        capsule["source_evidence"]["packet_pointer"]
        == f"{atlas.JSON_ARTIFACT}:$.prior_observation_packet"
    )
    assert any(row["label"] == "laplace_latent" for row in capsule["prior_observations"])


def test_source_evidence_pointers_resolve_inside_payload_or_written_tree(tmp_path, monkeypatch):
    def fake_result(spec):
        status = "failed" if spec.label == "laplace_latent" else "pass"
        return _fake_surface_result(spec, status)

    monkeypatch.setattr(atlas, "_surface_result", fake_result)
    payload = atlas.build_payload(run_id="fixture-run", generated_at="fixture-time")
    paths = atlas.write_outputs(payload, root=tmp_path)
    written = json.loads(paths["json"].read_text(encoding="utf-8"))
    capsule = json.loads(paths["claim_capsule"].read_text(encoding="utf-8"))
    source = {
        "payload": written,
        "capsule_source_evidence": capsule["source_evidence"],
        "claim_evidence_pointer": capsule["claim"]["evidence_pointer"],
        "prior_observations": capsule["prior_observations"],
    }

    pointers = set(_collect_named_pointers(source))
    pointers.add(capsule["claim"]["evidence_pointer"])
    for pointer in pointers:
        artifact, _, local_pointer = pointer.partition(":")
        if local_pointer:
            artifact_path = tmp_path / artifact
            assert artifact_path.exists(), pointer
            target_payload = json.loads(artifact_path.read_text(encoding="utf-8"))
            assert _pointer_value(target_payload, local_pointer) is not None
        else:
            assert _pointer_value(written, pointer) is not None


def test_multi_surface_decision_demotes_when_forbidden_column_aggregate_gate_fails(monkeypatch):
    def fake_result(spec):
        surface = _fake_surface_result(spec, "pass")
        if spec.label == "sample_count_1024":
            surface["hardgates"]["A2-HG4"]["status"] = "fail"
            surface["ForbiddenColumnAudit"] = {"status": "fail"}
        return surface

    monkeypatch.setattr(atlas, "_surface_result", fake_result)

    payload = atlas.build_payload(run_id="fixture-run", generated_at="fixture-time")

    assert payload["hardgate_evidence"]["A2-HG5"]["status"] == "pass"
    assert payload["hardgate_evidence"]["A2-HG4"]["status"] == "fail"
    assert payload["multi_surface_d5_o"]["decision"] == "failed"
    assert payload["multi_surface_d5_o"]["discovery_level"] == "DN"
    assert payload["multi_surface_d5_o"]["failed_gates"] == ["A2-HG4"]


def test_write_outputs_keeps_canonical_pointer_and_run_capsule(tmp_path, monkeypatch):
    monkeypatch.setattr(atlas, "_surface_result", lambda spec: _fake_surface_result(spec, "pass"))
    payload = atlas.build_payload(run_id="fixture-run", generated_at="fixture-time")

    paths = atlas.write_outputs(payload, root=tmp_path)

    written = json.loads(paths["json"].read_text(encoding="utf-8"))
    capsule = json.loads(paths["claim_capsule"].read_text(encoding="utf-8"))
    summary = json.loads(paths["summary"].read_text(encoding="utf-8"))
    markdown = paths["report"].read_text(encoding="utf-8")
    assert written["artifact_id"] == atlas.ARTIFACT_ID
    assert capsule["schema_id"] == atlas.CLAIM_CAPSULE_SCHEMA_ID
    assert summary["boundary_ledger"] == written["boundary_ledger"]
    assert "Hardgate evidence pointer" in markdown
    assert "learned AUROC CI-low" not in markdown


def test_canonical_manifest_owns_atlas():
    spec = canonical._specs_by_name()["gap-head-transfer-atlas"]

    assert spec.command == ("python3", "scripts/run_gap_head_transfer_atlas.py")
    assert spec.json_artifact == "reports/canonical/gap_head_transfer_atlas.json"
    assert spec.markdown_artifact == "reports/canonical/gap_head_transfer_atlas.md"
    assert spec.positive_claim_pointer == "$.multi_surface_d5_o"


def test_forbidden_claim_and_package_invariants(monkeypatch):
    monkeypatch.setattr(atlas, "_surface_result", lambda spec: _fake_surface_result(spec, "pass"))
    payload = atlas.build_payload(run_id="fixture-run", generated_at="fixture-time")

    assert payload["forbidden_claim_term_audit"]["status"] == "pass"
    assert "global-quality" not in json.dumps(payload["multi_surface_d5_o"]).lower()
    assert SCHEMA_ID == "bedc-quality-lab:evidence-envelope"
    assert bedc_quality_lab.__all__ == ["QualityEvidenceEnvelope"]


def test_real_surface_smoke_uses_three_arms(monkeypatch):
    spec = atlas.AtlasSurfaceSpec(
        surface_id="S-smoke",
        label="sample_count_smoke",
        surface_kind=atlas.OBSERVED_DEBT_SURFACE_KIND,
        sample_count=96,
        seeds=(11,),
        rho=0.82,
    )

    surface = atlas._surface_result(spec)

    assert surface["arms"] == list(atlas.ARMS)
    assert set(surface["metrics"]) == set(atlas.ARMS)
    assert set(surface["hardgates"]) == {"A2-HG1", "A2-HG2", "A2-HG3", "A2-HG4"}
