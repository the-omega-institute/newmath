import json
import importlib
from pathlib import Path

import pytest

from bedc_quality_lab import hardgate_inventory
from bedc_quality_lab import metric_purity


L1_GATING_FAMILIES = {
    "FAIR-L1": {
        "FAIR-L1-HG1",
        "FAIR-L1-HG2",
        "FAIR-L1-HG3",
        "FAIR-L1-HG4",
        "FAIR-L1-HG5",
        "FAIR-L1-HG6",
        "FAIR-L1-HG7",
    },
    "L1OOD": {
        "L1OOD-HG1",
        "L1OOD-HG2",
        "L1OOD-HG3",
        "L1OOD-HG4",
        "L1OOD-HG5",
        "L1OOD-HG6",
    },
    "INPUT": {
        "ACCESS-HG1",
        "ACCESS-HG2",
        "ACCESS-HG3",
        "OOD-HG1",
    },
    "WIN": {
        "ORACLE-HG1",
        "ORACLE-HG2",
        "ORACLE-HG3",
        "ORACLE-HG4",
        "ORACLE-HG5",
    },
    "SGS": {
        "POS-HG1",
        "POS-HG2",
        "POS-HG3",
        "POS-HG4",
        "SYM-HG1",
        "SYM-HG2",
        "SYM-HG3",
        "SYM-HG4",
    },
}


def _resolve_owner_pointer(owner_pointer):
    module_name, _, callable_name = owner_pointer.partition(":")
    if not callable_name:
        module_name, _, callable_name = owner_pointer.rpartition(".")
    module_name = module_name.removesuffix(".py").replace("/", ".")
    value = importlib.import_module(module_name)
    for part in callable_name.split("."):
        value = getattr(value, part)
    assert callable(value)
    return value


def test_registered_hardgate_mutations_fail_through_owner_contract():
    cases = metric_purity.iter_registered_hardgate_mutations(Path.cwd())

    assert cases
    for case in cases:
        result = metric_purity.evaluate_hardgate_mutation(Path.cwd(), case)
        assert result["status"] == "pass"
        assert result["failed_gate"] == case.expected_failed_gate
        assert result["restored_owner_status"] == "pass"
        assert result["restored_gate_status"] == "pass"


def test_owner_hardgate_surface_owner_pointers_resolve():
    root = Path.cwd()
    surfaces = hardgate_inventory.iter_promotion_hardgate_surfaces(root)
    win_surface = next(surface for surface in surfaces if surface.family == "WIN")

    assert win_surface.owner_pointer == "bedc_quality_lab/winnability.py:_hardgates"
    for surface in surfaces:
        _resolve_owner_pointer(surface.owner_pointer)


def test_owner_inventory_generates_concrete_hardgate_targets_and_mutations():
    root = Path.cwd()
    inventory_gate_ids = {row.gate_id for row in hardgate_inventory.iter_hardgate_inventory(root)}
    generated_targets_by_id = {row["id"]: row for row in hardgate_inventory.generated_target_rows(root)}
    payload = metric_purity.run_metric_purity_audit(root)
    hardgate_targets = {
        target["id"]
        for target in payload["targets"]
        if target["kind"] == "hardgate" and target["module"] == hardgate_inventory.INVENTORY_MODULE
    }
    hardgate_targets_by_id = {
        target["id"]: target
        for target in payload["targets"]
        if target["kind"] == "hardgate" and target["module"] == hardgate_inventory.INVENTORY_MODULE
    }
    mutation_refs = set(payload["mutation_coverage"]["by_gate"])

    assert inventory_gate_ids
    assert hardgate_targets == inventory_gate_ids
    assert {
        gate_id: target["owner_pointer"]
        for gate_id, target in hardgate_targets_by_id.items()
    } == {
        gate_id: target["owner_pointer"]
        for gate_id, target in generated_targets_by_id.items()
    }
    assert inventory_gate_ids <= mutation_refs
    assert "fair-l1-decision/hardgates" not in hardgate_targets


def test_l1_gating_hardgate_families_are_registered_with_mutation_coverage():
    root = Path.cwd()
    payload = metric_purity.run_metric_purity_audit(root)
    targets = {
        target["id"]: target
        for target in payload["targets"]
        if target["kind"] == "hardgate"
    }
    mutation_results = {
        result["gate_id"]: result
        for result in payload["mutation_coverage"]["results"]
    }

    assert payload["status"] == "pass"
    assert payload["mutation_coverage"]["by_family"] == {
        family: len(gates)
        for family, gates in sorted(L1_GATING_FAMILIES.items())
    } | {
        family: payload["mutation_coverage"]["by_family"][family]
        for family in payload["mutation_coverage"]["by_family"]
        if family not in L1_GATING_FAMILIES
    }
    for family, gate_ids in L1_GATING_FAMILIES.items():
        assert payload["mutation_coverage"]["by_family"][family] >= len(gate_ids)
        for gate_id in gate_ids:
            target = targets[gate_id]
            result = mutation_results[gate_id]
            assert target["family"] == family
            assert target["owner_surface"]
            assert target["owner_pointer"]
            _resolve_owner_pointer(target["owner_pointer"])
            assert target["evidence_pointer"].startswith("reports/canonical/")
            assert result["status"] == "pass"
            assert result["owner_status"] == "fail"
            assert result["failed_gate"] == gate_id
            assert result["restored_owner_status"] == "pass"
            assert result["restored_gate_status"] == "pass"


def test_every_concrete_hardgate_target_has_mutation_row():
    payload = metric_purity.run_metric_purity_audit(Path.cwd())
    hardgate_refs = {
        ref
        for target in payload["targets"]
        if target["kind"] == "hardgate"
        for ref in (target["mutation_contract_refs"] or [target["id"]])
    }

    assert hardgate_refs <= set(payload["mutation_coverage"]["by_gate"])


def test_new_hardgate_without_mutation_row_is_mut_hg1(tmp_path):
    target = {
        "id": "fixture-hardgate",
        "kind": "hardgate",
        "module": "bedc_quality_lab.order_k_benchmark",
        "callable": "OrderKBenchmarkProjection.hardgate_verdicts",
        "owner_pointer": "bedc_quality_lab/order_k_benchmark.py:OrderKBenchmarkProjection.hardgate_verdicts",
        "report_artifact": "reports/canonical/order-k-benchmark.json",
        "evidence_pointer": "reports/canonical/order-k-benchmark.json:$.hardgate",
        "empirical_metric_keys": [],
        "mutation_contract_refs": ["fixture-hardgate"],
        "allowlist_refs": [],
    }
    targets_path = tmp_path / "targets.json"
    allowlist_path = tmp_path / "allowlist.json"
    targets_path.write_text(
        json.dumps({"schema_id": metric_purity.TARGETS_SCHEMA_ID, "targets": [target], "hardgate_mutations": []}) + "\n",
        encoding="utf-8",
    )
    allowlist_path.write_text(json.dumps({"schema_id": metric_purity.ALLOWLIST_SCHEMA_ID, "rows": []}) + "\n", encoding="utf-8")

    payload = metric_purity.run_metric_purity_audit(Path.cwd(), targets_path, allowlist_path)

    assert payload["status"] == "fail"
    assert any(finding["code"] == "MUT-HG1" for finding in payload["findings"])


def test_mutation_output_must_match_expected_gate_and_reason(tmp_path):
    case = metric_purity.iter_registered_hardgate_mutations(Path.cwd())[0]
    wrong = metric_purity.HardgateMutationCase(
        gate_id=case.gate_id,
        mutation_id="wrong-expected-gate",
        owner_pointer=case.owner_pointer,
        apply=case.apply,
        expected_failed_gate="different-gate",
        expected_reason_regex=case.expected_reason_regex,
        source_payload_pointer=case.source_payload_pointer,
        source_payload_factory=case.source_payload_factory,
    )

    result = metric_purity.evaluate_hardgate_mutation(Path.cwd(), wrong)

    assert result["status"] == "fail"
    assert result["code"] == "MUT-HG4"


def test_mutation_apply_failure_is_mut_hg2():
    case = metric_purity.HardgateMutationCase(
        gate_id="FIXTURE-HG1",
        mutation_id="bad-pointer",
        owner_pointer=hardgate_inventory.INVENTORY_OWNER_CALLABLE,
        apply={"delete": ["$.gates.FIXTURE-HG1.missing"]},
        expected_failed_gate="FIXTURE-HG1",
        expected_reason_regex="FIXTURE-HG1",
        source_payload_factory=hardgate_inventory.INVENTORY_SOURCE_FACTORY,
    )

    result = metric_purity.evaluate_hardgate_mutation(Path.cwd(), case)

    assert result["status"] == "fail"
    assert result["code"] == "MUT-HG2"


def test_mutation_owner_exception_is_mut_hg3():
    case = metric_purity.HardgateMutationCase(
        gate_id="FIXTURE-HG1",
        mutation_id="bad-owner",
        owner_pointer="bedc_quality_lab.missing_metric_purity_owner:evaluate",
        apply={"set": {"$.gates.FIXTURE-HG1.status": "fail"}},
        expected_failed_gate="FIXTURE-HG1",
        expected_reason_regex="FIXTURE-HG1",
        source_payload_factory=hardgate_inventory.INVENTORY_SOURCE_FACTORY,
    )

    result = metric_purity.evaluate_hardgate_mutation(Path.cwd(), case)

    assert result["status"] == "fail"
    assert result["code"] == "MUT-HG3"


def test_original_nonpassing_gate_is_mut_hg4(monkeypatch):
    case = metric_purity.HardgateMutationCase(
        gate_id="FIXTURE-HG1",
        mutation_id="original-nonpassing",
        owner_pointer=hardgate_inventory.INVENTORY_OWNER_CALLABLE,
        apply={"set": {"$.gates.FIXTURE-HG1.fail_closed_reason": "mutated"}},
        expected_failed_gate="FIXTURE-HG1",
        expected_reason_regex="FIXTURE-HG1",
        source_payload_factory="bedc_quality_lab.hardgate_inventory:source_payload_for_mutation",
    )
    source = hardgate_inventory.source_payload_for_mutation("FIXTURE-HG1")
    source["gates"]["FIXTURE-HG1"]["status"] = "fail"

    def factory(gate_id):
        assert gate_id == "FIXTURE-HG1"
        return source

    def resolve(pointer):
        if pointer == "bedc_quality_lab.hardgate_inventory:source_payload_for_mutation":
            return factory
        return hardgate_inventory.evaluate_inventory_hardgate_payload

    monkeypatch.setattr(metric_purity, "_resolve_owner_callable", resolve)
    result = metric_purity.evaluate_hardgate_mutation(Path.cwd(), case)
    assert result["status"] == "fail"
    assert result["code"] == "MUT-HG4"
    assert "original gate FIXTURE-HG1 was not passing" in result["reason"]


def test_registered_mutation_iterator_is_deterministic():
    first = metric_purity.iter_registered_hardgate_mutations(Path.cwd())
    second = metric_purity.iter_registered_hardgate_mutations(Path.cwd())

    assert first == second


def test_registered_mutation_iterator_rejects_wrong_target_schema(tmp_path):
    targets_path = tmp_path / "targets.json"
    targets_path.write_text(
        json.dumps({"schema_id": "wrong.schema", "hardgate_mutations": []}) + "\n",
        encoding="utf-8",
    )

    with pytest.raises(ValueError, match=metric_purity.TARGETS_SCHEMA_ID):
        metric_purity.iter_registered_hardgate_mutations(Path.cwd(), targets_path)


def test_mutation_source_must_be_exactly_one_of_pointer_or_factory(tmp_path):
    base_row = {
        "gate_id": "FIXTURE-HG1",
        "mutation_id": "bad-source-contract",
        "owner_pointer": hardgate_inventory.INVENTORY_OWNER_CALLABLE,
        "apply": {"set": {"$.gates.FIXTURE-HG1.status": "fail"}},
        "expected_failed_gate": "FIXTURE-HG1",
        "expected_reason_regex": "FIXTURE-HG1",
    }
    targets_path = tmp_path / "targets.json"
    targets_path.write_text(
        json.dumps(
            {
                "schema_id": metric_purity.TARGETS_SCHEMA_ID,
                "targets": [],
                "hardgate_mutations": [
                    {
                        **base_row,
                        "source_payload_pointer": "reports/canonical/order-k-benchmark.json:$",
                        "source_payload_factory": hardgate_inventory.INVENTORY_SOURCE_FACTORY,
                    },
                    base_row,
                ],
            }
        )
        + "\n",
        encoding="utf-8",
    )

    with pytest.raises(ValueError, match="exactly one"):
        metric_purity.iter_registered_hardgate_mutations(Path.cwd(), targets_path)


def test_promoted_unregistered_gate_fails_closed(tmp_path, monkeypatch):
    root = tmp_path
    artifact = root / "reports" / "canonical" / "fixture-promotion.json"
    artifact.parent.mkdir(parents=True)
    artifact.write_text(
        json.dumps({"hardgates": {"FAIR-L1-HG99": {"gate_id": "FAIR-L1-HG99", "status": "pass"}}}, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    targets_path = root / "targets.json"
    allowlist_path = root / "allowlist.json"
    targets_path.write_text(
        json.dumps(
            {
                "schema_id": metric_purity.TARGETS_SCHEMA_ID,
                "targets": [],
                "hardgate_mutations": [],
            }
        )
        + "\n",
        encoding="utf-8",
    )
    allowlist_path.write_text(json.dumps({"schema_id": metric_purity.ALLOWLIST_SCHEMA_ID, "rows": []}) + "\n", encoding="utf-8")
    surface = hardgate_inventory.HardgateSurface(
        "fixture-promotion",
        "fixture",
        "reports/canonical/fixture-promotion.json",
        "$.hardgates",
        "tests/fixtures/metric_purity/fixture.py:evaluate",
    )
    inventory_row = hardgate_inventory.HardgateInventoryRow(
        gate_id="FAIR-L1-HG99",
        family="fixture",
        surface_id=surface.surface_id,
        artifact=surface.artifact,
        pointer="$.hardgates.FAIR-L1-HG99",
        owner_pointer=surface.owner_pointer,
        row={"gate_id": "FAIR-L1-HG99", "status": "pass"},
    )
    monkeypatch.setattr(metric_purity.hardgate_inventory, "generated_target_rows", lambda root, extra_surfaces=(): ())
    monkeypatch.setattr(metric_purity.hardgate_inventory, "generated_mutation_rows", lambda root, extra_surfaces=(): ())
    monkeypatch.setattr(metric_purity.hardgate_inventory, "iter_promotion_hardgate_surfaces", lambda root, extra_surfaces=(): (surface,))
    monkeypatch.setattr(metric_purity.hardgate_inventory, "iter_hardgate_inventory", lambda root, extra_surfaces=(): (inventory_row,))

    payload = metric_purity.run_metric_purity_audit(root, targets_path, allowlist_path, report_artifacts=["reports/canonical/fixture-promotion.json"])

    assert payload["status"] == "fail"
    assert {
        (finding["code"], finding["symbol"])
        for finding in payload["findings"]
    } >= {("REG-HG1", "FAIR-L1-HG99"), ("MUT-HG1", "FAIR-L1-HG99")}
