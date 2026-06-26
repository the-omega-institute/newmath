from __future__ import annotations

import importlib.util
import json
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT_PATH = REPO_ROOT / "tools" / "bedc_discover_evolve.py"


def _load_module():
    spec = importlib.util.spec_from_file_location("bedc_discover_evolve", SCRIPT_PATH)
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(module)
    return module


def _write_json(root: Path, artifact: str, payload: dict) -> None:
    path = root / artifact
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _root(tmp_path: Path) -> Path:
    _write_json(tmp_path, "reports/canonical/index.json", {"generated_at": "fixture-time"})
    _write_json(tmp_path, "reports/runs/source/claim_capsule.json", {"run_local": {"negative_witness": [{"status": "blocked"}]}})
    _write_json(tmp_path, "reports/canonical/claim_capsule.json", {"status": "complete"})
    _write_json(
        tmp_path,
        "reports/canonical/discovery_negative_witness_summary.json",
        {
            "rows": [
                {
                    "witness_basis_pointer": "reports/runs/source/claim_capsule.json:$.run_local.negative_witness[0]",
                    "claim_capsule_pointer": "reports/canonical/claim_capsule.json:$",
                    "hardgate_pointer": "reports/runs/source/claim_capsule.json:$.run_local.negative_witness[0].status",
                }
            ]
        },
    )
    _write_json(tmp_path, "reports/canonical/discovery_map.json", {"rows": []})
    return tmp_path


def test_dry_run_writes_no_board_or_canonical_artifact(tmp_path: Path, capsys) -> None:
    module = _load_module()
    root = _root(tmp_path)

    rc = module.main(["--root", str(root)])

    assert rc == 0
    payload = json.loads(capsys.readouterr().out)
    assert payload["canonical_role"] == "run_local_not_in_CANONICAL_REPORTS"
    assert payload["queue_admissible_count"] == 1
    assert not (root / "reports/canonical/architecture_mutation_drafts.json").exists()
    assert not (root / "reports/canonical/architecture_mutation_drafts.md").exists()
    assert not (REPO_ROOT / "tools/bedc-deep/BOARD.md.tmp").exists()


def test_output_files_are_written_without_stdout(tmp_path: Path, capsys) -> None:
    module = _load_module()
    root = _root(tmp_path)
    output_json = tmp_path / "run-local" / "architecture_mutation_drafts.json"
    output_md = tmp_path / "run-local" / "architecture_mutation_drafts.md"

    rc = module.main(
        [
            "--root",
            str(root),
            "--output-json",
            str(output_json),
            "--output-md",
            str(output_md),
        ]
    )

    assert rc == 0
    captured = capsys.readouterr()
    assert captured.out == ""
    assert output_json.exists()
    assert output_md.exists()
    payload = json.loads(output_json.read_text(encoding="utf-8"))
    assert payload["canonical_role"] == "run_local_not_in_CANONICAL_REPORTS"
    assert payload["queue_admissible_count"] == 1
    markdown = output_md.read_text(encoding="utf-8")
    assert "# Architecture Mutation Drafts" in markdown
    assert "run_local_not_in_CANONICAL_REPORTS" in markdown


def test_enqueue_uses_compiler_gate_and_board_spawn(monkeypatch, tmp_path: Path, capsys) -> None:
    module = _load_module()
    root = _root(tmp_path)
    calls = {"gate": 0, "spawn": 0}

    original_gate = module.require_witness_basis

    def recording_gate(candidate, gate_root):
        calls["gate"] += 1
        return original_gate(candidate, gate_root)

    class Result:
        ok = True
        accepted = [{"title": "accepted"}]
        appended_ids = ["B-test"]
        rejected = []
        error = ""
        error_kind = ""

    def fake_spawn_from_candidates(*, codex_candidates, oracle_candidates):
        calls["spawn"] += 1
        assert oracle_candidates == []
        assert codex_candidates[0]["kind"] == "architecture_mutation"
        assert codex_candidates[0]["witness_basis_pointer"].startswith("reports/runs/source/")
        return Result()

    monkeypatch.setattr(module, "require_witness_basis", recording_gate)
    import sys
    import types

    fake_board_spawn = types.SimpleNamespace(spawn_from_candidates=fake_spawn_from_candidates)
    monkeypatch.setitem(sys.modules, "board_spawn", fake_board_spawn)

    rc = module.main(["--root", str(root), "--enqueue"])

    assert rc == 0
    payload = json.loads(capsys.readouterr().out)
    assert payload["enqueue_result"]["appended_ids"] == ["B-test"]
    assert calls == {"gate": 1, "spawn": 1}
