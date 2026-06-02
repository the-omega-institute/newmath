import json

import pytest

from scripts import run_gap_head_discovery_stability as runner


def _cell(sample_count, seed_index, positive=True, net=0.5, reason=None):
    return {
        "sample_count": sample_count,
        "seed": sample_count * 100 + seed_index,
        "surface_delta_count": int(positive),
        "shift_information": float(positive),
        "net_information": net,
        "positive_discovery": bool(positive),
        "non_discovery_reason": reason,
        "valid_cell": True,
    }


def _grid(selector):
    return [selector(s, i) for s in runner.SAMPLE_COUNTS for i in range(runner.SEEDS_PER_SAMPLE_COUNT)]


def _verdict():
    return {
        "source_artifacts": {},
        "boundary_checks": {},
        "surface_delta_count": 1,
        "shift_information": 1,
        "net_information": 0.25,
        "structural_discovery": True,
        "positive_discovery": True,
        "net_positive_signal": True,
        "non_discovery_reason": None,
    }


def test_stability_grid_is_fixed_independent_4_by_10():
    configs = runner._cell_configs()
    seed_groups = [{c.seeds[0] for _, _, c in configs if c.sample_count == s} for s in runner.SAMPLE_COUNTS]
    assert len(configs) == 40
    assert runner.GRID_KIND == "independent_seed_grid"
    assert tuple(sorted({c.sample_count for _, _, c in configs})) == runner.SAMPLE_COUNTS
    assert all(len(group) == 10 for group in seed_groups)
    assert len(set.union(*seed_groups)) == 40
    assert all(seed_groups[l].isdisjoint(seed_groups[r]) for l in range(4) for r in range(l + 1, 4))


def test_each_cell_uses_producer_then_existing_discovery_projection(monkeypatch):
    calls = []
    sample_i, seed_i, config = runner._cell_configs()[0]
    monkeypatch.setattr(runner.producer, "_records", lambda c: calls.append("records") or [{"seed": c.seeds[0]}])
    monkeypatch.setattr(runner.producer, "_payload", lambda records, c: calls.append("payload") or {"config": {}, "source_artifacts": {}})
    monkeypatch.setattr(runner.discovery, "_build_gap_head_projection", lambda payload: calls.append("projection") or payload)
    monkeypatch.setattr(runner.discovery, "_verdict_payload", lambda projection: calls.append("verdict") or _verdict())
    row = runner._run_cell(sample_i, seed_i, config)
    assert calls == ["records", "payload", "projection", "verdict"]
    assert row["valid_cell"] is True
    assert row["positive_discovery"] is True
    assert not hasattr(runner, "positive_discovery")
    assert not hasattr(runner, "net_information")


def test_final_verdict_branches():
    largest, mixed = runner.SAMPLE_COUNTS[-1], runner.SAMPLE_COUNTS[1]
    robust = runner._payload(_grid(lambda s, i: _cell(s, i, True, 0.75)), elapsed_seconds=1.0)
    finite = runner._payload(_grid(lambda s, i: _cell(s, i, s != largest, 0.5 if s != largest else -0.2, None if s != largest else "net_information_nonpositive")), elapsed_seconds=1.0)
    noisy = runner._payload(_grid(lambda s, i: _cell(s, i, s != mixed or i < 5, 0.8 if i % 2 == 0 else 0.1, None if s != mixed or i < 5 else "structural_discovery_false")), elapsed_seconds=1.0)
    assert robust["final_verdict"] == "robust_positive"
    assert robust["aggregate"]["sample_count_groups"][0]["positive_rate"] == pytest.approx(1.0)
    assert finite["final_verdict"] == "finite_sample_artifact"
    assert finite["aggregate"]["sample_count_groups"][-1]["positive_rate"] == pytest.approx(0.0)
    assert noisy["final_verdict"] == "seed_dependent_or_noisy"
    assert noisy["aggregate"]["sample_count_groups"][1]["net_information"]["variance"] > 0.0


def test_invalid_grid_verdict():
    cells = _grid(lambda s, i: _cell(s, i, True, 0.75))
    cells[0] = cells[0] | {
        "valid_cell": False,
        "positive_discovery": False,
        "net_positive_signal": False,
        "non_discovery_reason": "invalid_cell:ValueError",
    }
    payload = runner._payload(cells, elapsed_seconds=1.0)

    assert payload["final_verdict"] == "invalid_grid"
    assert payload["aggregate"]["invalid_cell_count"] == 1
    assert payload["aggregate"]["valid_cell_count"] == len(cells) - 1


def test_not_positive_verdict():
    payload = runner._payload(
        _grid(lambda s, i: _cell(s, i, False, -0.1, "net_information_nonpositive")),
        elapsed_seconds=1.0,
    )

    assert payload["final_verdict"] == "not_positive"
    assert payload["aggregate"]["positive_cell_count"] == 0
    assert all(group["positive_seed_count"] == 0 for group in payload["aggregate"]["sample_count_groups"])


def test_payload_validation_fail_closed(monkeypatch):
    sample_i, seed_i, config = runner._cell_configs()[0]
    monkeypatch.setattr(runner.producer, "_records", lambda c: [{"seed": c.seeds[0]}])
    monkeypatch.setattr(runner.producer, "_payload", lambda records, c: {"representation_boundary": "source_h", "records": records})
    row = runner._run_cell(sample_i, seed_i, config)
    assert row["valid_cell"] is False
    assert row["positive_discovery"] is False
    assert row["net_positive_signal"] is False
    assert row["non_discovery_reason"].startswith("invalid_cell:")


def test_json_markdown_same_source(monkeypatch, tmp_path):
    monkeypatch.setattr(runner, "ROOT", tmp_path)
    cells = _grid(lambda s, i: _cell(s, i, True, 0.75))
    monkeypatch.setattr(runner, "_cell_configs", lambda: [(0, 0, object())])
    monkeypatch.setattr(runner, "_run_cell", lambda sample_i, seed_i, config: cells.pop(0))
    runner.main()
    json_text = (tmp_path / runner.JSON_ARTIFACT).read_text(encoding="utf-8")
    payload = json.loads(json_text)
    markdown = (tmp_path / runner.REPORT_ARTIFACT).read_text(encoding="utf-8")
    assert payload["final_verdict"] == "robust_positive"
    assert f"Final verdict: `{payload['final_verdict']}`" in markdown
    assert f"Total cells: `{payload['aggregate']['cell_count']}`" in markdown
    assert "report_schema_id" not in json_text
    assert "report_kind" not in json_text
