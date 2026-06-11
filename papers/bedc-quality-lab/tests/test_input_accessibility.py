import json

from bedc_quality_lab import input_accessibility as ia
from scripts import run_input_accessibility_audit as runner


def literal_lag_features(x):
    return x[:, -1] + x[:, -2]


def batch_features(batch):
    return batch.x + batch.x_pair


def z_features(z, z_pair):
    return z + z_pair


def helper_shape_only(x):
    return x.shape[0]


def helper_feature(x):
    pad = helper_shape_only(x)
    return x[:, -1] + pad


def unknown_helper_feature(x):
    return custom_value_helper(x[:, -1])


def custom_value_helper(value):
    return value


def dynamic_feature(x, name):
    return getattr(x, name)


def token_lag_label(x):
    y = x[:, -3]
    return x, y


def _extract(callable_obj, *, target="feature", split="in_distribution", arm="fixture_arm", shape_helpers=()):
    context = ia.ExtractionContext(
        split=split,
        arm=arm,
        shape_helper_allowlist=tuple(shape_helpers),
        target=target,
    )
    return ia.VisibleVariableExtractor().extract_callable(callable_obj, context, "fixture:callable")


def test_extractor_accepts_literal_lag_variables_and_token_lag_subscripts():
    feature = _extract(literal_lag_features)
    label = ia.RequiredVariableExtractor().extract_callable(
        token_lag_label,
        ia.ExtractionContext(split="in_distribution", arm="fixture_arm", target="label"),
        "fixture:label",
    )

    assert feature.status == "pass"
    assert feature.variables == ("x_minus_1", "x_minus_2")
    assert label.status == "pass"
    assert label.variables == ("x_minus_3",)


def test_extractor_accepts_batch_fields_and_z_tokens():
    batch = _extract(batch_features)
    z = _extract(z_features)

    assert batch.status == "pass"
    assert batch.variables == ("full_sequence", "h_pair")
    assert z.status == "pass"
    assert z.variables == ("z", "z_pair")


def test_shape_helper_allowlist_is_not_treated_as_feature_access():
    result = _extract(helper_feature, shape_helpers=("helper_shape_only",))

    assert result.status == "pass"
    assert result.variables == ("x_minus_1",)


def test_unknown_helper_and_dynamic_access_fail_closed():
    unknown = _extract(unknown_helper_feature)
    dynamic = _extract(dynamic_feature)

    assert unknown.status == "fail"
    assert unknown.variables == ("x_minus_1", "unknown:custom_value_helper")
    assert unknown.failures == ("unknown-helper:custom_value_helper",)
    assert dynamic.status == "fail"
    assert dynamic.variables == ("unknown:dynamic_access",)
    assert dynamic.failures == ("dynamic-access:getattr",)


def test_registry_rows_contain_only_callable_pointers():
    rows = ia.source_registry()
    serialized = json.dumps(rows, sort_keys=True)

    assert rows
    assert all(row["feature_source_pointer"].startswith("bedc_quality_lab.") for row in rows)
    assert all(row["label_source_pointer"].startswith("bedc_quality_lab.") for row in rows)
    assert "visible_variables" not in serialized
    assert "required_variables" not in serialized
    assert ia.registry_digest() == ia.registry_digest()


def test_rows_are_sorted_and_row_id_is_stable():
    payload = ia.build_payload(generated_at="fixture-time")
    row_ids = [row["row_id"] for row in payload["rows"]]
    first_spec = ia.DEFAULT_REGISTRY[0]

    assert row_ids == sorted(row_ids)
    assert ia.row_id_for_spec(first_spec) in row_ids
    assert ia.row_id_for_spec(first_spec) == ia.row_id_for_spec(first_spec)
    ia.validate_payload(payload)


def test_real_callable_audit_builds_canonical_payload():
    payload = ia.build_payload(generated_at="fixture-time")

    assert payload["schema_id"] == ia.SCHEMA_ID
    assert payload["artifact_id"] == ia.ARTIFACT_ID
    assert payload["row_count"] == len(ia.DEFAULT_REGISTRY)
    assert payload["access_hardgates"]["status"] == "fail"
    assert payload["boundary_ledger"]
    assert payload["consumer_pointers"]["input_accessibility_ref"] == f"{ia.JSON_ARTIFACT}:$"


def test_producer_writes_idempotent_artifacts_even_when_gate_fails_closed(tmp_path):
    payload = ia.build_payload(generated_at=ia.GENERATED_AT)
    ia.write_artifacts(payload, root=tmp_path)
    first = {
        ia.JSON_ARTIFACT: (tmp_path / ia.JSON_ARTIFACT).read_bytes(),
        ia.MARKDOWN_ARTIFACT: (tmp_path / ia.MARKDOWN_ARTIFACT).read_bytes(),
    }

    payload = ia.build_payload(generated_at=ia.GENERATED_AT)
    ia.write_artifacts(payload, root=tmp_path)
    second = {
        ia.JSON_ARTIFACT: (tmp_path / ia.JSON_ARTIFACT).read_bytes(),
        ia.MARKDOWN_ARTIFACT: (tmp_path / ia.MARKDOWN_ARTIFACT).read_bytes(),
    }

    assert first == second


def test_cli_writes_payload_when_coverage_gate_fails_closed(tmp_path, capsys):
    status = runner.main(["--root", str(tmp_path), "--generated-at", "fixture-time"])
    output = json.loads(capsys.readouterr().out)

    assert status == 0
    assert output["artifact_id"] == ia.ARTIFACT_ID
    assert output["row_count"] == len(ia.DEFAULT_REGISTRY)
    assert (tmp_path / ia.JSON_ARTIFACT).exists()
    assert (tmp_path / ia.MARKDOWN_ARTIFACT).exists()
