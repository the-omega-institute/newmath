import json

from bedc_quality_lab import input_accessibility as ia
from scripts import run_input_accessibility_audit as runner


def literal_lag_features(x):
    return x[:, -1] + x[:, -2]


def single_lag_feature(x):
    return x[:, -1]


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


def dynamic_index_feature(x, lag):
    return x[:, lag]


def dynamic_index_label(x, lag):
    y = x[:, lag]
    return x, y


def hidden_name_label(x, hidden_dependency):
    return x, hidden_dependency


def keyword_label(x, torch):
    y = torch.stack(tensors=[x[:, -2]])
    return x, y


def loop_feature(x):
    out = None
    for lag in (-2,):
        out = x[:, lag]
    return out


def loop_label(x):
    y = None
    for lag in (-2,):
        y = x[:, lag]
    return x, y


def branch_assign_feature(x, flag):
    if flag:
        first = x[:, -1]
    else:
        first = x[:, -2]
    return first


def tuple_unpack_feature(x):
    first, second = x[:, -1], x[:, -2]
    return first + second


def unsupported_lag_feature(x):
    return x[:, -4]


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


def test_dynamic_and_unsupported_lag_subscripts_fail_closed():
    dynamic_feature_result = _extract(dynamic_index_feature)
    dynamic_label_result = ia.RequiredVariableExtractor().extract_callable(
        dynamic_index_label,
        ia.ExtractionContext(split="in_distribution", arm="fixture_arm", target="label"),
        "fixture:dynamic_index_label",
    )
    unsupported = _extract(unsupported_lag_feature)

    assert dynamic_feature_result.status == "fail"
    assert dynamic_feature_result.variables == ("unknown:dynamic_index",)
    assert dynamic_feature_result.failures == ("dynamic-index:lag",)
    assert dynamic_label_result.status == "fail"
    assert dynamic_label_result.variables == ("unknown:dynamic_index",)
    assert dynamic_label_result.failures == ("dynamic-index:lag",)
    assert unsupported.status == "fail"
    assert unsupported.variables == ("unknown:dynamic_index",)
    assert unsupported.failures == ("unsupported-lag:-4",)


def test_dynamic_index_row_cannot_support_architecture_claim():
    spec = ia.FeatureSourceSpec(
        experiment="repro",
        split="in_distribution",
        arm="dynamic-index",
        role="candidate",
        feature_module=__name__,
        feature_callable="dynamic_index_feature",
        label_module=__name__,
        label_callable="dynamic_index_label",
        claim_scope="repro",
    )
    payload = ia.build_payload(generated_at="fixture-time", registry=(spec,))
    row = payload["rows"][0]

    assert payload["access_hardgates"]["status"] == "fail"
    assert row["coverage_status"] == "fail"
    assert row["claim_exclusion"] == "extractor-fail-closed"
    assert row["supports_architecture_claim"] is False
    assert row["feature_extraction"]["failures"] == ["dynamic-index:lag"]
    ia.validate_payload(payload)

    row["coverage_status"] = "pass"
    row["supports_architecture_claim"] = True
    try:
        ia.validate_payload(payload)
    except ValueError as exc:
        assert str(exc) == "input accessibility pass row has extraction failure"
    else:
        raise AssertionError("dynamic-index extraction failure must not validate as coverage pass")


def test_unknown_name_label_dependency_fails_closed_in_row():
    spec = ia.FeatureSourceSpec(
        experiment="repro",
        split="in_distribution",
        arm="unknown-name",
        role="candidate",
        feature_module=__name__,
        feature_callable="literal_lag_features",
        label_module=__name__,
        label_callable="hidden_name_label",
        claim_scope="repro",
    )
    row = ia.build_payload(generated_at="fixture-time", registry=(spec,))["rows"][0]

    assert row["required_variables"] == ["unknown:hidden_dependency"]
    assert row["coverage_status"] == "fail"
    assert row["supports_architecture_claim"] is False
    assert row["label_extraction"]["failures"] == ["unknown-name:hidden_dependency"]


def test_keyword_call_values_are_included_in_required_variables():
    spec = ia.FeatureSourceSpec(
        experiment="repro",
        split="in_distribution",
        arm="keyword",
        role="candidate",
        feature_module=__name__,
        feature_callable="single_lag_feature",
        label_module=__name__,
        label_callable="keyword_label",
        claim_scope="repro",
    )
    row = ia.build_payload(generated_at="fixture-time", registry=(spec,))["rows"][0]

    assert row["required_variables"] == ["x_minus_2"]
    assert row["missing_variables"] == ["x_minus_2"]
    assert row["coverage_status"] == "fail"
    assert row["supports_architecture_claim"] is False


def test_unsupported_statement_nodes_fail_closed_in_rows():
    spec = ia.FeatureSourceSpec(
        experiment="repro",
        split="in_distribution",
        arm="loop",
        role="candidate",
        feature_module=__name__,
        feature_callable="loop_feature",
        label_module=__name__,
        label_callable="loop_label",
        claim_scope="repro",
    )
    payload = ia.build_payload(generated_at="fixture-time", registry=(spec,))
    row = payload["rows"][0]

    assert row["feature_extraction"]["status"] == "fail"
    assert row["feature_extraction"]["failures"] == ["unsupported-stmt:For"]
    assert row["label_extraction"]["status"] == "fail"
    assert row["label_extraction"]["failures"] == ["unsupported-stmt:For"]
    assert row["coverage_status"] == "fail"
    assert row["supports_architecture_claim"] is False
    assert payload["access_hardgates"]["status"] == "fail"


def test_unknown_branch_assignment_keeps_union_of_branch_evidence():
    result = _extract(branch_assign_feature)

    assert result.status == "pass"
    assert result.variables == ("x_minus_1", "x_minus_2")


def test_tuple_unpack_assignment_keeps_visible_evidence():
    result = _extract(tuple_unpack_feature)

    assert result.status == "pass"
    assert result.variables == ("x_minus_1", "x_minus_2")


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
