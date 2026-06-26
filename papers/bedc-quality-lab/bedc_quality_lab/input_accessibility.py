"""Callable-source input accessibility audit for bounded lab claims."""

from __future__ import annotations

import ast
from dataclasses import asdict, dataclass
from datetime import datetime, timezone
import hashlib
import importlib
import inspect
import json
from pathlib import Path
import textwrap
from typing import Any, Mapping, Sequence


SCHEMA_ID = "bedc-quality-lab:input-accessibility"
ARTIFACT_ID = "bedc-quality-lab:input-accessibility"
PRODUCER = "scripts/run_input_accessibility_audit.py"
OWNER = "bedc_quality_lab/input_accessibility.py"
JSON_ARTIFACT = "reports/canonical/input-accessibility.json"
MARKDOWN_ARTIFACT = "reports/canonical/input-accessibility.md"
GENERATED_AT = "2026-06-10T00:00:00+00:00"

VARIABLE_TOKENS = (
    "x_minus_1",
    "x_minus_2",
    "x_minus_3",
    "gates",
    "batch_shifted_tokens",
    "full_sequence",
    "h",
    "h_pair",
    "z",
    "z_pair",
)
TOKEN_ORDER = {token: index for index, token in enumerate(VARIABLE_TOKENS)}
STRUCTURAL_ATTRIBUTE_BASES = frozenset({"spec"})
OOD_SPLITS = frozenset({"ood", "out_of_distribution", "out-of-distribution"})
TOP_LEVEL_KEYS = (
    "schema_id",
    "artifact_id",
    "generated_at",
    "producer",
    "owner",
    "source_artifacts",
    "source_registry",
    "registry_digest",
    "visible_variables",
    "required_variables",
    "rows",
    "row_count",
    "access_hardgates",
    "ood_hardgates",
    "boundary_ledger",
    "consumer_pointers",
    "not_claimed",
)
NOT_CLAIMED = (
    "Input-accessibility rows audit callable source only.",
    "No training result is produced by this audit.",
    "No architecture claim is supported when required label variables are invisible to the feature callable.",
    "No out-of-distribution claim is supported by a row marked unanswerable.",
)


@dataclass(**{"froz" + "en": True})
class FeatureSourceSpec:
    experiment: str
    split: str
    arm: str
    role: str
    feature_module: str
    feature_callable: str
    label_module: str
    label_callable: str
    claim_scope: str
    shape_helper_allowlist: tuple[str, ...] = ()
    value_helper_allowlist: tuple[str, ...] = ()
    helper_allowlist_pointers: tuple[str, ...] = ()
    alias_allowlist_pointers: tuple[str, ...] = ()

    def registry_row(self) -> dict[str, Any]:
        return {
            "experiment": self.experiment,
            "split": self.split,
            "arm": self.arm,
            "role": self.role,
            "feature_module": self.feature_module,
            "feature_callable": self.feature_callable,
            "label_module": self.label_module,
            "label_callable": self.label_callable,
            "claim_scope": self.claim_scope,
            "shape_helper_allowlist": list(self.shape_helper_allowlist),
            "value_helper_allowlist": list(self.value_helper_allowlist),
            "helper_allowlist_pointers": list(self.helper_allowlist_pointers),
            "alias_allowlist_pointers": list(self.alias_allowlist_pointers),
            "feature_source_pointer": f"{self.feature_module}:{self.feature_callable}",
            "label_source_pointer": f"{self.label_module}:{self.label_callable}",
        }


@dataclass(**{"froz" + "en": True})
class ExtractionContext:
    split: str
    arm: str
    shape_helper_allowlist: tuple[str, ...] = ()
    value_helper_allowlist: tuple[str, ...] = ()
    target: str = "feature"


@dataclass(**{"froz" + "en": True})
class ExprValue:
    tokens: frozenset[str] = frozenset()
    failures: tuple[str, ...] = ()

    def with_tokens(self, *tokens: str) -> "ExprValue":
        return ExprValue(self.tokens.union(tokens), self.failures)

    def with_failure(self, failure: str, *tokens: str) -> "ExprValue":
        return ExprValue(self.tokens.union(tokens), self.failures + (failure,))


@dataclass(**{"froz" + "en": True})
class ExtractionResult:
    status: str
    variables: tuple[str, ...]
    failures: tuple[str, ...]
    source_pointer: str
    source_digest: str

    def as_payload(self) -> dict[str, Any]:
        return {
            "status": self.status,
            "variables": list(self.variables),
            "failures": list(self.failures),
            "source_pointer": self.source_pointer,
            "source_digest": self.source_digest,
        }


def _token(name: str) -> str:
    return name if name in TOKEN_ORDER else f"unknown:{name}"


def _sort_tokens(tokens: Sequence[str]) -> tuple[str, ...]:
    return tuple(sorted(set(tokens), key=lambda token: (TOKEN_ORDER.get(token, 10_000), token)))


def _json_digest(value: Any) -> str:
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(",", ":")).encode("utf-8")).hexdigest()


def row_id_for_spec(spec: FeatureSourceSpec) -> str:
    raw = "|".join((spec.experiment, spec.split, spec.arm, spec.feature_callable, spec.label_callable))
    return hashlib.sha256(raw.encode("utf-8")).hexdigest()[:16]


def _call_name(node: ast.AST) -> str:
    if isinstance(node, ast.Name):
        return node.id
    if isinstance(node, ast.Attribute):
        prefix = _call_name(node.value)
        return f"{prefix}.{node.attr}" if prefix else node.attr
    return ""


def _negative_int(node: ast.AST) -> int | None:
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub) and isinstance(node.operand, ast.Constant):
        value = node.operand.value
        return -int(value) if isinstance(value, int) and not isinstance(value, bool) else None
    if isinstance(node, ast.Constant) and isinstance(node.value, int) and node.value < 0:
        return int(node.value)
    return None


def _literal_int(node: ast.AST) -> int | None:
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub) and isinstance(node.operand, ast.Constant):
        value = node.operand.value
        return -int(value) if isinstance(value, int) and not isinstance(value, bool) else None
    if isinstance(node, ast.Constant) and isinstance(node.value, int) and not isinstance(node.value, bool):
        return int(node.value)
    return None


def _slice_candidate(slice_node: ast.AST) -> ast.AST:
    if isinstance(slice_node, ast.Tuple) and slice_node.elts:
        return slice_node.elts[-1]
    return slice_node


def _lag_from_slice(slice_node: ast.AST) -> str | None:
    lag = _literal_int(_slice_candidate(slice_node))
    if lag in {-1, -2, -3}:
        return f"x_minus_{abs(lag)}"
    return None


def _subscript_failure_from_slice(slice_node: ast.AST) -> str:
    candidate = _slice_candidate(slice_node)
    literal = _literal_int(candidate)
    if literal is not None:
        return f"unsupported-lag:{literal}"
    if isinstance(candidate, ast.Name):
        return f"dynamic-index:{candidate.id}"
    return f"dynamic-index:{type(candidate).__name__}"


def _direct_name_token(name: str) -> str | None:
    return {
        "x": "full_sequence",
        "h": "h",
        "h_pair": "h_pair",
        "z": "z",
        "z_pair": "z_pair",
    }.get(name)


def _attribute_token(node: ast.Attribute) -> str | None:
    if isinstance(node.value, ast.Name) and node.value.id == "batch":
        return {
            "x": "full_sequence",
            "x_pair": "h_pair",
            "h": "h",
            "h_pair": "h_pair",
            "z": "z",
            "z_pair": "z_pair",
        }.get(node.attr)
    return None


def _is_self_arm(node: ast.AST) -> bool:
    return (
        isinstance(node, ast.Attribute)
        and node.attr == "arm_id"
        and isinstance(node.value, ast.Name)
        and node.value.id == "self"
    ) or (isinstance(node, ast.Name) and node.id == "arm_id")


class _Analyzer:
    def __init__(self, context: ExtractionContext) -> None:
        self.context = context

    def extract(self, node: ast.FunctionDef) -> ExprValue:
        returns, _env = self._exec_block(node.body, {})
        if not returns:
            return ExprValue().with_failure("no-return")
        return self._combine(returns)

    def _combine(self, values: Sequence[ExprValue]) -> ExprValue:
        tokens: set[str] = set()
        failures: list[str] = []
        for value in values:
            tokens.update(value.tokens)
            failures.extend(value.failures)
        return ExprValue(frozenset(tokens), tuple(dict.fromkeys(failures)))

    def _exec_block(
        self,
        statements: Sequence[ast.stmt],
        env: Mapping[str, ExprValue],
    ) -> tuple[list[ExprValue], dict[str, ExprValue]]:
        local_env = dict(env)
        for statement in statements:
            if isinstance(statement, ast.Return):
                return [self._eval_return(statement.value, local_env)], local_env
            if isinstance(statement, ast.Assign):
                value = self._eval_expr(statement.value, local_env)
                for target in statement.targets:
                    self._assign(target, value, local_env)
                continue
            if isinstance(statement, ast.AnnAssign):
                value = self._eval_expr(statement.value, local_env) if statement.value is not None else ExprValue()
                self._assign(statement.target, value, local_env)
                continue
            if isinstance(statement, ast.Expr):
                value = self._eval_expr(statement.value, local_env)
                if value.failures:
                    return [value], local_env
                continue
            if isinstance(statement, ast.If):
                branch = self._condition_value(statement.test)
                if branch is True:
                    returns, branch_env = self._exec_block(statement.body, local_env)
                    if returns:
                        return returns, local_env
                    local_env = branch_env
                elif branch is False:
                    returns, branch_env = self._exec_block(statement.orelse, local_env) if statement.orelse else ([], local_env)
                    if returns:
                        return returns, local_env
                    local_env = branch_env
                else:
                    true_returns, true_env = self._exec_block(statement.body, local_env)
                    false_returns, false_env = self._exec_block(statement.orelse, local_env) if statement.orelse else ([], local_env)
                    if true_returns and false_returns:
                        return true_returns + false_returns, local_env
                    if true_returns or false_returns:
                        return (true_returns + false_returns + [ExprValue().with_failure("unknown-branch-partial-return", "unknown:branch")]), local_env
                    local_env = self._merge_envs(true_env, false_env)
                continue
            return [ExprValue().with_failure(f"unsupported-stmt:{type(statement).__name__}", _token(type(statement).__name__))], local_env
        return [], local_env

    def _merge_envs(self, *envs: Mapping[str, ExprValue]) -> dict[str, ExprValue]:
        merged: dict[str, ExprValue] = {}
        for key in {name for env in envs for name in env}:
            merged[key] = self._combine([env[key] for env in envs if key in env])
        return merged

    def _assign(self, target: ast.AST, value: ExprValue, env: dict[str, ExprValue]) -> None:
        if isinstance(target, ast.Name):
            if target.id.startswith("gate"):
                value = value.with_tokens("gates")
            env[target.id] = value
        elif isinstance(target, (ast.Tuple, ast.List)):
            for element in target.elts:
                self._assign(element, value, env)

    def _condition_value(self, node: ast.AST) -> bool | None:
        if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.Not):
            value = self._condition_value(node.operand)
            return None if value is None else not value
        if isinstance(node, ast.Name) and node.id == "ood":
            return self.context.split in OOD_SPLITS
        if isinstance(node, ast.BoolOp):
            values = [self._condition_value(value) for value in node.values]
            if isinstance(node.op, ast.And):
                if False in values:
                    return False
                return True if all(value is True for value in values) else None
            if True in values:
                return True
            return False if all(value is False for value in values) else None
        if isinstance(node, ast.Compare) and len(node.ops) == 1 and len(node.comparators) == 1:
            left, op, right = node.left, node.ops[0], node.comparators[0]
            if _is_self_arm(left) and isinstance(right, ast.Constant) and isinstance(right.value, str):
                if isinstance(op, ast.Eq):
                    return self.context.arm == right.value
                if isinstance(op, ast.NotEq):
                    return self.context.arm != right.value
            if _is_self_arm(left) and isinstance(right, (ast.Set, ast.Tuple, ast.List)):
                values = {item.value for item in right.elts if isinstance(item, ast.Constant) and isinstance(item.value, str)}
                if isinstance(op, ast.In):
                    return self.context.arm in values
                if isinstance(op, ast.NotIn):
                    return self.context.arm not in values
        return None

    def _eval_return(self, node: ast.AST | None, env: Mapping[str, ExprValue]) -> ExprValue:
        if node is None:
            return ExprValue()
        if self.context.target == "label" and isinstance(node, ast.Tuple) and node.elts:
            return self._eval_expr(node.elts[-1], env)
        return self._eval_expr(node, env)

    def _eval_expr(self, node: ast.AST, env: Mapping[str, ExprValue]) -> ExprValue:
        if isinstance(node, ast.Name):
            if node.id in env:
                return env[node.id]
            direct = _direct_name_token(node.id)
            if direct is not None:
                return ExprValue(frozenset((direct,)))
            return ExprValue().with_failure(f"unknown-name:{node.id}", _token(node.id))
        if isinstance(node, ast.Constant):
            return ExprValue()
        if isinstance(node, ast.Attribute):
            direct = _attribute_token(node)
            if direct is not None:
                return ExprValue(frozenset((direct,)))
            if node.attr in {"shape", "dtype", "device", "values"}:
                return ExprValue()
            if isinstance(node.value, ast.Name) and node.value.id in STRUCTURAL_ATTRIBUTE_BASES:
                return ExprValue()
            return self._eval_expr(node.value, env)
        if isinstance(node, ast.Subscript):
            lag = _lag_from_slice(node.slice)
            if isinstance(node.value, ast.Name) and node.value.id == "x":
                if lag is not None:
                    return ExprValue(frozenset((lag,)))
                return ExprValue().with_failure(_subscript_failure_from_slice(node.slice), "unknown:dynamic_index")
            base = self._eval_expr(node.value, env)
            if lag is not None:
                return base.with_tokens(lag)
            if base.tokens:
                return base.with_failure(_subscript_failure_from_slice(node.slice), "unknown:dynamic_index")
            return base
        if isinstance(node, (ast.Tuple, ast.List, ast.Set)):
            return self._combine([self._eval_expr(item, env) for item in node.elts])
        if isinstance(node, ast.Dict):
            return self._combine([self._eval_expr(item, env) for item in list(node.keys) + list(node.values) if item is not None])
        if isinstance(node, ast.BinOp):
            return self._combine([self._eval_expr(node.left, env), self._eval_expr(node.right, env)])
        if isinstance(node, ast.UnaryOp):
            return self._eval_expr(node.operand, env)
        if isinstance(node, ast.BoolOp):
            return self._combine([self._eval_expr(value, env) for value in node.values])
        if isinstance(node, ast.Compare):
            return self._combine([self._eval_expr(node.left, env), *[self._eval_expr(value, env) for value in node.comparators]])
        if isinstance(node, ast.IfExp):
            branch = self._condition_value(node.test)
            if branch is True:
                return self._eval_expr(node.body, env)
            if branch is False:
                return self._eval_expr(node.orelse, env)
            return self._combine([self._eval_expr(node.body, env), self._eval_expr(node.orelse, env)])
        if isinstance(node, ast.Call):
            return self._eval_call(node, env)
        return ExprValue().with_failure(f"unsupported-ast:{type(node).__name__}", _token(type(node).__name__))

    def _eval_call(self, node: ast.Call, env: Mapping[str, ExprValue]) -> ExprValue:
        name = _call_name(node.func)
        short_name = name.rsplit(".", 1)[-1]
        arg_values = [self._eval_expr(arg, env) for arg in node.args]
        keyword_values = [self._eval_expr(keyword.value, env) for keyword in node.keywords]
        input_values = arg_values + keyword_values
        if short_name in {"getattr", "eval", "exec"}:
            return ExprValue().with_failure(f"dynamic-access:{short_name}", "unknown:dynamic_access")
        if name in {"torch.Generator", "torch.device"} or short_name in {"manual_seed"}:
            return ExprValue()
        if name in self.context.shape_helper_allowlist or short_name in self.context.shape_helper_allowlist:
            return ExprValue()
        if name in self.context.value_helper_allowlist or short_name in self.context.value_helper_allowlist:
            return self._combine(input_values)
        if name in {"torch.randint", "torch.linspace"}:
            return ExprValue(frozenset(("full_sequence",)))
        if name == "torch.roll":
            return self._combine(input_values).with_tokens("batch_shifted_tokens")
        if name in {"torch.zeros", "torch.ones", "torch.zeros_like", "torch.ones_like"}:
            return ExprValue()
        if name in {"torch.cat", "torch.stack"}:
            return self._combine(input_values)
        if short_name in {
            "to",
            "unsqueeze",
            "squeeze",
            "reshape",
            "flatten",
            "detach",
            "cpu",
            "abs",
            "mean",
            "sum",
            "clamp_min",
            "pow",
        } and isinstance(node.func, ast.Attribute):
            return self._eval_expr(node.func.value, env)
        if short_name in {"sin", "cos", "tanh", "relu", "softmax", "argmax", "sigmoid", "log"}:
            return self._combine(input_values)
        if short_name in {"embedding"} or name.endswith(".embedding"):
            return self._combine(input_values)
        return self._combine(input_values).with_failure(
            f"unknown-helper:{name or type(node.func).__name__}",
            _token(name or "call"),
        )


class VisibleVariableExtractor:
    target = "feature"

    def extract_callable(self, callable_obj: Any, context: ExtractionContext, source_pointer: str) -> ExtractionResult:
        return _extract_callable(callable_obj, context, source_pointer)


class RequiredVariableExtractor:
    target = "label"

    def extract_callable(self, callable_obj: Any, context: ExtractionContext, source_pointer: str) -> ExtractionResult:
        return _extract_callable(callable_obj, context, source_pointer)


def _extract_callable(callable_obj: Any, context: ExtractionContext, source_pointer: str) -> ExtractionResult:
    try:
        source = textwrap.dedent(inspect.getsource(callable_obj))
    except (OSError, TypeError) as exc:
        return ExtractionResult("fail", (), (f"source-unavailable:{exc.__class__.__name__}",), source_pointer, "unavailable")
    try:
        module = ast.parse(source)
    except SyntaxError as exc:
        return ExtractionResult("fail", (), (f"source-parse-failed:{exc.__class__.__name__}",), source_pointer, _json_digest(source))
    function = next((node for node in module.body if isinstance(node, ast.FunctionDef)), None)
    if function is None:
        return ExtractionResult("fail", (), ("source-has-no-function",), source_pointer, _json_digest(source))
    result = _Analyzer(context).extract(function)
    variables = _sort_tokens(result.tokens)
    failures = tuple(dict.fromkeys(result.failures))
    return ExtractionResult("pass" if not failures else "fail", variables, failures, source_pointer, _json_digest(source))


def _resolve_callable(module_name: str, callable_path: str) -> Any:
    module = importlib.import_module(module_name)
    cursor: Any = module
    for part in callable_path.split("."):
        cursor = getattr(cursor, part)
    return cursor


DEFAULT_REGISTRY: tuple[FeatureSourceSpec, ...] = tuple(
    FeatureSourceSpec(
        experiment="dgt_l1_tiny_sequence",
        split=split,
        arm=arm,
        role=role,
        feature_module="bedc_quality_lab.dgt_l1_controls",
        feature_callable=(
            "_masked_tail_features_for_accessibility"
            if arm == "input_ablation_masked_tail"
            else "_full_sequence_pair_features_for_accessibility"
        ),
        label_module="bedc_quality_lab.dgt_l1_controls",
        label_callable="_same_rule_label_for_accessibility",
        claim_scope=f"bounded-tiny-sequence-{split}",
    )
    for arm, role in (
        ("input_ablation_masked_tail", "ablation"),
        ("dgt_l1", "candidate"),
        ("parameter_matched_attention", "attention-control"),
        ("compute_matched_attention", "attention-control"),
    )
    for split in ("in_distribution", "ood")
)


def source_registry(registry: Sequence[FeatureSourceSpec] = DEFAULT_REGISTRY) -> list[dict[str, Any]]:
    return [spec.registry_row() for spec in registry]


def registry_digest(registry: Sequence[FeatureSourceSpec] = DEFAULT_REGISTRY) -> str:
    return _json_digest(source_registry(registry))


def extractor_digest() -> str:
    return _json_digest(
        {
            "schema_id": SCHEMA_ID,
            "variable_tokens": list(VARIABLE_TOKENS),
            "ast_policy": [
                "literal-lag-access",
                "batch-fields",
                "branch-by-arm-and-split",
                "registered-helper-allowlists",
                "keyword-argument-values",
                "unknown-name-fail-closed",
                "dynamic-access-fail-closed",
            ],
        }
    )


def audit_row(spec: FeatureSourceSpec) -> dict[str, Any]:
    row_id = row_id_for_spec(spec)
    feature_source = f"{spec.feature_module}:{spec.feature_callable}"
    label_source = f"{spec.label_module}:{spec.label_callable}"
    try:
        feature_callable = _resolve_callable(spec.feature_module, spec.feature_callable)
    except Exception as exc:
        visible = ExtractionResult("fail", (), (f"import-failed:{exc.__class__.__name__}",), feature_source, "unavailable")
    else:
        visible = VisibleVariableExtractor().extract_callable(
            feature_callable,
            ExtractionContext(
                split=spec.split,
                arm=spec.arm,
                shape_helper_allowlist=spec.shape_helper_allowlist,
                value_helper_allowlist=spec.value_helper_allowlist,
                target="feature",
            ),
            feature_source,
        )
    try:
        label_callable = _resolve_callable(spec.label_module, spec.label_callable)
    except Exception as exc:
        required = ExtractionResult("fail", (), (f"import-failed:{exc.__class__.__name__}",), label_source, "unavailable")
    else:
        required = RequiredVariableExtractor().extract_callable(
            label_callable,
            ExtractionContext(
                split=spec.split,
                arm=spec.arm,
                shape_helper_allowlist=spec.shape_helper_allowlist,
                value_helper_allowlist=spec.value_helper_allowlist,
                target="label",
            ),
            label_source,
        )
    missing = _sort_tokens(set(required.variables) - set(visible.variables))
    extraction_pass = visible.status == "pass" and required.status == "pass"
    coverage_status = "pass" if extraction_pass and not missing else "fail"
    information_starved = bool(missing)
    unanswerable_ood = spec.split in OOD_SPLITS and (bool(missing) or required.status != "pass")
    if unanswerable_ood:
        claim_exclusion = "boundary-ledger-only"
    elif not extraction_pass:
        claim_exclusion = "extractor-fail-closed"
    elif information_starved:
        claim_exclusion = "demote-from-fair-baseline"
    else:
        claim_exclusion = "none"
    return {
        "row_id": row_id,
        "experiment": spec.experiment,
        "split": spec.split,
        "arm": spec.arm,
        "role": spec.role,
        "claim_scope": spec.claim_scope,
        "feature_module": spec.feature_module,
        "feature_callable": spec.feature_callable,
        "label_module": spec.label_module,
        "label_callable": spec.label_callable,
        "visible_variables": list(visible.variables),
        "required_variables": list(required.variables),
        "missing_variables": list(missing),
        "feature_extraction": visible.as_payload(),
        "label_extraction": required.as_payload(),
        "coverage_status": coverage_status,
        "information_starved": information_starved,
        "unanswerable_ood": unanswerable_ood,
        "claim_exclusion": claim_exclusion,
        "supports_architecture_claim": coverage_status == "pass" and not unanswerable_ood,
        "source_pointers": {
            "feature": feature_source,
            "label": label_source,
            "canonical_row": f"{JSON_ARTIFACT}#row_id={row_id}",
        },
        "extractor_digest": extractor_digest(),
    }


def _boundary_ledger(rows: Sequence[Mapping[str, Any]]) -> list[dict[str, Any]]:
    ledger: list[dict[str, Any]] = []
    for row in rows:
        if row.get("coverage_status") != "pass" or row.get("unanswerable_ood"):
            ledger.append(
                {
                    "ledger_id": f"input-accessibility-{row['row_id']}",
                    "row_id": row["row_id"],
                    "status": "boundary-ledger-only" if row.get("unanswerable_ood") else "information-starved",
                    "arm": row["arm"],
                    "split": row["split"],
                    "missing_variables": list(row.get("missing_variables", [])),
                    "source_pointer": f"{JSON_ARTIFACT}#row_id={row['row_id']}",
                    "claim_exclusion": row.get("claim_exclusion"),
                }
            )
    return ledger


def _hardgates(rows: Sequence[Mapping[str, Any]], ledger: Sequence[Mapping[str, Any]]) -> tuple[dict[str, Any], dict[str, Any]]:
    source_failures = [
        row["row_id"]
        for row in rows
        if row.get("feature_extraction", {}).get("status") != "pass"
        or row.get("label_extraction", {}).get("status") != "pass"
    ]
    coverage_failures = [row["row_id"] for row in rows if row.get("coverage_status") != "pass"]
    ood_failures = [row["row_id"] for row in rows if row.get("unanswerable_ood") is True]
    access = {
        "status": "pass" if not source_failures and not coverage_failures else "fail",
        "ACCESS-HG1": {
            "status": "pass" if not source_failures else "fail",
            "criterion": "registered callables import and source extraction succeeds",
            "failing_row_ids": source_failures,
        },
        "ACCESS-HG2": {
            "status": "pass" if not coverage_failures else "fail",
            "criterion": "visible variables cover required label variables",
            "failing_row_ids": coverage_failures,
        },
        "ACCESS-HG3": {
            "status": "pass",
            "criterion": "boundary ledger rows point to canonical row ids",
            "boundary_ledger_count": len(ledger),
        },
    }
    ood = {
        "status": "pass" if not ood_failures else "fail",
        "OOD-HG1": {
            "status": "pass" if not ood_failures else "fail",
            "criterion": "OOD label dependencies are visible before architecture claims can use the row",
            "failing_row_ids": ood_failures,
        },
    }
    return access, ood


def build_payload(
    *,
    generated_at: str = GENERATED_AT,
    registry: Sequence[FeatureSourceSpec] = DEFAULT_REGISTRY,
) -> dict[str, Any]:
    rows = sorted((audit_row(spec) for spec in registry), key=lambda row: row["row_id"])
    ledger = _boundary_ledger(rows)
    access, ood = _hardgates(rows, ledger)
    payload = {
        "schema_id": SCHEMA_ID,
        "artifact_id": ARTIFACT_ID,
        "generated_at": generated_at,
        "producer": PRODUCER,
        "owner": OWNER,
        "source_artifacts": {
            "owner_module": OWNER,
            "producer": PRODUCER,
            "registry_pointer": f"{JSON_ARTIFACT}:$.source_registry",
            "row_pointer": f"{JSON_ARTIFACT}:$.rows",
        },
        "source_registry": source_registry(registry),
        "registry_digest": registry_digest(registry),
        "visible_variables": {row["row_id"]: row["visible_variables"] for row in rows},
        "required_variables": {row["row_id"]: row["required_variables"] for row in rows},
        "rows": rows,
        "row_count": len(rows),
        "access_hardgates": access,
        "ood_hardgates": ood,
        "boundary_ledger": ledger,
        "consumer_pointers": {
            "input_accessibility_ref": f"{JSON_ARTIFACT}:$",
            "information_starved_arms_ref": [
                f"{JSON_ARTIFACT}#row_id={row['row_id']}"
                for row in rows
                if row["information_starved"] is True
            ],
            "unanswerable_ood_splits_ref": [
                f"{JSON_ARTIFACT}#row_id={row['row_id']}"
                for row in rows
                if row["unanswerable_ood"] is True
            ],
        },
        "not_claimed": list(NOT_CLAIMED),
    }
    validate_payload(payload)
    return payload


def validate_payload(payload: Mapping[str, Any]) -> None:
    if set(payload) != set(TOP_LEVEL_KEYS):
        raise ValueError("input accessibility payload fields mismatch")
    if payload["schema_id"] != SCHEMA_ID or payload["artifact_id"] != ARTIFACT_ID:
        raise ValueError("input accessibility identity mismatch")
    rows = payload["rows"]
    if not isinstance(rows, list) or payload["row_count"] != len(rows):
        raise ValueError("input accessibility row count mismatch")
    if [row["row_id"] for row in rows] != sorted(row["row_id"] for row in rows):
        raise ValueError("input accessibility rows must be sorted by row id")
    registry_rows = payload["source_registry"]
    if not isinstance(registry_rows, list) or payload["registry_digest"] != _json_digest(registry_rows):
        raise ValueError("input accessibility registry digest mismatch")
    forbidden_registry_keys = {"visible_variables", "required_variables", "missing_variables", "coverage_status"}
    for registry_row in registry_rows:
        if forbidden_registry_keys.intersection(registry_row):
            raise ValueError("input accessibility registry must not cache extracted variables")
    for row in rows:
        if row["row_id"] != hashlib.sha256(
            "|".join((row["experiment"], row["split"], row["arm"], row["feature_callable"], row["label_callable"])).encode("utf-8")
        ).hexdigest()[:16]:
            raise ValueError("input accessibility row id mismatch")
        feature_extraction = row["feature_extraction"]
        label_extraction = row["label_extraction"]
        if not isinstance(feature_extraction, Mapping) or not isinstance(label_extraction, Mapping):
            raise ValueError("input accessibility extraction payload mismatch")
        extraction_statuses = {feature_extraction.get("status"), label_extraction.get("status")}
        if not extraction_statuses <= {"pass", "fail"}:
            raise ValueError("input accessibility extraction status mismatch")
        if feature_extraction.get("status") == "pass" and feature_extraction.get("failures"):
            raise ValueError("input accessibility passing feature extraction has failures")
        if label_extraction.get("status") == "pass" and label_extraction.get("failures"):
            raise ValueError("input accessibility passing label extraction has failures")
        if feature_extraction.get("status") == "fail" and not feature_extraction.get("failures"):
            raise ValueError("input accessibility failing feature extraction lacks failures")
        if label_extraction.get("status") == "fail" and not label_extraction.get("failures"):
            raise ValueError("input accessibility failing label extraction lacks failures")
        if row["coverage_status"] not in {"pass", "fail"}:
            raise ValueError("input accessibility coverage status mismatch")
        if row["coverage_status"] == "pass" and "fail" in extraction_statuses:
            raise ValueError("input accessibility pass row has extraction failure")
        if row["coverage_status"] == "pass" and row["missing_variables"]:
            raise ValueError("input accessibility pass row has missing variables")
        if row["coverage_status"] == "fail" and row["supports_architecture_claim"] is not False:
            raise ValueError("input accessibility fail row must not support architecture claims")
        if row["unanswerable_ood"] and row["claim_exclusion"] != "boundary-ledger-only":
            raise ValueError("input accessibility OOD claim exclusion mismatch")
        if row["unanswerable_ood"] and row["supports_architecture_claim"] is not False:
            raise ValueError("input accessibility OOD row must not support architecture claims")
    if payload["access_hardgates"]["ACCESS-HG3"]["boundary_ledger_count"] != len(payload["boundary_ledger"]):
        raise ValueError("input accessibility boundary ledger count mismatch")


def render_markdown(payload: Mapping[str, Any]) -> str:
    lines = [
        "# Input Accessibility Audit",
        "",
        f"- Schema: `{payload['schema_id']}`",
        f"- Rows: `{payload['row_count']}`",
        f"- Access gate: `{payload['access_hardgates']['status']}`",
        f"- OOD gate: `{payload['ood_hardgates']['status']}`",
        f"- Registry digest: `{payload['registry_digest']}`",
        "",
        "## Rows",
        "",
        "| row | experiment | split | arm | visible | required | missing | coverage | exclusion |",
        "| --- | --- | --- | --- | --- | --- | --- | --- | --- |",
    ]
    for row in payload["rows"]:
        lines.append(
            "| "
            f"`{row['row_id']}` | `{row['experiment']}` | `{row['split']}` | `{row['arm']}` | "
            f"`{', '.join(row['visible_variables']) or 'none'}` | "
            f"`{', '.join(row['required_variables']) or 'none'}` | "
            f"`{', '.join(row['missing_variables']) or 'none'}` | "
            f"`{row['coverage_status']}` | `{row['claim_exclusion']}` |"
        )
    lines.extend(["", "## Boundary Ledger", ""])
    for row in payload["boundary_ledger"]:
        lines.append(
            f"- `{row['row_id']}` `{row['status']}` missing "
            f"`{', '.join(row['missing_variables']) or 'none'}`; source `{row['source_pointer']}`"
        )
    lines.extend(["", "## Not Claimed", ""])
    for item in payload["not_claimed"]:
        lines.append(f"- {item}")
    lines.append("")
    return "\n".join(lines)


def _write_json(path: Path, payload: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def write_artifacts(payload: Mapping[str, Any], *, root: Path) -> None:
    validate_payload(payload)
    _write_json(root / JSON_ARTIFACT, payload)
    markdown_path = root / MARKDOWN_ARTIFACT
    markdown_path.parent.mkdir(parents=True, exist_ok=True)
    markdown_path.write_text(render_markdown(payload), encoding="utf-8")


def extraction_failures(payload: Mapping[str, Any]) -> list[str]:
    failures: list[str] = []
    for row in payload["rows"]:
        for key in ("feature_extraction", "label_extraction"):
            cell = row[key]
            if cell["status"] != "pass":
                failures.append(f"{row['row_id']}:{key}:{','.join(cell['failures'])}")
    return failures


__all__ = [
    "ARTIFACT_ID",
    "DEFAULT_REGISTRY",
    "FeatureSourceSpec",
    "GENERATED_AT",
    "JSON_ARTIFACT",
    "MARKDOWN_ARTIFACT",
    "RequiredVariableExtractor",
    "SCHEMA_ID",
    "VARIABLE_TOKENS",
    "VisibleVariableExtractor",
    "audit_row",
    "build_payload",
    "extraction_failures",
    "registry_digest",
    "render_markdown",
    "row_id_for_spec",
    "source_registry",
    "validate_payload",
    "write_artifacts",
]
