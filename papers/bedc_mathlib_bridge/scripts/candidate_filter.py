#!/usr/bin/env python3
from __future__ import annotations

import argparse
from dataclasses import dataclass
import json
from pathlib import Path
import re
import subprocess
import sys
from typing import Any

from matrix_metadata import MatrixMetadataError, load_rows


DECL_RE = re.compile(
    r"^\s*(?P<private>private\s+)?"
    r"(?:(?:noncomputable|unsafe|partial)\s+)*"
    r"(?P<kind>abbrev|def|theorem|lemma|structure|inductive)\s+"
    r"(?P<name>[A-Za-z_][A-Za-z0-9_']*)\b"
)
NAMESPACE_RE = re.compile(r"^\s*namespace\s+(.+?)\s*$")
END_RE = re.compile(r"^\s*end\s+(.+?)\s*$")
EXPLICIT_TARGET_RE = re.compile(
    r"mathlib[-_ ](?:ref|target)\s*:\s*([A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*)",
    re.IGNORECASE,
)

ANCHOR_PATTERNS = (
    "BHist",
    "BMark",
    "UnaryHistory",
    "NameCert",
    "ProbeBundle",
    "SigRel",
    "BoolHistoryCarrier",
    "IntPairCarrier",
    "NatFactorial",
    "NatBinom",
    "NatGcd",
    "NatDivides",
    "NatDivRem",
    "NatMul",
    "NatAdd",
    "ZMod",
    "GaussInt",
    "GaussEq",
    "EisInt",
    "EisEq",
    "BHistCarrier",
    "ChapterTasteGate",
)
BHIST_ANCHOR_PATTERNS = (
    "BHist",
    "UnaryHistory",
    "NatFactorial",
    "NatBinom",
    "NatGcd",
    "NatDivides",
    "NatDivRem",
    "NatMul",
    "NatAdd",
)
REFUGE_NAME_TERMS = (
    "_StdBridge",
    "StdBridge",
)
GENERIC_TARGET_TERMS = (
    "Repr",
    "ReprAtom",
    "ToString",
    "Hashable",
    "Inhabited",
    "Countable",
    "Denumerable",
    "Infinite",
    "SizeOf",
    "ToExpr",
    "ToJson",
    "FromJson",
    "KVMap",
    "PRange",
    "Rxc",
    "Rxo",
    "Plausible",
    "Arbitrary",
    "Shrinkable",
    "Grind",
)
BOUNDARY_TARGET_TERMS = (
    "Real",
    "Cauchy",
    "Completion",
    "Metric",
    "Topology",
    "Filter",
    "Measure",
    "Padic",
    "riemannZeta",
    "RiemannHypothesis",
    "Differentiable",
    "Complex",
    "Set",
    "Quot",
)
FORBIDDEN_AXIOMS = {"Classical.choice", "Quot.sound", "propext"}
NAT_VALUE_SHAPES = {"pointwise_eq", "nat_sequence_eq", "readback_eq", "bhist_readback"}
REUSABLE_NAT_VALUE_TARGETS = {
    "Nat.choose",
    "Nat.factorial",
    "Nat.fib",
    "Nat.centralBinom",
    "Nat.stirlingFirst",
    "Nat.stirlingSecond",
    "Nat.descFactorial",
    "Nat.superFactorial",
    "Nat.pow",
    "numDerangements",
}
INTERESTING_NAME_TERMS = (
    "bool",
    "bmark",
    "fib",
    "choose",
    "binom",
    "factorial",
    "gcd",
    "zmod",
    "gauss",
    "eis",
    "stirling",
    "catalan",
    "narayana",
    "partition",
    "polygonal",
    "fermat",
    "wilson",
    "crt",
    "padic",
    "real",
    "zeta",
)
TRUE_CARRIER_TERMS = (
    "Carrier",
    "Core",
    "NatFactorial",
    "NatGcd",
    "NatBinom",
    "ZMod",
    "GaussInt",
    "EisInt",
    "BoolCarrier",
)


@dataclass(frozen=True)
class TargetRule:
    names: tuple[str, ...]
    target: str
    mathlib_class: str
    mathlib_instance: str
    shape: str
    reason: str


TARGET_RULES = (
    TargetRule(
        ("BoolCarrier", "BoolClassifierSpec", "BoolEndpoint"),
        "Bool",
        "Bool",
        "Bool",
        "carrier_equiv",
        "bool_carrier_core",
    ),
    TargetRule(
        ("TaggedOptionHistoryCarrier", "TaggedOptionHistoryClassifier"),
        "Option",
        "Option",
        "Option",
        "carrier_equiv",
        "tagged_option_history_core",
    ),
    TargetRule(
        ("SumHistoryCarrier", "SumHistoryClassifier"),
        "Sum",
        "Sum",
        "Sum",
        "carrier_equiv",
        "tagged_sum_history_core",
    ),
    TargetRule(
        ("ListHistoryCarrier", "ListHistoryClassifier"),
        "List",
        "List",
        "List",
        "carrier_equiv",
        "list_history_core",
    ),
    TargetRule(("BoolUp_StdBridge",), "Bool", "Bool", "Bool", "rel_equiv", "bool_stdbridge_refuge"),
    TargetRule(("fib",), "Nat.fib", "Nat.fib", "Nat.fib", "pointwise_eq", "common_name_fib"),
    TargetRule(
        ("bedcChooseNat", "chooseNat", "natChooseFn"),
        "Nat.choose",
        "Nat.choose",
        "Nat.choose",
        "pointwise_eq",
        "common_name_choose",
    ),
    TargetRule(
        ("NatFactorial", "natFactorialFn"),
        "Nat.factorial",
        "Nat.factorial",
        "Nat.factorial",
        "pointwise_eq",
        "bhist_factorial_carrier",
    ),
    TargetRule(
        ("natGcdFn", "NatGcd"),
        "Nat.gcd",
        "Nat.gcd",
        "Nat.gcd",
        "pointwise_eq",
        "bhist_gcd_carrier",
    ),
    TargetRule(("GaussInt",), "GaussianInt", "CommRing", "GaussianInt.instCommRing", "ring_equiv", "gaussian_int_core"),
    TargetRule(
        ("EisInt",),
        "QuadraticAlgebra",
        "CommRing",
        "QuadraticAlgebra.instCommRing",
        "ring_equiv",
        "eisenstein_int_core",
    ),
    TargetRule(("ZMod",), "ZMod", "CommRing", "ZMod.commRing", "carrier_equiv", "zmod_core"),
)


@dataclass
class Decl:
    full_name: str
    terminal: str
    kind: str
    path: Path
    line_no: int
    block: str
    file_text: str
    prior_context: str
    file_clean: str
    file_features: dict[str, bool]


@dataclass
class MatrixIndex:
    used_pairs: set[tuple[str, str]]
    used_mathlib_decls: set[str]
    used_bedc_decls: set[str]
    boundary_decls: set[str]
    boundary_pairs: set[tuple[str, str]]
    generic_pairs: set[tuple[str, str]]
    rows_by_target: dict[str, list[str]]


def strip_line_comments(text: str) -> str:
    return "\n".join(line.split("--", 1)[0] for line in text.splitlines())


def file_may_contain_candidate(text: str, path: Path) -> bool:
    if EXPLICIT_TARGET_RE.search(text):
        return True
    candidate_names = {name for rule in TARGET_RULES for name in rule.names}
    if any(re.search(rf"\b(?:abbrev|def|theorem|lemma|structure|inductive)\s+{re.escape(name)}\b", text) for name in candidate_names):
        return True
    path_lower = path.as_posix().lower()
    return any(
        term in path_lower
        for term in (
            "boolup",
            "factorialup",
            "gcdup",
            "gaussianup",
            "eisensteinup",
            "zmodup",
        )
    )


def file_features(clean_text: str) -> dict[str, bool]:
    return {
        "final_theorem": re.search(
            r"\b(theorem|lemma)\s+[A-Za-z0-9_']*(?:spec|iff|_eq_|RingEquiv|RelEquiv|Equiv|functional|unique|recurrence)\b",
            clean_text,
        )
        is not None,
        "recurrence_cluster": re.search(
            r"\b(theorem|lemma)\s+[A-Za-z0-9_']*(?:recurrence|pascal|succ|zero|one|boundary)\b",
            clean_text,
            re.IGNORECASE,
        )
        is not None,
    }


def candidate_file_pattern() -> str:
    candidate_names = "|".join(
        re.escape(name) for rule in TARGET_RULES for name in rule.names
    )
    return (
        r"mathlib[-_ ](?:ref|target)\s*:"
        + r"|^\s*(?:abbrev|def|theorem|lemma|structure|inductive)\s+(?:"
        + candidate_names
        + r")\b"
    )


def candidate_files(derived_root: Path) -> list[Path]:
    pattern = candidate_file_pattern()
    try:
        result = subprocess.run(
            ["rg", "-l", "-g", "*.lean", pattern, str(derived_root)],
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=False,
        )
    except FileNotFoundError:
        result = None
    if result is not None and result.returncode in {0, 1}:
        return [Path(line) for line in sorted(result.stdout.splitlines()) if line.strip()]
    return [
        path
        for path in sorted(derived_root.rglob("*.lean"))
        if file_may_contain_candidate(path.read_text(encoding="utf-8"), path)
    ]


def find_repo_root() -> Path:
    here = Path(__file__).resolve()
    for parent in (here.parent, *here.parents):
        if (
            (parent / "lean4" / "BEDC" / "Derived").is_dir()
            and (parent / "papers" / "bedc_mathlib_bridge" / "MATRIX.md").is_file()
        ):
            return parent
    raise RuntimeError("cannot locate repository root")


def matrix_path(repo_root: Path) -> Path:
    return repo_root / "papers" / "bedc_mathlib_bridge" / "MATRIX.md"


def load_matrix_index(path: Path) -> MatrixIndex:
    rows = load_rows(path)
    used_pairs: set[tuple[str, str]] = set()
    used_mathlib_decls: set[str] = set()
    used_bedc_decls: set[str] = set()
    boundary_decls: set[str] = set()
    boundary_pairs: set[tuple[str, str]] = set()
    generic_pairs: set[tuple[str, str]] = set()
    rows_by_target: dict[str, list[str]] = {}
    for row in rows:
        meta = row.metadata
        row_id = str(meta.get("row_id", row.cells.get("row_id", "")))
        cls = meta.get("mathlib_class")
        inst = meta.get("mathlib_instance")
        if isinstance(cls, str) and isinstance(inst, str):
            pair = (cls, inst)
            used_pairs.add(pair)
            rows_by_target.setdefault(cls, []).append(row_id)
            rows_by_target.setdefault(inst, []).append(row_id)
            if meta.get("kind") == "measured_boundary":
                boundary_pairs.add(pair)
            if meta.get("kind") == "out_of_scope_generic":
                generic_pairs.add(pair)
        decl = meta.get("mathlib_decl")
        if isinstance(decl, str):
            used_mathlib_decls.add(decl)
            rows_by_target.setdefault(decl, []).append(row_id)
            if meta.get("kind") == "measured_boundary":
                boundary_decls.add(decl)
        bedc = meta.get("bedc_irreducible_decl")
        if isinstance(bedc, str):
            used_bedc_decls.add(bedc)
        consumed = meta.get("bedc_consumed_decl")
        if isinstance(consumed, str):
            used_bedc_decls.add(consumed)
        elif isinstance(consumed, list):
            used_bedc_decls.update(item for item in consumed if isinstance(item, str))
        for footprint_field in ("mathlib_footprint", "bedc_irreducible_footprint"):
            footprint = meta.get(footprint_field)
            if isinstance(footprint, list) and FORBIDDEN_AXIOMS.intersection(footprint):
                if isinstance(decl, str):
                    boundary_decls.add(decl)
                if isinstance(cls, str) and isinstance(inst, str):
                    boundary_pairs.add((cls, inst))
    return MatrixIndex(
        used_pairs=used_pairs,
        used_mathlib_decls=used_mathlib_decls,
        used_bedc_decls=used_bedc_decls,
        boundary_decls=boundary_decls,
        boundary_pairs=boundary_pairs,
        generic_pairs=generic_pairs,
        rows_by_target=rows_by_target,
    )


def scan_decls(derived_root: Path) -> list[Decl]:
    decls: list[Decl] = []
    repo_root = derived_root.parents[2]
    for path in candidate_files(derived_root):
        text = path.read_text(encoding="utf-8")
        if not file_may_contain_candidate(text, path):
            continue
        try:
            display_path = path.relative_to(repo_root)
        except ValueError:
            display_path = path
        clean_text = strip_line_comments(text)
        features = file_features(clean_text)
        lines = text.splitlines()
        namespace_stack: list[str] = []
        starts: list[tuple[int, re.Match[str], tuple[str, ...]]] = []
        for index, line in enumerate(lines):
            ns = NAMESPACE_RE.match(line)
            if ns:
                namespace_stack.append(ns.group(1).strip())
                continue
            end = END_RE.match(line)
            if end and namespace_stack:
                end_name = end.group(1).strip()
                if namespace_stack[-1] == end_name or namespace_stack[-1].endswith("." + end_name):
                    namespace_stack.pop()
                continue
            match = DECL_RE.match(line)
            if match:
                starts.append((index, match, tuple(namespace_stack)))
        for pos, (start, match, ns_stack) in enumerate(starts):
            if match.group("private"):
                continue
            name = match.group("name")
            ns = ".".join(ns_stack)
            full_name = f"{ns}.{name}" if ns else name
            if not full_name.startswith("BEDC.Derived."):
                continue
            end_line = starts[pos + 1][0] if pos + 1 < len(starts) else len(lines)
            block = "\n".join(lines[start:end_line])
            prior = "\n".join(lines[max(0, start - 4) : start])
            decls.append(
                Decl(
                    full_name=full_name,
                    terminal=name,
                    kind=match.group("kind"),
                    path=display_path,
                    line_no=start + 1,
                    block=block,
                    file_text=text,
                    prior_context=prior,
                    file_clean=clean_text,
                    file_features=features,
                )
            )
    return decls


def explicit_target(decl: Decl) -> str | None:
    match = EXPLICIT_TARGET_RE.search(decl.prior_context + "\n" + decl.block[:300])
    if match:
        return match.group(1)
    return None


def rule_for_decl(decl: Decl) -> TargetRule | None:
    for rule in TARGET_RULES:
        if decl.terminal in rule.names:
            return rule
    return None


def target_metadata(decl: Decl) -> tuple[str | None, str | None, str | None, str, str]:
    explicit = explicit_target(decl)
    if explicit:
        return explicit, explicit, explicit, "unknown", "explicit_mathlib_ref"
    rule = rule_for_decl(decl)
    if rule:
        return rule.target, rule.mathlib_class, rule.mathlib_instance, rule.shape, rule.reason
    return None, None, None, "unknown", "no_unique_target_rule"


def is_interesting(decl: Decl, target: str | None) -> bool:
    if target:
        return True
    if EXPLICIT_TARGET_RE.search(decl.prior_context + "\n" + decl.block[:300]):
        return True
    return False


def contains_anchor(text: str) -> bool:
    clean = strip_line_comments(text)
    return any(pattern in clean for pattern in ANCHOR_PATTERNS)


def contains_bhist_anchor(text: str) -> bool:
    clean = strip_line_comments(text)
    return any(pattern in clean for pattern in BHIST_ANCHOR_PATTERNS)


def is_refuge_decl(decl: Decl) -> bool:
    values = (decl.terminal, decl.full_name, decl.path.as_posix())
    return any(term in value for term in REFUGE_NAME_TERMS for value in values)


def is_true_carrier_decl(decl: Decl) -> bool:
    if decl.terminal in {"BoolCarrier", "BoolClassifierSpec", "BoolEndpoint"}:
        return True
    if any(term in decl.terminal for term in TRUE_CARRIER_TERMS) and contains_anchor(decl.block):
        return True
    if decl.kind in {"inductive", "structure"} and contains_bhist_anchor(decl.block):
        return True
    if decl.terminal in {"NatGcd", "NatDivRem", "NatLcm"} and contains_bhist_anchor(decl.block):
        return True
    return False


def source_role(decl: Decl, shape: str) -> str:
    if is_refuge_decl(decl):
        return "stdbridge_refuge"
    if is_true_carrier_decl(decl):
        return "bedc_carrier"
    if shape == "pointwise_eq" and contains_bhist_anchor(decl.block):
        return "bhist_readback"
    if contains_anchor(decl.block):
        return "bedc_anchored_decl"
    return "unanchored_decl"


CONSUMED_DECL_HINTS: dict[str, tuple[str, ...]] = {
    "BEDC.Derived.FactorialUp.NatFactorial": (
        "BEDC.Derived.FactorialUp.natFactorialFn_spec",
        "BEDC.Derived.FactorialUp.natFactorialFn_succ",
    ),
    "BEDC.Derived.GcdUp.NatGcd": (
        "BEDC.Derived.GcdUp.natGcdFn_spec",
        "BEDC.Derived.GcdUp.NatGcd_unique_hsame",
    ),
    "BEDC.Derived.OptionUp.TaggedOptionHistoryCarrier": (
        "BEDC.Derived.OptionUp.TaggedOptionHistoryClassifier_branch_exactness",
        "BEDC.Derived.OptionUp.TaggedOptionHistoryClassifier_stability_fields",
    ),
    "BEDC.Derived.SumUp.SumHistoryCarrier": (
        "BEDC.Derived.SumUp.SumHistoryCarrier_tagged_injections",
        "BEDC.Derived.SumUp.SumHistoryClassifier_trans",
    ),
    "BEDC.Derived.ListUp.ListHistoryCarrier": (
        "BEDC.Derived.ListUp.ListHistoryCarrier_generated_cases",
        "BEDC.Derived.ListUp.ListHistoryClassifierRec_equivalence_fields",
    ),
}


def consumed_decl_hints(decl: Decl) -> list[str]:
    return list(CONSUMED_DECL_HINTS.get(decl.full_name, ()))


def nat_shadow_like(decl: Decl) -> bool:
    clean = strip_line_comments(decl.block)
    if contains_anchor(clean):
        return False
    if re.search(r"\bBHist\b|\bBMark\b|\bUnaryHistory\b|\bNameCert\b", clean):
        return False
    has_natish = re.search(r"\bNat\b|\bInt\b|List\s+Nat", clean) is not None
    has_other_bedc = re.search(r"\bBEDC\.(?!Derived\.(?:FibonacciUp|LucasTheoremUp))", clean) is not None
    return has_natish and not has_other_bedc


def cluster_text(decl: Decl) -> str:
    return decl.file_clean


def has_final_theorem(decl: Decl) -> bool:
    name = re.escape(decl.terminal)
    local = strip_line_comments(decl.block)
    if re.search(
        rf"\b(theorem|lemma)\s+{name}[A-Za-z0-9_']*(?:spec|iff|_eq_|RingEquiv|RelEquiv|Equiv)\b",
        local,
    ):
        return True
    return bool(decl.file_features.get("final_theorem"))


def has_recurrence_cluster(decl: Decl) -> bool:
    name = re.escape(decl.terminal)
    local = strip_line_comments(decl.block)
    if re.search(
        rf"\b(theorem|lemma)\s+{name}[A-Za-z0-9_']*(?:recurrence|pascal|succ|zero|one|boundary)\b",
        local,
        re.IGNORECASE,
    ):
        return True
    return bool(decl.file_features.get("recurrence_cluster"))


def finite_or_canonical_target(target: str | None) -> bool:
    if target is None:
        return False
    return target in {
        "Bool",
        "Option",
        "Sum",
        "Fin",
        "List",
        "ZMod",
        "GaussianInt",
        "QuadraticAlgebra",
        "Int",
    }


def canonical_computable_target(target: str | None) -> bool:
    if target is None:
        return False
    return target in {"Nat.factorial", "Nat.gcd"}


def reusable_target(shape: str | None, target: str | None) -> bool:
    return bool(shape in NAT_VALUE_SHAPES and target in REUSABLE_NAT_VALUE_TARGETS)


def generic_target(target: str | None, cls: str | None, inst: str | None) -> bool:
    values = [value for value in (target, cls, inst) if value]
    return any(any(term in value for term in GENERIC_TARGET_TERMS) for value in values)


def boundary_target(target: str | None, decl: Decl) -> bool:
    values = [target or "", decl.full_name, str(decl.path)]
    return any(any(term in value for term in BOUNDARY_TARGET_TERMS) for value in values)


def small_scope(target: str | None, decl: Decl) -> bool:
    if boundary_target(target, decl):
        return False
    return True


def candidate_score(
    decl: Decl,
    target: str | None,
    shape: str,
    is_generic: bool,
    is_boundary: bool,
    is_nat_shadow: bool,
    is_refuge: bool,
) -> tuple[int, list[str]]:
    score = 0
    reasons: list[str] = []
    if has_final_theorem(decl):
        score += 5
        reasons.append("score:+5_final_spec_iff_or_eq_theorem")
    if is_true_carrier_decl(decl):
        score += 4
        reasons.append("score:+4_true_bedc_carrier_or_relation")
    if finite_or_canonical_target(target):
        score += 4
        reasons.append("score:+4_finite_inductive_or_canonical_target")
    if canonical_computable_target(target):
        score += 3
        reasons.append("score:+3_canonical_computable_mathlib_target")
    if shape in {"equiv", "rel_equiv", "ring_equiv", "relation_iff", "iff", "carrier_equiv"}:
        score += 3
        reasons.append("score:+3_equiv_or_iff_shape")
    if shape == "pointwise_eq" and (has_final_theorem(decl) or has_recurrence_cluster(decl)):
        score += 3
        reasons.append("score:+3_pointwise_eq_with_final_or_recurrence")
    if has_recurrence_cluster(decl):
        score += 2
        reasons.append("score:+2_recurrence_or_boundary_cluster")
    if is_refuge:
        score -= 6
        reasons.append("score:-6_stdbridge_refuge_not_primary_carrier")
    if is_generic:
        score -= 5
        reasons.append("score:-5_generic_typeclass_or_api")
    if is_boundary:
        score -= 8
        reasons.append("score:-8_boundary_or_forbidden_footprint_risk")
    if is_nat_shadow:
        score -= 10
        reasons.append("score:-10_pure_nat_shadow_without_bedc_anchor")
    return score, reasons


def matrix_exclusion(
    index: MatrixIndex,
    decl: Decl,
    target: str | None,
    cls: str | None,
    inst: str | None,
    shape: str | None = None,
) -> tuple[str | None, list[str]]:
    reasons: list[str] = []
    if decl.full_name in index.used_bedc_decls:
        reasons.append("matrix:bedc_decl_already_classified")
        return "matrix_already_classified", reasons
    pair = (cls, inst) if cls and inst else None
    if pair and pair in index.generic_pairs:
        reasons.append("matrix:mathlib_pair_out_of_scope_generic")
        return "generic_mathlib_target", reasons
    if pair and pair in index.boundary_pairs:
        reasons.append("matrix:mathlib_pair_measured_boundary")
        return "boundary_or_forbidden_footprint", reasons
    if target and target in index.boundary_decls:
        reasons.append("matrix:mathlib_decl_measured_boundary")
        return "boundary_or_forbidden_footprint", reasons
    if pair and pair in index.used_pairs and not reusable_target(shape, target):
        reasons.append("matrix:mathlib_class_instance_already_classified")
        return "matrix_already_classified", reasons
    if target and target in index.used_mathlib_decls and not reusable_target(shape, target):
        reasons.append("matrix:mathlib_decl_already_classified")
        return "matrix_already_classified", reasons
    return None, reasons


def raw_candidate(
    decl: Decl,
    index: MatrixIndex,
    min_score: int,
) -> dict[str, Any] | None:
    target, cls, inst, shape, target_reason = target_metadata(decl)
    if not is_interesting(decl, target):
        return None

    reasons: list[str] = [f"source:{decl.path.as_posix()}:{decl.line_no}", f"decl_kind:{decl.kind}"]
    anchor_ok = contains_anchor(decl.block)
    if anchor_ok:
        reasons.append("bedc_anchor:declaration_mentions_bedc_carrier")
    else:
        reasons.append("bedc_anchor:missing_in_declaration")
    if target:
        reasons.append(f"canonical_target:{target_reason}")
        if target in {"Option", "Sum", "List"}:
            reasons.append("canonical_target:constructor_carrier_not_generic_api")
    else:
        reasons.append("canonical_target:no_unique_mathlib_target")
    role = source_role(decl, shape)
    reasons.append(f"source_role:{role}")
    refuge = is_refuge_decl(decl)
    if refuge:
        reasons.append("refuge:stdbridge_internal_bridge_not_primary_carrier")
    if has_recurrence_cluster(decl):
        reasons.append("bedc_cluster:recurrence_or_boundary_theorem_present")

    is_generic = generic_target(target, cls, inst)
    is_boundary = boundary_target(target, decl)
    is_nat_shadow = nat_shadow_like(decl)
    score, score_reasons = candidate_score(
        decl,
        target,
        shape,
        is_generic,
        is_boundary,
        is_nat_shadow,
        refuge,
    )
    reasons.extend(score_reasons)

    exclude_reason, matrix_reasons = matrix_exclusion(index, decl, target, cls, inst, shape)
    reasons.extend(matrix_reasons)
    if exclude_reason is None:
        if target is None:
            exclude_reason = "no_unique_mathlib_target"
        elif is_generic:
            exclude_reason = "generic_mathlib_target"
        elif is_boundary:
            exclude_reason = "boundary_or_forbidden_footprint"
        elif is_nat_shadow:
            exclude_reason = "nat_shadow"
        elif refuge:
            exclude_reason = "stdbridge_refuge"
        elif not anchor_ok and role not in {"bedc_carrier", "bhist_readback"}:
            exclude_reason = "bedc_anchor_missing"
        elif not small_scope(target, decl):
            exclude_reason = "scope_too_large"
        elif score < min_score:
            exclude_reason = "human_review_low_score"

    return {
        "bedc_decl": decl.full_name,
        "mathlib_target_guess": target,
        "mathlib_class_guess": cls,
        "mathlib_instance_guess": inst,
        "correspondence_shape_guess": shape,
        "bedc_consumed_decl_guess": consumed_decl_hints(decl),
        "eligible": exclude_reason is None,
        "score": score,
        "reasons": reasons,
        "exclude_reason": exclude_reason,
    }


def duplicate_filter(candidates: list[dict[str, Any]]) -> None:
    grouped: dict[str, list[dict[str, Any]]] = {}
    for candidate in candidates:
        target = candidate.get("mathlib_target_guess")
        shape = candidate.get("correspondence_shape_guess")
        if reusable_target(shape if isinstance(shape, str) else None, target if isinstance(target, str) else None):
            continue
        if isinstance(target, str) and candidate.get("exclude_reason") not in {
            "matrix_already_classified",
            "generic_mathlib_target",
            "boundary_or_forbidden_footprint",
        }:
            grouped.setdefault(target, []).append(candidate)
    for target_candidates in grouped.values():
        if len(target_candidates) <= 1:
            continue
        target_candidates.sort(
            key=lambda item: (
                item.get("exclude_reason") is None,
                int(item.get("score", 0)),
                -len(str(item.get("bedc_decl", ""))),
            ),
            reverse=True,
        )
        keep = target_candidates[0]
        for candidate in target_candidates[1:]:
            if candidate is keep:
                continue
            candidate["eligible"] = False
            if candidate.get("exclude_reason") is None:
                candidate["exclude_reason"] = "duplicate_candidate_target"
            candidate.setdefault("reasons", []).append(
                f"duplicate_target:preferred={keep['bedc_decl']}"
            )


def sort_candidates(candidates: list[dict[str, Any]]) -> list[dict[str, Any]]:
    def sort_key(item: dict[str, Any]) -> tuple[int, int, int, str]:
        eligible = 1 if item.get("eligible") else 0
        has_target = 1 if item.get("mathlib_target_guess") else 0
        score = int(item.get("score", 0))
        return (-eligible, -score, -has_target, str(item.get("bedc_decl", "")))

    return sorted(candidates, key=sort_key)


def build_candidates(repo_root: Path, min_score: int) -> list[dict[str, Any]]:
    index = load_matrix_index(matrix_path(repo_root))
    derived_root = repo_root / "lean4" / "BEDC" / "Derived"
    candidates = [
        candidate
        for decl in scan_decls(derived_root)
        if (candidate := raw_candidate(decl, index, min_score)) is not None
    ]
    duplicate_filter(candidates)
    return sort_candidates(candidates)


def write_jsonl(candidates: list[dict[str, Any]], out: Path | None) -> None:
    data = "".join(json.dumps(candidate, sort_keys=True) + "\n" for candidate in candidates)
    if out is None:
        print(data, end="")
    else:
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text(data, encoding="utf-8")


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate conservative BEDC to mathlib exported_core bridge candidates."
    )
    parser.add_argument("--out", type=Path, help="write JSONL output to this path")
    parser.add_argument("--top", type=int, help="emit only the top N candidates")
    parser.add_argument("--min-score", type=int, default=7, help="eligibility score threshold")
    return parser.parse_args(argv)


def main(argv: list[str]) -> int:
    args = parse_args(argv)
    if args.top is not None and args.top < 0:
        raise SystemExit("--top must be non-negative")
    try:
        repo_root = find_repo_root()
        candidates = build_candidates(repo_root, args.min_score)
    except (RuntimeError, MatrixMetadataError) as exc:
        print(f"candidate_filter: {exc}", file=sys.stderr)
        return 1
    if args.top is not None:
        candidates = candidates[: args.top]
    write_jsonl(candidates, args.out)
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
