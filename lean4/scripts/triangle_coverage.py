#!/usr/bin/env python3
"""BEDC Triangle Coverage Harness.

This host-owned CI gate reads Lean sources and checks that advertised triangle
coverage is routed through Lean declarations.

The harness has three layers:

* Layer 1 is an informational survey.  It finds the TGS universe by scanning
  for files that import ``TriangleGenerationSystem`` or use the concrete TGS
  API: ``triAxisProjection`` / ``IsProjectionOf`` / ``TriAxisObjCode`` /
  ``TriAxisProfile`` plus the coverage gate API.  This layer always exits 0.
* Layer 2 is a source-level chaff check.  Once a Lean declaration states a TGS
  projection/profile relation or coverage gate, the body must not be a hollow
  ``True.intro``, ``sorry`` placeholder, or all-zero/default profile.
* Layer 3 checks a host-owned designated list.  A designated target passes only
  when Lean declares a ``TriAxisProjected`` instance for it or a
  ``TriAxisBindingObligation`` for a target whose object-code binding is still
  outside the file.  Local triangle-shaped names are reported as context, not
  accepted as semantic evidence.

The semantic anti-vacuity authority is the Lean kernel: ``CoversDistinction``,
``CoversTime``, and ``CoversSymmetry`` are inductive predicates over
``TriAxisObjCode``.  This script is an index and anti-cheating check; it verifies
that the Lean gate exists and that source-level placeholders are absent.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Iterable


TOKEN = "BEDC_TRIANGLE_COVERAGE"
SCRIPT_DIR = Path(__file__).resolve().parent
LEAN_ROOT = SCRIPT_DIR.parent
REPO_ROOT = LEAN_ROOT.parent
BEDC_ROOT = LEAN_ROOT / "BEDC"
DEFAULT_DESIGNATED_PATH = REPO_ROOT / ".bedc" / "triangle_designated.txt"

FALLBACK_DESIGNATED = (
    "BEDC.Derived.RHRoute.CausalReflectionPositiveCone.CausalReflectionPositiveCone",
    "BEDC.Derived.RHRoute.PrimeCausalTower.PrimeCausalTower",
    "BEDC.Derived.RHRoute.ThreeAxisOrbitCollapse.ThreeAxisOrbitCollapseKernel",
    "BEDC.Foundations.TriangleGenerationSystem.triAxisProjection",
    "BEDC.Foundations.TriangleGenerationSystem.IsProjectionOf",
    "BEDC.Foundations.TriangleGenerationSystem.triAxisProjection_is_projection",
    "BEDC.Foundations.TriangleGenerationSystem.triAxisProjection_relation_forced",
    "BEDC.Foundations.TriangleGenerationSystem.ExistsUniqueProjection",
    "BEDC.Foundations.TriangleGenerationSystem.ExistsUniqueProjectionSigma",
    "BEDC.Foundations.TriangleGenerationSystem.triAxisProjection_forced_unique",
    "BEDC.Foundations.TriangleGenerationSystem.triAxisProjection_forced_unique_sigma",
    "BEDC.Foundations.TriangleGenerationSystem.triAxisProjection_forced_unique_pair",
    "BEDC.Foundations.TriangleGenerationSystem.nat_profile_zero",
    "BEDC.Foundations.TriangleGenerationSystem.nat_profile_succ",
    "BEDC.Foundations.TriangleGenerationSystem.nat_profile",
    "BEDC.Foundations.TriangleGenerationSystem.int_profile_zero",
    "BEDC.Foundations.TriangleGenerationSystem.int_profile_pos",
    "BEDC.Foundations.TriangleGenerationSystem.int_profile_neg",
    "BEDC.Foundations.TriangleGenerationSystem.int_negative_has_symmetry",
)

TGS_MODULE = "BEDC.Foundations.TriangleGenerationSystem"
TGS_API_RE = re.compile(
    r"\b(?:triAxisProjection|IsProjectionOf|TriAxisObjCode|TriAxisProfile|"
    r"ExistsUniqueProjection|ExistsUniqueProjectionSigma|CoversDistinction|"
    r"CoversTime|CoversSymmetry|AxisDemand|TriAxisProjected|"
    r"TriAxisBindingObligation)\b"
)
TGS_CLAIM_RE = re.compile(
    r"\b(?:triAxisProjection|IsProjectionOf|ExistsUniqueProjection|"
    r"ExistsUniqueProjectionSigma|CoversDistinction|CoversTime|"
    r"CoversSymmetry|TriAxisProjected|TriAxisBindingObligation)\b"
)
TGS_IMPORT_RE = re.compile(
    r"^\s*import\s+BEDC\.Foundations\.TriangleGenerationSystem\b",
    re.MULTILINE,
)

DECL_RE = re.compile(
    r"^\s*"
    r"(?:@\[[^\]]+\]\s*)*"
    r"(?:(?:private|protected|noncomputable|unsafe|partial|scoped|mutual|local)\s+)*"
    r"(?P<kind>theorem|lemma|def|abbrev|instance|inductive|class|structure)\s+"
    r"(?P<name>«[^»]+»|[A-Za-z0-9_'.]+)?\b"
)
NAMESPACE_RE = re.compile(r"^\s*namespace\s+(?P<name>[A-Za-z0-9_'.]+)\s*$")
END_RE = re.compile(r"^\s*end(?:\s+(?P<name>[A-Za-z0-9_'.]+))?\s*$")
FIELD_RE = re.compile(r"^\s{2,}(?P<name>[A-Za-z0-9_']+)\s*:")

SORRY_RE = re.compile(r"\bsorry\b|sorryAx")
TRUE_INTRO_RE = re.compile(r"\bTrue\.intro\b")
TRIVIAL_TRUE_TYPE_RE = re.compile(r":\s*True(?:\s*:=|\s*$)")
BY_TRIVIAL_RE = re.compile(r":=\s*by\s*(?:\n\s*)?(?:trivial|exact\s+True\.intro)\b")
ZERO_PROFILE_RE = re.compile(
    r"\{\s*distinction\s*:=\s*0\s*,\s*time\s*:=\s*0\s*,\s*symmetry\s*:=\s*0\s*\}"
)
PROFILE_ZERO_RE = re.compile(r"\bTriAxisProfile\.zero\b")
TGS_BINDING_RE = re.compile(r"\b(?:triAxisProjection|IsProjectionOf|ExistsUniqueProjection)\b")
TGS_RECURSIVE_SHAPE_RE = re.compile(
    r"\b(?:TriAxisObjCode\.(?:base|distinctionGen|timeGen|symmetryGen|pairGen)|"
    r"natAsObjCode|intAsObjCode)\b"
)
LOCAL_TRIANGLE_RE = re.compile(
    r"(?:ThreeAxis|threeAxis|Iota|iota|Symmetry|symmetry|Projection|projection|"
    r"Orbit|orbit|frontier|Frontier|collapse|Collapse)"
)


@dataclass
class LeanDeclaration:
    kind: str
    name: str
    qualified_name: str
    file: str
    line: int
    header: str
    body: str


@dataclass
class SourceUnit:
    file: str
    text: str
    imports_tgs: bool
    api_hits: tuple[str, ...]


@dataclass
class TGSRegistration:
    declaration: str
    kind: str
    file: str
    line: int
    uses_tri_axis_projection: bool
    uses_is_projection_of: bool
    uses_tri_axis_profile: bool
    uses_tri_axis_obj_code: bool


@dataclass
class AntiVacuityViolation:
    declaration: str
    file: str
    line: int
    reason: str


@dataclass
class DesignatedResult:
    target: str
    file: str | None
    line: int | None
    present: bool
    target_has_sorry: bool
    has_tgs_structure: bool
    has_triaxis_projected_gate: bool
    has_binding_obligation_gate: bool
    has_local_triangle_structure: bool
    enforceable: bool
    informational: bool
    reason: str


@dataclass
class LeanField:
    parent: str
    name: str
    qualified_name: str
    file: str
    line: int


def read_text(path: Path) -> str:
    return path.read_text(encoding="utf-8")


def strip_comments_and_strings(text: str) -> str:
    """Remove Lean comments and string contents while preserving line layout."""
    out: list[str] = []
    i = 0
    block_depth = 0
    while i < len(text):
        ch = text[i]
        nxt = text[i + 1] if i + 1 < len(text) else ""

        if block_depth:
            if ch == "/" and nxt == "-":
                block_depth += 1
                out.extend("  ")
                i += 2
                continue
            if ch == "-" and nxt == "/":
                block_depth -= 1
                out.extend("  ")
                i += 2
                continue
            out.append("\n" if ch == "\n" else " ")
            i += 1
            continue

        if ch == "/" and nxt == "-":
            block_depth = 1
            out.extend("  ")
            i += 2
            continue
        if ch == "-" and nxt == "-":
            while i < len(text) and text[i] != "\n":
                out.append(" ")
                i += 1
            continue
        if ch == '"':
            out.append(" ")
            i += 1
            while i < len(text):
                if text[i] == "\\":
                    out.append(" ")
                    if i + 1 < len(text):
                        out.append("\n" if text[i + 1] == "\n" else " ")
                    i += 2
                    continue
                if text[i] == '"':
                    out.append(" ")
                    i += 1
                    break
                out.append("\n" if text[i] == "\n" else " ")
                i += 1
            continue

        out.append(ch)
        i += 1

    return "".join(out)


def strip_line_comment(line: str) -> str:
    idx = line.find("--")
    return line if idx < 0 else line[:idx]


def module_name(path: Path) -> str:
    rel = path.relative_to(LEAN_ROOT).with_suffix("")
    return ".".join(rel.parts)


def lean_files(bedc_root: Path = BEDC_ROOT) -> list[Path]:
    return sorted(bedc_root.rglob("*.lean"))


def resolve_namespace(name: str, namespace_stack: list[str]) -> str:
    if name.startswith("BEDC."):
        return name
    if namespace_stack:
        return f"{namespace_stack[-1]}.{name}"
    return name


def declaration_namespace(module: str, namespace_stack: list[str]) -> str:
    return namespace_stack[-1] if namespace_stack else module


def qualified_name(name: str, namespace: str) -> str:
    if name.startswith("BEDC."):
        return name
    return f"{namespace}.{name}" if namespace else name


def update_namespace_stack(line: str, namespace_stack: list[str]) -> None:
    namespace_match = NAMESPACE_RE.match(line)
    if namespace_match:
        namespace_stack.append(resolve_namespace(namespace_match.group("name"), namespace_stack))
        return

    end_match = END_RE.match(line)
    if not end_match or not namespace_stack:
        return
    name = end_match.group("name")
    if name is None or namespace_stack[-1] == name or namespace_stack[-1].endswith(f".{name}"):
        namespace_stack.pop()


def declaration_block(lines: list[str], start_idx: int) -> str:
    block_lines = [strip_line_comment(lines[start_idx])]
    j = start_idx + 1
    while j < len(lines):
        line = strip_line_comment(lines[j])
        if (
            line.strip()
            and not line.startswith((" ", "\t", "|", "·"))
            and not re.match(r"^\s*(where|deriving)\b", line)
        ):
            break
        block_lines.append(line)
        j += 1
    return "\n".join(block_lines)


def declaration_header(block: str) -> str:
    marker_positions = [pos for pos in (block.find(":="), block.find(" where")) if pos >= 0]
    if not marker_positions:
        return block
    return block[: min(marker_positions)]


def scan_sources() -> tuple[list[LeanDeclaration], list[LeanField], list[SourceUnit]]:
    declarations: list[LeanDeclaration] = []
    fields: list[LeanField] = []
    sources: list[SourceUnit] = []
    for path in lean_files():
        text = read_text(path)
        lines = text.splitlines()
        module = module_name(path)
        rel_file = str(path.relative_to(REPO_ROOT))
        stripped_for_hits = "\n".join(strip_line_comment(line) for line in lines)
        sources.append(
            SourceUnit(
                file=rel_file,
                text=stripped_for_hits,
                imports_tgs=TGS_IMPORT_RE.search(stripped_for_hits) is not None,
                api_hits=tuple(sorted(set(TGS_API_RE.findall(stripped_for_hits)))),
            )
        )
        namespace_stack: list[str] = []
        for idx, line in enumerate(lines):
            line = strip_line_comment(line)
            update_namespace_stack(line, namespace_stack)
            match = DECL_RE.match(line)
            if not match:
                continue
            kind = match.group("kind")
            name = (match.group("name") or f"<anonymous_{kind}_{idx + 1}>").strip()
            namespace = declaration_namespace(module, namespace_stack)
            qualified = qualified_name(name, namespace)
            block = declaration_block(lines, idx)
            declarations.append(
                LeanDeclaration(
                    kind=kind,
                    name=name,
                    qualified_name=qualified,
                    file=rel_file,
                    line=idx + 1,
                    header=declaration_header(block),
                    body=block,
                )
            )
            if kind in {"structure", "class"}:
                j = idx + 1
                while j < len(lines):
                    next_line = lines[j]
                    if next_line.strip() == "":
                        j += 1
                        continue
                    if not next_line.startswith((" ", "\t")):
                        break
                    field_match = FIELD_RE.match(next_line)
                    if field_match:
                        field_name = field_match.group("name")
                        fields.append(
                            LeanField(
                                parent=qualified,
                                name=field_name,
                                qualified_name=f"{qualified}.{field_name}",
                                file=rel_file,
                                line=j + 1,
                            )
                        )
                    j += 1
    return declarations, fields, sources


def tgs_relevant_files(sources: Iterable[SourceUnit]) -> list[dict[str, object]]:
    files: list[dict[str, object]] = []
    for source in sources:
        if source.imports_tgs or source.api_hits:
            files.append(
                {
                    "file": source.file,
                    "imports_tgs": source.imports_tgs,
                    "api_hits": list(source.api_hits),
                }
            )
    return files


def is_tgs_declaration(decl: LeanDeclaration) -> bool:
    tgs_primitive_prefix = "BEDC.Foundations.TriangleGenerationSystem.TriAxisProfile"
    if decl.qualified_name == "BEDC.Foundations.TriangleGenerationSystem.TriAxisProfile":
        return False
    if decl.qualified_name.startswith(f"{tgs_primitive_prefix}."):
        return False
    if decl.qualified_name == "BEDC.Foundations.TriangleGenerationSystem.TriAxisObjCode":
        return False
    if TGS_CLAIM_RE.search(decl.body):
        return True
    return decl.file != "lean4/BEDC/Foundations/TriangleGenerationSystem.lean" and (
        "TriAxisProfile" in decl.body
    )


def tgs_registrations(declarations: Iterable[LeanDeclaration]) -> list[TGSRegistration]:
    registrations: list[TGSRegistration] = []
    for decl in declarations:
        if not is_tgs_declaration(decl):
            continue
        registrations.append(
            TGSRegistration(
                declaration=decl.qualified_name,
                kind=decl.kind,
                file=decl.file,
                line=decl.line,
                uses_tri_axis_projection="triAxisProjection" in decl.body,
                uses_is_projection_of="IsProjectionOf" in decl.body,
                uses_tri_axis_profile="TriAxisProfile" in decl.body,
                uses_tri_axis_obj_code="TriAxisObjCode" in decl.body,
            )
        )
    return registrations


def has_nondefault_profile_shape(body: str) -> bool:
    if TGS_RECURSIVE_SHAPE_RE.search(body):
        return True
    if re.search(r"\bTriAxisProfile\.(?:distinctionStep|timeStep|symmetryStep|merge)\b", body):
        return True
    if re.search(r"\{\s*distinction\s*:=\s*[1-9]", body):
        return True
    if re.search(r"\btime\s*:=\s*[1-9]", body):
        return True
    if re.search(r"\bsymmetry\s*:=\s*[1-9]", body):
        return True
    return False


def anti_vacuity_violations(declarations: Iterable[LeanDeclaration]) -> list[AntiVacuityViolation]:
    violations: list[AntiVacuityViolation] = []
    for decl in declarations:
        if not is_tgs_declaration(decl):
            continue

        body = decl.body
        if SORRY_RE.search(body):
            violations.append(
                AntiVacuityViolation(
                    declaration=decl.qualified_name,
                    file=decl.file,
                    line=decl.line,
                    reason="declares TGS structure with sorry/sorryAx",
                )
            )
        if TRUE_INTRO_RE.search(body) or TRIVIAL_TRUE_TYPE_RE.search(decl.header) or BY_TRIVIAL_RE.search(body):
            violations.append(
                AntiVacuityViolation(
                    declaration=decl.qualified_name,
                    file=decl.file,
                    line=decl.line,
                    reason="declares TGS structure with trivial True proof",
                )
            )
        if ("TriAxisProfile" in body or "triAxisProjection" in body) and (
            ZERO_PROFILE_RE.search(body) or PROFILE_ZERO_RE.search(body)
        ) and "triAxisProjection" not in body and not has_nondefault_profile_shape(body):
            violations.append(
                AntiVacuityViolation(
                    declaration=decl.qualified_name,
                    file=decl.file,
                    line=decl.line,
                    reason="TGS profile is all-zero/default without a generator-forced projection",
                )
            )
    return violations


def read_designated(path: Path) -> list[str]:
    if not path.exists():
        return list(FALLBACK_DESIGNATED)
    targets: list[str] = []
    for raw_line in path.read_text(encoding="utf-8").splitlines():
        line = raw_line.strip()
        if not line or line.startswith("#"):
            continue
        targets.append(line)
    return targets


def designated_source(path: Path) -> str:
    return (
        str(path.relative_to(REPO_ROOT))
        if path.exists() and path.is_relative_to(REPO_ROOT)
        else ("script-constant" if not path.exists() else str(path))
    )


def declaration_has_tgs_structure(target: str, declarations: Iterable[LeanDeclaration], fields: Iterable[LeanField]) -> bool:
    target_decl = next((decl for decl in declarations if decl.qualified_name == target), None)
    if target_decl and is_tgs_declaration(target_decl):
        return True
    target_prefix = f"{target}."
    if any(field.parent == target and TGS_API_RE.search(field.name) for field in fields):
        return True
    for decl in declarations:
        body_mentions_target = target in decl.body or target.rsplit(".", 1)[-1] in decl.body
        if body_mentions_target and is_tgs_declaration(decl):
            return True
        if decl.qualified_name.startswith(target_prefix) and is_tgs_declaration(decl):
            return True
    return False


def _gate_mentions_target(target: str, decl: LeanDeclaration) -> bool:
    return target in decl.body or target in decl.header


def declaration_has_triaxis_projected_gate(
    target: str,
    declarations: Iterable[LeanDeclaration],
) -> bool:
    for decl in declarations:
        if decl.kind != "instance":
            continue
        if "TriAxisProjected" not in decl.body and "TriAxisProjected" not in decl.header:
            continue
        if _gate_mentions_target(target, decl) and not SORRY_RE.search(decl.body):
            return True
    return False


def declaration_has_binding_obligation_gate(
    target: str,
    declarations: Iterable[LeanDeclaration],
) -> bool:
    for decl in declarations:
        if "TriAxisBindingObligation" not in decl.body and "TriAxisBindingObligation" not in decl.header:
            continue
        if _gate_mentions_target(target, decl) and not SORRY_RE.search(decl.body):
            return True
    return False


def declaration_has_local_triangle_structure(
    target: str,
    declarations: Iterable[LeanDeclaration],
    fields: Iterable[LeanField],
) -> bool:
    target_short = target.rsplit(".", 1)[-1]
    target_decl = next((decl for decl in declarations if decl.qualified_name == target), None)
    if target_decl and LOCAL_TRIANGLE_RE.search(target_decl.body):
        return True
    if any(field.parent == target and LOCAL_TRIANGLE_RE.search(field.name) for field in fields):
        return True
    for decl in declarations:
        if target in decl.body or target_short in decl.body or decl.qualified_name.startswith(f"{target}."):
            if LOCAL_TRIANGLE_RE.search(decl.body) or LOCAL_TRIANGLE_RE.search(decl.qualified_name):
                return True
    return False


def file_has_local_triangle_structure(target: str, declarations: list[LeanDeclaration]) -> bool:
    target_decl = next((decl for decl in declarations if decl.qualified_name == target), None)
    if target_decl is None:
        return False
    return any(
        decl.file == target_decl.file
        and (LOCAL_TRIANGLE_RE.search(decl.body) or LOCAL_TRIANGLE_RE.search(decl.qualified_name))
        for decl in declarations
    )


def effective_designated_targets(
    configured: Iterable[str],
    registrations: Iterable[TGSRegistration],
) -> list[str]:
    seen: set[str] = set()
    targets: list[str] = []
    _ = registrations
    for target in configured:
        if target in seen:
            continue
        seen.add(target)
        targets.append(target)
    return targets


def designated_results(
    declarations: list[LeanDeclaration],
    fields: list[LeanField],
    designated: list[str],
    *,
    strict_designated: bool,
) -> list[DesignatedResult]:
    by_name = {decl.qualified_name: decl for decl in declarations}
    results: list[DesignatedResult] = []
    for target in designated:
        decl = by_name.get(target)
        has_tgs = declaration_has_tgs_structure(target, declarations, fields)
        has_projected_gate = declaration_has_triaxis_projected_gate(target, declarations)
        has_obligation_gate = declaration_has_binding_obligation_gate(target, declarations)
        target_has_sorry = bool(decl and SORRY_RE.search(decl.body))
        has_local = declaration_has_local_triangle_structure(
            target,
            declarations,
            fields,
        ) or file_has_local_triangle_structure(target, declarations)
        present = decl is not None
        enforceable = True
        informational = False
        if not present:
            reason = "designated declaration is missing"
        elif target_has_sorry:
            reason = "designated declaration contains sorry/sorryAx"
        elif has_projected_gate:
            reason = "designated target has Lean kernel TriAxisProjected gate"
        elif has_obligation_gate:
            reason = "designated target has honest Lean binding obligation gate"
        elif has_tgs:
            reason = "designated target has TGS-bound structure"
        elif has_local:
            reason = (
                "designated target has local triangle/projection structure but "
                "no Lean kernel gate"
            )
        else:
            reason = "designated target has no detected Lean kernel gate"
        results.append(
            DesignatedResult(
                target=target,
                file=decl.file if decl else None,
                line=decl.line if decl else None,
                present=present,
                target_has_sorry=target_has_sorry,
                has_tgs_structure=has_tgs,
                has_triaxis_projected_gate=has_projected_gate,
                has_binding_obligation_gate=has_obligation_gate,
                has_local_triangle_structure=has_local,
                enforceable=enforceable,
                informational=informational,
                reason=reason,
            )
        )
    return results


def designated_violations(
    results: Iterable[DesignatedResult],
    *,
    strict_designated: bool,
) -> list[DesignatedResult]:
    return [
        result
        for result in results
        if (
            result.enforceable
            and (
                not result.present
                or result.target_has_sorry
                or (
                    not result.has_triaxis_projected_gate
                    if strict_designated
                    else not (
                        result.has_triaxis_projected_gate
                        or result.has_binding_obligation_gate
                        or result.has_tgs_structure
                    )
                )
            )
        )
    ]


def layer1_payload(declarations: list[LeanDeclaration], sources: list[SourceUnit]) -> dict[str, object]:
    registrations = tgs_registrations(declarations)
    return {
        "layer": "layer1_survey",
        "informational": True,
        "exit_code": 0,
        "tgs_files": tgs_relevant_files(sources),
        "registered_count": len(registrations),
        "registered": [asdict(record) for record in registrations],
    }


def layer2_payload(declarations: list[LeanDeclaration]) -> dict[str, object]:
    violations = anti_vacuity_violations(declarations)
    registrations = tgs_registrations(declarations)
    return {
        "layer": "layer2_antivacuity",
        "informational": False,
        "passed": len(violations) == 0,
        "exit_code": 0 if not violations else 1,
        "checked_count": len(registrations),
        "violations": [asdict(record) for record in violations],
    }


def layer3_payload(
    declarations: list[LeanDeclaration],
    fields: list[LeanField],
    designated: list[str],
    *,
    strict_designated: bool,
) -> dict[str, object]:
    results = designated_results(declarations, fields, designated, strict_designated=strict_designated)
    violations = designated_violations(results, strict_designated=strict_designated)
    return {
        "layer": "layer3_designated",
        "informational": False,
        "strict_designated": strict_designated,
        "passed": len(violations) == 0,
        "exit_code": 0 if not violations else 1,
        "designated_count": len(results),
        "results": [asdict(result) for result in results],
        "violations": [asdict(result) for result in violations],
    }


def full_payload(
    args: argparse.Namespace,
    declarations: list[LeanDeclaration],
    fields: list[LeanField],
    sources: list[SourceUnit],
) -> dict[str, object]:
    layer1 = layer1_payload(declarations, sources)
    registered = [
        TGSRegistration(**record)
        for record in layer1["registered"]
    ]
    designated = effective_designated_targets(read_designated(args.designated), registered)
    layer2 = layer2_payload(declarations)
    layer3 = layer3_payload(
        declarations,
        fields,
        designated,
        strict_designated=args.strict_designated,
    )
    exit_code = max(
        int(layer2["exit_code"]),
        int(layer3["exit_code"]),
    )
    return {
        "token": TOKEN,
        "script": str(Path(__file__).relative_to(REPO_ROOT)),
        "repo_root": str(REPO_ROOT),
        "no_chaff_design": True,
        "scope": (
            "Lean kernel coverage predicates are the semantic authority.  This "
            "harness indexes TGS-registered declarations and checks that "
            "designated targets expose a Lean gate."
        ),
        "tgs_api": {
            "module": TGS_MODULE,
            "object_code": "TriAxisObjCode",
            "profile": "TriAxisProfile",
            "projection": "triAxisProjection",
            "relation": "IsProjectionOf",
            "forced_unique": "triAxisProjection_forced_unique",
            "coverage_predicates": [
                "CoversDistinction",
                "CoversTime",
                "CoversSymmetry",
            ],
            "kernel_gate": "TriAxisProjected",
            "binding_obligation_gate": "TriAxisBindingObligation",
        },
        "designated_source": designated_source(args.designated),
        "strict_designated": args.strict_designated,
        "exit_code": exit_code,
        "passed": exit_code == 0,
        "layers": {
            "layer1_survey": layer1,
            "layer2_antivacuity": layer2,
            "layer3_designated": layer3,
        },
    }


def print_human(payload: dict[str, object]) -> None:
    layers = payload["layers"]
    layer1 = layers["layer1_survey"]
    layer2 = layers["layer2_antivacuity"]
    layer3 = layers["layer3_designated"]
    print(
        f"[{TOKEN}] layer1 survey (informational): "
        f"registered={layer1['registered_count']} files={len(layer1['tgs_files'])}"
    )
    print(
        f"[{TOKEN}] layer2 anti-vacuity: "
        f"checked={layer2['checked_count']} violations={len(layer2['violations'])}"
    )
    for violation in layer2["violations"]:
        print(
            f"[{TOKEN}] layer2 FAIL {violation['declaration']} "
            f"({violation['file']}:{violation['line']}): {violation['reason']}",
            file=sys.stderr,
        )
    print(
        f"[{TOKEN}] layer3 designated: "
        f"targets={layer3['designated_count']} violations={len(layer3['violations'])} "
        f"strict={layer3['strict_designated']}"
    )
    for result in layer3["results"]:
        level = "info" if result["informational"] else "hard"
        print(
            f"[{TOKEN}] layer3 {level}: {result['target']} - {result['reason']}"
        )
    for violation in layer3["violations"]:
        print(
            f"[{TOKEN}] layer3 FAIL {violation['target']}: {violation['reason']}",
            file=sys.stderr,
        )
    print(f"[{TOKEN}] exit_code={payload['exit_code']}")


def command_payload(args: argparse.Namespace) -> tuple[dict[str, object], int]:
    declarations, fields, sources = scan_sources()
    if args.command == "survey":
        payload = {"token": TOKEN, **layer1_payload(declarations, sources)}
        return payload, 0
    if args.command == "anti-vacuity":
        payload = {"token": TOKEN, **layer2_payload(declarations)}
        return payload, int(payload["exit_code"])
    if args.command == "designated":
        registered = tgs_registrations(declarations)
        designated = effective_designated_targets(read_designated(args.designated), registered)
        payload = {
            "token": TOKEN,
            **layer3_payload(
                declarations,
                fields,
                designated,
                strict_designated=args.strict_designated,
            ),
        }
        return payload, int(payload["exit_code"])
    payload = full_payload(args, declarations, fields, sources)
    return payload, int(payload["exit_code"])


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="BEDC triangle coverage harness over the TGS universe and designated targets."
    )
    parser.add_argument("--json", action="store_true", help="Emit JSON to stdout")
    parser.add_argument(
        "--designated",
        type=Path,
        default=DEFAULT_DESIGNATED_PATH,
        help="Host-owned designated target list",
    )
    parser.add_argument(
        "--strict-designated",
        action="store_true",
        help=(
            "Fail designated targets that lack a TriAxisProjected instance.  "
            "The default also accepts an honest TriAxisBindingObligation."
        ),
    )
    sub = parser.add_subparsers(dest="command")
    sub.add_parser("all", help="Run all layers")
    sub.add_parser("survey", help="Run layer 1 informational survey")
    sub.add_parser("anti-vacuity", help="Run layer 2 hard anti-vacuity gate")
    sub.add_parser("designated", help="Run layer 3 designated target reader")
    return parser


def main() -> int:
    parser = build_parser()
    args = parser.parse_args()
    if args.command is None:
        args.command = "all"
    args.designated = args.designated.resolve()
    if not BEDC_ROOT.exists():
        print(f"[{TOKEN}] setup error: lean4/BEDC not found at {BEDC_ROOT}", file=sys.stderr)
        return 2
    payload, exit_code = command_payload(args)
    if args.json:
        print(json.dumps(payload, indent=2, ensure_ascii=False))
    else:
        if args.command == "all":
            print_human(payload)
        else:
            print(f"[{TOKEN}] {args.command}: exit_code={exit_code}")
            if "violations" in payload:
                for violation in payload["violations"]:
                    target = violation.get("declaration") or violation.get("target")
                    reason = violation.get("reason")
                    print(f"[{TOKEN}] FAIL {target}: {reason}", file=sys.stderr)
    return exit_code


if __name__ == "__main__":
    raise SystemExit(main())
