#!/usr/bin/env python3
from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
import re
import sys

from matrix_metadata import MatrixMetadataError, load_rows


TOKEN = "BEDC_GATE_H_HOLLOW_PATTERN"

# This gate is intentionally syntactic. It blocks known hollow shapes that are
# recognizable from Lean source text; it does not decide whether an arbitrary
# theorem carries mathematical content. Gate W remains the primary exported_core
# correspondence anchor, and this gate adds bedc_constructive_core depth.
ALLOWLIST: dict[str, str] = {}

DECL_RE = re.compile(
    r"^\s*(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*"
    r"(?P<kind>theorem|lemma|def|structure)\s+"
    r"(?P<name>[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*)\b"
)
NAMESPACE_RE = re.compile(r"^\s*namespace\s+([A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*)\b")
END_RE = re.compile(r"^\s*end(?:\s+[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*)?\s*$")
LEAN_DECL_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)+")
TRUE_INTRO_RE = re.compile(
    r":\s*True\s*:=\s*(?:by\s+)?(?:exact\s+)?(?:True\.intro|trivial)\b",
    re.DOTALL,
)
STATEMENT_DEF_RE = re.compile(r":\s*Prop\b", re.DOTALL)


@dataclass(frozen=True)
class Decl:
    path: Path
    line_no: int
    kind: str
    short_name: str
    full_name: str
    block: str
    scan_all: bool


@dataclass(frozen=True)
class Violation:
    decl: Decl
    pattern: str
    detail: str


def find_bridge_root() -> Path:
    here = Path(__file__).resolve()
    for parent in (here.parent, *here.parents):
        if (parent / "lean4" / "lakefile.lean").exists() and parent.name == "bedc_mathlib_bridge":
            return parent
    raise RuntimeError("cannot locate papers/bedc_mathlib_bridge root")


def find_repo_root(bridge_root: Path) -> Path:
    for parent in (bridge_root, *bridge_root.parents):
        if (parent / "lean4" / "BEDC").exists() and (parent / "papers" / "bedc_mathlib_bridge").exists():
            return parent
    raise RuntimeError("cannot locate repository root")


def strip_line_comment(line: str) -> str:
    return line.split("--", 1)[0]


def join_name(namespace_stack: list[str], name: str) -> str:
    if "." in name:
        return name
    if not namespace_stack:
        return name
    return ".".join([*namespace_stack, name])


def pop_namespace(namespace_stack: list[str], line: str) -> None:
    match = END_RE.match(line)
    if match and namespace_stack:
        namespace_stack.pop()


def declaration_starts(path: Path, scan_all: bool) -> list[tuple[int, str, str, str]]:
    starts: list[tuple[int, str, str, str]] = []
    namespace_stack: list[str] = []
    for index, raw_line in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
        line = strip_line_comment(raw_line)
        match = NAMESPACE_RE.match(line)
        if match:
            namespace_stack.extend(match.group(1).split("."))
            continue
        decl = DECL_RE.match(line)
        if decl:
            short = decl.group("name")
            starts.append((index, decl.group("kind"), short, join_name(namespace_stack, short)))
            continue
        pop_namespace(namespace_stack, line)
    return starts


def parse_declarations(path: Path, scan_all: bool) -> list[Decl]:
    text = path.read_text(encoding="utf-8")
    lines = text.splitlines()
    starts = declaration_starts(path, scan_all)
    decls: list[Decl] = []
    for offset, (line_no, kind, short_name, full_name) in enumerate(starts):
        next_line = starts[offset + 1][0] if offset + 1 < len(starts) else len(lines) + 1
        block = "\n".join(lines[line_no - 1 : next_line - 1])
        decls.append(
            Decl(
                path=path,
                line_no=line_no,
                kind=kind,
                short_name=short_name,
                full_name=full_name,
                block=block,
                scan_all=scan_all,
            )
        )
    return decls


def collect_matrix_targets(matrix_path: Path) -> set[str]:
    rows = load_rows(matrix_path)
    targets: set[str] = set()
    for row in rows:
        if row.metadata["kind"] not in {"exported_core", "bedc_constructive_core"}:
            continue
        for field in (
            "bedc_irreducible_decl",
            "export_witness",
            "mathlib_correspondence_decl",
        ):
            value = row.metadata.get(field)
            if isinstance(value, str) and value.strip():
                targets.add(value.strip())
        for value in LEAN_DECL_RE.findall(row.cells.get("BEDC source", "")):
            if value.startswith(("BEDC.Derived.", "BedcMathlibBridge.Export.")):
                targets.add(value)
    return targets


def all_scan_files(repo_root: Path, bridge_root: Path, fixture_paths: list[Path]) -> dict[Path, bool]:
    files: dict[Path, bool] = {}
    export_dir = bridge_root / "lean4" / "BedcMathlibBridge" / "Export"
    if export_dir.exists():
        for path in sorted(export_dir.rglob("*.lean")):
            files[path.resolve()] = True
    derived_dir = repo_root / "lean4" / "BEDC" / "Derived"
    if derived_dir.exists():
        for path in sorted(derived_dir.rglob("*.lean")):
            files.setdefault(path.resolve(), False)
    for path in fixture_paths:
        files[path.resolve()] = True
    return files


def decl_is_target(decl: Decl, targets: set[str]) -> bool:
    if decl.scan_all:
        return True
    return decl.full_name in targets or decl.short_name in targets


def statement_defs(decls: list[Decl]) -> dict[Path, set[str]]:
    out: dict[Path, set[str]] = {}
    for decl in decls:
        if decl.kind != "def":
            continue
        if not decl.short_name.endswith("_Statement"):
            continue
        if STATEMENT_DEF_RE.search(decl.block):
            out.setdefault(decl.path, set()).add(decl.short_name[: -len("_Statement")])
    return out


def has_statement_companion(decl: Decl, defs_by_path: dict[Path, set[str]]) -> bool:
    bases = defs_by_path.get(decl.path, set())
    return any(
        decl.short_name == f"{base}_well_formed"
        or decl.short_name.startswith(f"{base}_")
        or base.startswith(decl.short_name)
        for base in bases
    )


def theorem_header_and_proof(block: str) -> tuple[str, str]:
    marker = block.find(":=")
    if marker < 0:
        return block, ""
    return block[:marker], block[marker + 2 :]


def first_top_level_colon(text: str) -> int:
    depth = 0
    opens = "([{"
    closes = ")]}"
    for index, char in enumerate(text):
        if char in opens:
            depth += 1
        elif char in closes and depth > 0:
            depth -= 1
        elif char == ":" and depth == 0:
            return index
    return -1


def theorem_conclusion(block: str) -> str:
    header, _proof = theorem_header_and_proof(block)
    colon = first_top_level_colon(header)
    if colon < 0:
        return ""
    return header[colon + 1 :].strip()


def conclusion_is_exists(block: str) -> bool:
    conclusion = theorem_conclusion(block)
    return conclusion.startswith("∃") or conclusion.startswith("Exists")


def binder_chunks(header: str) -> list[str]:
    chunks: list[str] = []
    stack: list[tuple[str, int]] = []
    pairs = {"(": ")", "{": "}", "[": "]"}
    for index, char in enumerate(header):
        if char in pairs:
            stack.append((pairs[char], index))
        elif stack and char == stack[-1][0]:
            expected, start = stack.pop()
            if not stack and expected in {")", "}"}:
                chunks.append(header[start + 1 : index])
    return chunks


def split_top_level_colon(text: str) -> tuple[str, str] | None:
    depth = 0
    for index, char in enumerate(text):
        if char in "([{":
            depth += 1
        elif char in ")]}" and depth > 0:
            depth -= 1
        elif char == ":" and depth == 0:
            return text[:index].strip(), text[index + 1 :].strip()
    return None


def names_from_binder(text: str) -> list[str]:
    return re.findall(r"\b[A-Za-z_][A-Za-z0-9_']*\b", text)


def cert_like_binders(block: str) -> list[str]:
    header, _proof = theorem_header_and_proof(block)
    binders: list[str] = []
    for chunk in binder_chunks(header):
        split = split_top_level_colon(chunk)
        if split is None:
            continue
        names_text, type_text = split
        names = names_from_binder(names_text)
        if not names:
            continue
        type_head = names_from_binder(type_text[: type_text.find(" ") if " " in type_text else len(type_text)])
        type_names = names_from_binder(type_text)
        cert_type = any(name.endswith(("Cert", "Certificate")) for name in [*type_head, *type_names])
        cert_name = any(name.endswith(("Cert", "Certificate")) for name in names)
        if cert_type or cert_name:
            binders.extend(names)
    return binders


def all_binders(block: str) -> list[str]:
    header, _proof = theorem_header_and_proof(block)
    binders: list[str] = []
    for chunk in binder_chunks(header):
        split = split_top_level_colon(chunk)
        if split is None:
            continue
        names_text, _type_text = split
        binders.extend(names_from_binder(names_text))
    return binders


def normalized_proof_body(block: str) -> str:
    _header, proof = theorem_header_and_proof(block)
    proof = "\n".join(
        line for line in proof.splitlines()
        if not END_RE.match(strip_line_comment(line))
    )
    proof = re.sub(r"\s+", " ", proof).strip()
    if proof.startswith("by exact "):
        proof = proof[len("by exact ") :].strip()
    elif proof.startswith("by "):
        body = proof[len("by ") :].strip()
        if body.startswith("exact "):
            proof = body[len("exact ") :].strip()
    elif proof.startswith("exact "):
        proof = proof[len("exact ") :].strip()
    return proof


def proof_is_projection_exists(block: str, hyp_names: list[str]) -> bool:
    if not conclusion_is_exists(block):
        return False
    proof = normalized_proof_body(block)
    if not (proof.startswith("⟨") or proof.startswith("Exists.intro ")):
        return False
    if any(token in proof for token in ("match ", "cases ", "induction ", "have ", "let ", "fun ")):
        return False
    projection_re = re.compile(
        r"\b(" + "|".join(re.escape(name) for name in hyp_names) + r")\.[A-Za-z_][A-Za-z0-9_'.]*\b"
    ) if hyp_names else None
    if projection_re is None or projection_re.search(proof) is None:
        return False
    callish = re.findall(
        r"\b[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)?\b",
        proof,
    )
    projection_terms = set()
    projection_parts = set()
    for match in projection_re.finditer(proof):
        term = match.group(0)
        projection_terms.add(term)
        projection_parts.update(term.split("."))
    allowed = set(hyp_names) | projection_parts | {"Exists", "intro", "And", "Iff", "rfl"}
    leftovers = [
        name for name in callish
        if name not in projection_terms
        and name not in allowed
        and not any(name in part for part in projection_parts)
    ]
    return not leftovers


def find_violations(decls: list[Decl], targets: set[str]) -> list[Violation]:
    defs_by_path = statement_defs(decls)
    violations: list[Violation] = []
    for decl in decls:
        if decl.kind not in {"theorem", "lemma"}:
            continue
        if not decl_is_target(decl, targets):
            continue
        cert_binders = cert_like_binders(decl.block)
        if TRUE_INTRO_RE.search(decl.block):
            if (
                "_well_formed" in decl.short_name
                or "_Statement" in decl.short_name
                or has_statement_companion(decl, defs_by_path)
            ):
                violations.append(
                    Violation(
                        decl,
                        "statement_only_true_intro",
                        "statement-only theorem proves True by True.intro/trivial",
                    )
                )
        if cert_binders and conclusion_is_exists(decl.block):
            violations.append(
                Violation(
                    decl,
                    "certificate_hypothesis_exists",
                    "certificate-like hypothesis feeds an existential conclusion",
                )
            )
        if proof_is_projection_exists(decl.block, all_binders(decl.block)):
            violations.append(
                Violation(
                    decl,
                    "projection_exists",
                    "existential proof is a pure projection from a hypothesis",
                )
            )
    return violations


def main() -> int:
    if len(sys.argv) < 2:
        raise SystemExit("usage: check_no_hollow.py MATRIX.md [fixture.lean ...]")
    matrix_path = Path(sys.argv[1])
    fixture_paths = [Path(arg) for arg in sys.argv[2:]]
    try:
        bridge_root = find_bridge_root()
        repo_root = find_repo_root(bridge_root)
        targets = collect_matrix_targets(matrix_path)
    except (RuntimeError, MatrixMetadataError) as exc:
        print(f"{TOKEN}: {exc}", file=sys.stderr)
        return 1

    decls: list[Decl] = []
    for path, scan_all in all_scan_files(repo_root, bridge_root, fixture_paths).items():
        if path.exists():
            decls.extend(parse_declarations(path, scan_all))

    violations = [
        violation
        for violation in find_violations(decls, targets)
        if violation.decl.full_name not in ALLOWLIST
    ]
    if violations:
        for violation in violations:
            rel = violation.decl.path
            try:
                rel = violation.decl.path.relative_to(repo_root)
            except ValueError:
                pass
            print(
                f"{rel}:{violation.decl.line_no}: {TOKEN}: "
                f"{violation.pattern}: `{violation.decl.full_name}`: {violation.detail}"
            )
        print(
            f"[no-hollow] FAIL: {len(violations)} hollow pattern hit(s); "
            f"allowlist={len(ALLOWLIST)}"
        )
        return 1

    audited = sum(1 for decl in decls if decl.kind in {"theorem", "lemma"} and decl_is_target(decl, targets))
    print(
        "[no-hollow] PASS: "
        f"audited {audited} export-related theorem(s); "
        "coverage=syntactic known hollow patterns only; "
        f"allowlist={len(ALLOWLIST)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
