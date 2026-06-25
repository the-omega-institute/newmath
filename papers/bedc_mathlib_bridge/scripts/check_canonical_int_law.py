#!/usr/bin/env python3
from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
import re
import sys


TOKEN = "BEDC_GATE_R_LOCAL_INT_LAW"

# Canonical integer ring laws live in the BEDC source below. The explicit list
# keeps this checker stable while still validating that the source declares each
# protected public law name.
CANONICAL_SOURCE = Path("lean4/BEDC/Derived/IntUp/CommRing.lean")
CANONICAL_NAMES = {
    "IntAdd_respects",
    "IntMul_respects",
    "IntNeg_respects",
    "IntAdd_comm",
    "IntAdd_assoc",
    "IntAdd_zero",
    "IntAdd_zero_left",
    "IntAdd_neg",
    "IntAdd_neg_left",
    "IntMul_comm",
    "IntMul_assoc",
    "IntMul_one",
    "IntMul_one_left",
    "IntMul_zero",
    "IntMul_zero_left",
    "IntMul_add_distrib",
    "IntMul_add_distrib_right",
}

ALLOWLIST = {
    "BEDC.Derived.RationalUp.IntMul_comm":
        "construction substrate imported by IntUp/CommRing.lean",
}

DECL_RE = re.compile(
    r"^\s*(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*"
    r"(?P<kind>theorem|lemma|def)\s+"
    r"(?P<name>[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*)\b"
)
NAMESPACE_RE = re.compile(
    r"^\s*namespace\s+"
    r"(?P<name>[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*)\b"
)
END_RE = re.compile(
    r"^\s*end(?:\s+[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*)?\s*$"
)

QUAL = r"(?:[A-Za-z_][A-Za-z0-9_']*\.)*"
VAR = r"[A-Za-z_][A-Za-z0-9_']*"
INT_EQ = rf"{QUAL}IntEq"
INT_ADD = rf"{QUAL}IntAdd"
INT_MUL = rf"{QUAL}IntMul"
INT_NEG = rf"{QUAL}IntNeg"
INT_ZERO = rf"{QUAL}intZero"
INT_ONE = rf"{QUAL}intOne"

LAW_SHAPES: tuple[tuple[str, re.Pattern[str], str], ...] = (
    (
        "heuristic_int_mul_assoc",
        re.compile(
            rf"{INT_EQ}\s*"
            rf"\(\s*{INT_MUL}\s+\(\s*{INT_MUL}\s+(?P<a>{VAR})\s+(?P<b>{VAR})\s*\)"
            rf"\s+(?P<c>{VAR})\s*\)\s*"
            rf"\(\s*{INT_MUL}\s+(?P=a)\s+\(\s*{INT_MUL}\s+(?P=b)\s+(?P=c)\s*\)\s*\)"
        ),
        "integer multiplication associativity shape",
    ),
    (
        "heuristic_int_mul_comm",
        re.compile(
            rf"{INT_EQ}\s*"
            rf"\(\s*{INT_MUL}\s+(?P<a>{VAR})\s+(?P<b>{VAR})\s*\)\s*"
            rf"\(\s*{INT_MUL}\s+(?P=b)\s+(?P=a)\s*\)"
        ),
        "integer multiplication commutativity shape",
    ),
    (
        "heuristic_int_add_assoc",
        re.compile(
            rf"{INT_EQ}\s*"
            rf"\(\s*{INT_ADD}\s+\(\s*{INT_ADD}\s+(?P<a>{VAR})\s+(?P<b>{VAR})\s*\)"
            rf"\s+(?P<c>{VAR})\s*\)\s*"
            rf"\(\s*{INT_ADD}\s+(?P=a)\s+\(\s*{INT_ADD}\s+(?P=b)\s+(?P=c)\s*\)\s*\)"
        ),
        "integer addition associativity shape",
    ),
    (
        "heuristic_int_add_comm",
        re.compile(
            rf"{INT_EQ}\s*"
            rf"\(\s*{INT_ADD}\s+(?P<a>{VAR})\s+(?P<b>{VAR})\s*\)\s*"
            rf"\(\s*{INT_ADD}\s+(?P=b)\s+(?P=a)\s*\)"
        ),
        "integer addition commutativity shape",
    ),
    (
        "heuristic_int_mul_add_distrib",
        re.compile(
            rf"{INT_EQ}\s*"
            rf"\(\s*{INT_MUL}\s+(?P<a>{VAR})\s+"
            rf"\(\s*{INT_ADD}\s+(?P<b>{VAR})\s+(?P<c>{VAR})\s*\)\s*\)\s*"
            rf"\(\s*{INT_ADD}\s+\(\s*{INT_MUL}\s+(?P=a)\s+(?P=b)\s*\)\s+"
            rf"\(\s*{INT_MUL}\s+(?P=a)\s+(?P=c)\s*\)\s*\)"
        ),
        "integer left distributivity shape",
    ),
    (
        "heuristic_int_mul_add_distrib_right",
        re.compile(
            rf"{INT_EQ}\s*"
            rf"\(\s*{INT_MUL}\s+\(\s*{INT_ADD}\s+(?P<a>{VAR})\s+(?P<b>{VAR})\s*\)"
            rf"\s+(?P<c>{VAR})\s*\)\s*"
            rf"\(\s*{INT_ADD}\s+\(\s*{INT_MUL}\s+(?P=a)\s+(?P=c)\s*\)\s+"
            rf"\(\s*{INT_MUL}\s+(?P=b)\s+(?P=c)\s*\)\s*\)"
        ),
        "integer right distributivity shape",
    ),
    (
        "heuristic_int_mul_one",
        re.compile(
            rf"{INT_EQ}\s*\(\s*{INT_MUL}\s+(?P<a>{VAR})\s+{INT_ONE}\s*\)\s+(?P=a)\b"
        ),
        "integer right one law shape",
    ),
    (
        "heuristic_int_mul_one_left",
        re.compile(
            rf"{INT_EQ}\s*\(\s*{INT_MUL}\s+{INT_ONE}\s+(?P<a>{VAR})\s*\)\s+(?P=a)\b"
        ),
        "integer left one law shape",
    ),
    (
        "heuristic_int_mul_zero",
        re.compile(
            rf"{INT_EQ}\s*\(\s*{INT_MUL}\s+(?P<a>{VAR})\s+{INT_ZERO}\s*\)\s+{INT_ZERO}\b"
        ),
        "integer right zero multiplication law shape",
    ),
    (
        "heuristic_int_mul_zero_left",
        re.compile(
            rf"{INT_EQ}\s*\(\s*{INT_MUL}\s+{INT_ZERO}\s+(?P<a>{VAR})\s*\)\s+{INT_ZERO}\b"
        ),
        "integer left zero multiplication law shape",
    ),
    (
        "heuristic_int_add_zero",
        re.compile(
            rf"{INT_EQ}\s*\(\s*{INT_ADD}\s+(?P<a>{VAR})\s+{INT_ZERO}\s*\)\s+(?P=a)\b"
        ),
        "integer right additive zero law shape",
    ),
    (
        "heuristic_int_add_zero_left",
        re.compile(
            rf"{INT_EQ}\s*\(\s*{INT_ADD}\s+{INT_ZERO}\s+(?P<a>{VAR})\s*\)\s+(?P=a)\b"
        ),
        "integer left additive zero law shape",
    ),
    (
        "heuristic_int_add_neg",
        re.compile(
            rf"{INT_EQ}\s*\(\s*{INT_ADD}\s+(?P<a>{VAR})\s+"
            rf"\(\s*{INT_NEG}\s+(?P=a)\s*\)\s*\)\s+{INT_ZERO}\b"
        ),
        "integer right additive inverse law shape",
    ),
    (
        "heuristic_int_add_neg_left",
        re.compile(
            rf"{INT_EQ}\s*\(\s*{INT_ADD}\s+\(\s*{INT_NEG}\s+(?P<a>{VAR})\s*\)"
            rf"\s+(?P=a)\s*\)\s+{INT_ZERO}\b"
        ),
        "integer left additive inverse law shape",
    ),
)


@dataclass(frozen=True)
class Decl:
    path: Path
    line_no: int
    kind: str
    short_name: str
    full_name: str
    block: str
    fixture: bool

    @property
    def base_name(self) -> str:
        return self.short_name.rsplit(".", 1)[-1]


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


def declaration_starts(path: Path) -> list[tuple[int, str, str, str]]:
    starts: list[tuple[int, str, str, str]] = []
    namespace_stack: list[str] = []
    for index, raw_line in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
        line = strip_line_comment(raw_line)
        namespace_match = NAMESPACE_RE.match(line)
        if namespace_match:
            namespace_stack.append(namespace_match.group("name"))
            continue
        decl_match = DECL_RE.match(line)
        if decl_match:
            short = decl_match.group("name")
            starts.append((index, decl_match.group("kind"), short, join_name(namespace_stack, short)))
            continue
        if END_RE.match(line) and namespace_stack:
            namespace_stack.pop()
    return starts


def parse_declarations(path: Path, fixture: bool = False) -> list[Decl]:
    lines = path.read_text(encoding="utf-8").splitlines()
    starts = declaration_starts(path)
    decls: list[Decl] = []
    for offset, (line_no, kind, short_name, full_name) in enumerate(starts):
        next_line = starts[offset + 1][0] if offset + 1 < len(starts) else len(lines) + 1
        decls.append(
            Decl(
                path=path,
                line_no=line_no,
                kind=kind,
                short_name=short_name,
                full_name=full_name,
                block="\n".join(lines[line_no - 1 : next_line - 1]),
                fixture=fixture,
            )
        )
    return decls


def theorem_header(block: str) -> str:
    marker = block.find(":=")
    if marker < 0:
        return block
    return block[:marker]


def normalized_header(block: str) -> str:
    lines = [strip_line_comment(line) for line in theorem_header(block).splitlines()]
    return re.sub(r"\s+", " ", "\n".join(lines)).strip()


def canonical_path(repo_root: Path) -> Path:
    return (repo_root / CANONICAL_SOURCE).resolve()


def derived_path(repo_root: Path) -> Path:
    return repo_root / "lean4" / "BEDC" / "Derived"


def validate_canonical_source(repo_root: Path) -> list[str]:
    source = canonical_path(repo_root)
    if not source.exists():
        return [f"missing canonical source {CANONICAL_SOURCE}"]
    declared = {decl.base_name for decl in parse_declarations(source)}
    missing = sorted(CANONICAL_NAMES - declared)
    return [f"canonical source missing `{name}`" for name in missing]


def scan_files(repo_root: Path, fixture_paths: list[Path]) -> list[Path]:
    source = canonical_path(repo_root)
    files = [
        path.resolve()
        for path in sorted(derived_path(repo_root).rglob("*.lean"))
        if path.resolve() != source
    ]
    files.extend(path.resolve() for path in fixture_paths)
    return files


def is_intup_derived_path(repo_root: Path, path: Path) -> bool:
    if not path.exists():
        return False
    try:
        rel = path.resolve().relative_to(derived_path(repo_root).resolve())
    except ValueError:
        return False
    return bool(rel.parts) and rel.parts[0] == "IntUp"


def relpath(repo_root: Path, path: Path) -> Path:
    path = path.resolve()
    try:
        return path.relative_to(repo_root)
    except ValueError:
        return path


def find_violations(repo_root: Path, decls: list[Decl]) -> list[Violation]:
    violations: list[Violation] = []
    for decl in decls:
        if decl.full_name in ALLOWLIST:
            continue
        if decl.base_name in CANONICAL_NAMES:
            violations.append(
                Violation(
                    decl=decl,
                    pattern="canonical_name_collision",
                    detail=(
                        f"`{decl.base_name}` is an IntUp.CommRing canonical law name; "
                        "import and reuse the canonical declaration"
                    ),
                )
            )
            continue
        if decl.kind not in {"theorem", "lemma"}:
            continue
        if not decl.fixture and is_intup_derived_path(repo_root, decl.path):
            continue
        header = normalized_header(decl.block)
        for pattern_name, pattern, detail in LAW_SHAPES:
            if pattern.search(header):
                violations.append(
                    Violation(
                        decl=decl,
                        pattern=pattern_name,
                        detail=f"{detail}; reuse IntUp.CommRing instead",
                    )
                )
                break
    return violations


def main() -> int:
    fixture_paths = [Path(arg) for arg in sys.argv[1:]]
    try:
        bridge_root = find_bridge_root()
        repo_root = find_repo_root(bridge_root)
    except RuntimeError as exc:
        print(f"{TOKEN}: {exc}", file=sys.stderr)
        return 2

    source_errors = validate_canonical_source(repo_root)
    if source_errors:
        for error in source_errors:
            print(f"{TOKEN}: {error}", file=sys.stderr)
        return 2

    missing_fixtures = [path for path in fixture_paths if not path.exists()]
    if missing_fixtures:
        for path in missing_fixtures:
            print(f"{TOKEN}: missing fixture {path}", file=sys.stderr)
        return 2

    fixture_resolved = {path.resolve() for path in fixture_paths}
    decls: list[Decl] = []
    for path in scan_files(repo_root, fixture_paths):
        decls.extend(parse_declarations(path, fixture=path in fixture_resolved))

    violations = find_violations(repo_root, decls)
    if violations:
        for violation in violations:
            decl = violation.decl
            print(
                f"{relpath(repo_root, decl.path)}:{decl.line_no}: {TOKEN}: "
                f"{violation.pattern}: `{decl.full_name}`: {violation.detail}"
            )
        print(
            "[canonical-int-law] FAIL: "
            f"{len(violations)} local integer law hit(s); "
            "pattern1=canonical name collision; "
            "pattern2=heuristic high-confidence IntEq/IntAdd/IntMul law shapes; "
            f"allowlist={len(ALLOWLIST)}"
        )
        return 1

    audited = sum(1 for decl in decls if decl.kind in {"theorem", "lemma", "def"})
    print(
        "[canonical-int-law] PASS: "
        f"audited {audited} declaration(s); "
        "pattern1=canonical name collision; "
        "pattern2=heuristic high-confidence IntEq/IntAdd/IntMul law shapes; "
        f"allowlist={len(ALLOWLIST)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
