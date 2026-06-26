#!/usr/bin/env python3
from __future__ import annotations

from collections import defaultdict
from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
import re
import sys


TOKEN = "BEDC_GATE_S_DUP_STATEMENT"

DECL_RE = re.compile(
    r"^\s*(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*"
    r"(?P<kind>theorem|lemma)\s+"
    r"(?P<name>[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*)\b"
)
NAMESPACE_RE = re.compile(
    r"^\s*namespace\s+"
    r"(?P<name>[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*)\b"
)
END_RE = re.compile(
    r"^\s*end(?:\s+[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*)?\s*$"
)
RING_HEAD_RE = re.compile(
    r"\b(?:IntEq|Zeq|GaussEq|EisEq|RelRing|RelCommRing|IntAdd|Zadd|IntMul|Zmul|"
    r"IntNeg|Zneg|gaussAdd|gaussMul|gaussNeg|eisAdd|eisMul|eisNeg)\b"
)
BINDER_RE = re.compile(r"\((?P<names>[A-Za-z_][A-Za-z0-9_'\s]*)\s*:\s*(?P<type>[^(){}[\]:=]+)\)")
IDENT_RE = re.compile(r"\b[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*\b")


@dataclass(frozen=True)
class Decl:
    path: Path
    line_no: int
    kind: str
    short_name: str
    full_name: str
    block: str
    fixture: bool


@dataclass(frozen=True)
class DigestHit:
    decl: Decl
    digest: str
    normalized: str


@dataclass(frozen=True)
class Manifest:
    canonical_files: frozenset[Path]
    owners: frozenset[str]
    wrappers: dict[str, str]
    aliases: dict[str, str]


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


def load_manifest(bridge_root: Path, repo_root: Path) -> Manifest:
    path = bridge_root / "canonical_manifest.json"
    try:
        raw = json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError as exc:
        raise RuntimeError(f"missing canonical manifest {path}") from exc
    except json.JSONDecodeError as exc:
        raise RuntimeError(f"invalid canonical manifest JSON: {exc}") from exc
    canonical_files = frozenset((repo_root / item).resolve() for item in raw.get("canonical_files", []))
    wrappers: dict[str, str] = {}
    for field in ("wrappers", "ring_bundle_wrappers"):
        value = raw.get(field, {})
        if not isinstance(value, dict):
            raise RuntimeError(f"canonical manifest `{field}` must be an object")
        wrappers.update({str(key): str(item) for key, item in value.items()})
    aliases_raw = raw.get("aliases", {})
    if not isinstance(aliases_raw, dict):
        raise RuntimeError("canonical manifest `aliases` must be an object")
    return Manifest(
        canonical_files=canonical_files,
        owners=frozenset(raw.get("owners", [])),
        wrappers=wrappers,
        aliases={str(key): str(value) for key, value in aliases_raw.items()},
    )


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
        ns = NAMESPACE_RE.match(line)
        if ns:
            namespace_stack.extend(ns.group("name").split("."))
            continue
        decl = DECL_RE.match(line)
        if decl:
            short = decl.group("name")
            starts.append((index, decl.group("kind"), short, join_name(namespace_stack, short)))
            continue
        if END_RE.match(line) and namespace_stack:
            namespace_stack.pop()
    return starts


def parse_declarations(path: Path, fixture: bool) -> list[Decl]:
    lines = path.read_text(encoding="utf-8").splitlines()
    starts = declaration_starts(path)
    out: list[Decl] = []
    for offset, (line_no, kind, short_name, full_name) in enumerate(starts):
        next_line = starts[offset + 1][0] if offset + 1 < len(starts) else len(lines) + 1
        out.append(
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
    return out


def theorem_header(block: str) -> str:
    marker = block.find(":=")
    return block if marker < 0 else block[:marker]


def first_top_level_colon(text: str) -> int:
    depth = 0
    for index, char in enumerate(text):
        if char in "([{":
            depth += 1
        elif char in ")]}" and depth > 0:
            depth -= 1
        elif char == ":" and depth == 0:
            return index
    return -1


def statement_text(block: str) -> str:
    header = "\n".join(strip_line_comment(line) for line in theorem_header(block).splitlines())
    colon = first_top_level_colon(header)
    if colon < 0:
        return ""
    return header[colon + 1 :].strip()


def binder_renames(header: str) -> dict[str, str]:
    renames: dict[str, str] = {}
    counter = 0
    for match in BINDER_RE.finditer(header):
        names = [item for item in match.group("names").split() if item]
        type_text = re.sub(r"\s+", " ", match.group("type")).strip()
        if not names or not type_text:
            continue
        for name in names:
            if name not in renames:
                renames[name] = f"v{counter}"
                counter += 1
    return renames


def replace_identifiers(text: str, replacements: dict[str, str]) -> str:
    def repl(match: re.Match[str]) -> str:
        token = match.group(0)
        return replacements.get(token, token)

    return IDENT_RE.sub(repl, text)


def normalize_statement(decl: Decl, manifest: Manifest) -> str | None:
    header = "\n".join(strip_line_comment(line) for line in theorem_header(decl.block).splitlines())
    stmt = statement_text(decl.block)
    if not stmt or RING_HEAD_RE.search(stmt) is None:
        return None
    stmt = replace_identifiers(stmt, manifest.aliases)
    stmt = replace_identifiers(stmt, binder_renames(header))
    stmt = re.sub(r"\s+", " ", stmt).strip()
    stmt = stmt.replace(" -> ", " → ")
    return stmt


def digest_statement(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()[:16]


def scan_files(repo_root: Path, manifest: Manifest, fixture_paths: list[Path]) -> list[Path]:
    files: list[Path] = []
    rel_dir = repo_root / "lean4" / "BEDC" / "Algebra" / "Rel"
    if rel_dir.exists():
        files.extend(path for path in sorted(rel_dir.rglob("*.lean")) if path.resolve() not in manifest.canonical_files)
    intup_dir = repo_root / "lean4" / "BEDC" / "Derived" / "IntUp"
    if intup_dir.exists():
        files.extend(path for path in sorted(intup_dir.rglob("*.lean")) if path.resolve() not in manifest.canonical_files)
    files.extend(fixture_paths)
    return sorted({path.resolve() for path in files})


def relpath(repo_root: Path, path: Path) -> Path:
    try:
        return path.resolve().relative_to(repo_root)
    except ValueError:
        return path


def non_wrapper_hit(hit: DigestHit, manifest: Manifest) -> bool:
    decl = hit.decl
    return decl.fixture or (decl.full_name not in manifest.owners and decl.full_name not in manifest.wrappers)


def main() -> int:
    fixture_paths = [Path(arg).resolve() for arg in sys.argv[1:]]
    try:
        bridge_root = find_bridge_root()
        repo_root = find_repo_root(bridge_root)
        manifest = load_manifest(bridge_root, repo_root)
    except RuntimeError as exc:
        print(f"{TOKEN}: {exc}", file=sys.stderr)
        return 2

    missing = [path for path in fixture_paths if not path.exists()]
    if missing:
        for path in missing:
            print(f"{TOKEN}: missing fixture {path}", file=sys.stderr)
        return 2

    fixture_set = set(fixture_paths)
    hits_by_digest: dict[str, list[DigestHit]] = defaultdict(list)
    audited = 0
    for path in scan_files(repo_root, manifest, fixture_paths):
        for decl in parse_declarations(path, fixture=path in fixture_set):
            normalized = normalize_statement(decl, manifest)
            if normalized is None:
                continue
            audited += 1
            digest = digest_statement(normalized)
            hits_by_digest[digest].append(DigestHit(decl, digest, normalized))

    violations = {
        digest: [hit for hit in hits if non_wrapper_hit(hit, manifest)]
        for digest, hits in hits_by_digest.items()
    }
    violations = {digest: hits for digest, hits in violations.items() if len(hits) > 1}
    if violations:
        for digest, hits in sorted(violations.items()):
            print(f"{TOKEN}: duplicate ring-law statement digest {digest}")
            print(f"  normalized: {hits[0].normalized}")
            for hit in hits:
                decl = hit.decl
                print(
                    f"  {relpath(repo_root, decl.path)}:{decl.line_no}: "
                    f"{decl.kind} `{decl.full_name}`"
                )
        print(
            "[statement-shape] FAIL: "
            f"{sum(len(hits) for hits in violations.values())} duplicated non-wrapper "
            f"ring-law-shaped declaration(s) across {len(violations)} digest(s)"
        )
        return 1

    print(
        "[statement-shape] PASS: "
        f"audited {audited} ring-law-shaped theorem/lemma statement(s); "
        "coverage=source-level heuristic with binder/alias/whitespace normalization, "
        "not full Lean environment type normalization"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
