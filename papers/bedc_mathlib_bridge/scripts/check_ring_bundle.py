#!/usr/bin/env python3
from __future__ import annotations

from collections import defaultdict
from dataclasses import dataclass
import json
from pathlib import Path
import re
import sys


TOKEN = "BEDC_GATE_B_DUP_RING_BUNDLE"

DECL_RE = re.compile(
    r"^\s*(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*"
    r"(?P<kind>instance|def|abbrev)\s+"
    r"(?:(?P<name>[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*)\s+)?"
)
NAMESPACE_RE = re.compile(
    r"^\s*namespace\s+"
    r"(?P<name>[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*)\b"
)
END_RE = re.compile(
    r"^\s*end(?:\s+[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*)?\s*$"
)
RELCOMMRING_RE = re.compile(
    r":\s*(?:[A-Za-z_][A-Za-z0-9_']*\.)*RelCommRing\s+"
    r"(?P<carrier>[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*)\s+"
    r"(?P<eq>[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*)\b",
    re.DOTALL,
)
CONSTRUCTOR_LITERAL_RE = re.compile(r"\bwhere\b|:=\s*\{", re.DOTALL)


@dataclass(frozen=True)
class BundleDecl:
    path: Path
    line_no: int
    kind: str
    short_name: str
    full_name: str
    carrier: str
    eq: str
    fixture: bool

    @property
    def key(self) -> str:
        return f"{self.carrier}|{self.eq}"


@dataclass(frozen=True)
class Manifest:
    aliases: dict[str, str]
    owners: dict[str, frozenset[str]]
    wrappers: dict[str, str]


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


def load_manifest(bridge_root: Path) -> Manifest:
    path = bridge_root / "canonical_manifest.json"
    try:
        raw = json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError as exc:
        raise RuntimeError(f"missing canonical manifest {path}") from exc
    except json.JSONDecodeError as exc:
        raise RuntimeError(f"invalid canonical manifest JSON: {exc}") from exc
    aliases_raw = raw.get("aliases", {})
    owners_raw = raw.get("ring_bundle_owners", {})
    wrappers_raw = raw.get("ring_bundle_wrappers", {})
    if not isinstance(aliases_raw, dict):
        raise RuntimeError("canonical manifest `aliases` must be an object")
    if not isinstance(owners_raw, dict):
        raise RuntimeError("canonical manifest `ring_bundle_owners` must be an object")
    if not isinstance(wrappers_raw, dict):
        raise RuntimeError("canonical manifest `ring_bundle_wrappers` must be an object")
    owners: dict[str, frozenset[str]] = {}
    for key, value in owners_raw.items():
        if not isinstance(value, list) or not all(isinstance(item, str) for item in value):
            raise RuntimeError(f"ring_bundle_owners `{key}` must be a string array")
        owners[str(key)] = frozenset(value)
    return Manifest(
        aliases={str(key): str(value) for key, value in aliases_raw.items()},
        owners=owners,
        wrappers={str(key): str(value) for key, value in wrappers_raw.items()},
    )


def strip_line_comment(line: str) -> str:
    return line.split("--", 1)[0]


def join_name(namespace_stack: list[str], name: str) -> str:
    if "." in name:
        return name
    if not namespace_stack:
        return name
    return ".".join([*namespace_stack, name])


def pop_namespace(namespace_stack: list[str], line: str) -> None:
    if END_RE.match(line) and namespace_stack:
        namespace_stack.pop()


def synthetic_instance_name(path: Path, line_no: int) -> str:
    return f"{path.stem}.anonymous_instance_line_{line_no}"


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
            kind = decl.group("kind")
            short = decl.group("name") or synthetic_instance_name(path, index)
            starts.append((index, kind, short, join_name(namespace_stack, short)))
            continue
        pop_namespace(namespace_stack, line)
    return starts


def normalize_name(name: str, manifest: Manifest) -> str:
    return manifest.aliases.get(name, name)


def parse_bundles(path: Path, manifest: Manifest, fixture: bool) -> list[BundleDecl]:
    lines = path.read_text(encoding="utf-8").splitlines()
    starts = declaration_starts(path)
    out: list[BundleDecl] = []
    for offset, (line_no, kind, short_name, full_name) in enumerate(starts):
        next_line = starts[offset + 1][0] if offset + 1 < len(starts) else len(lines) + 1
        block = "\n".join(strip_line_comment(line) for line in lines[line_no - 1 : next_line - 1])
        match = RELCOMMRING_RE.search(block)
        if match is None:
            continue
        if CONSTRUCTOR_LITERAL_RE.search(block) is None:
            continue
        out.append(
            BundleDecl(
                path=path,
                line_no=line_no,
                kind=kind,
                short_name=short_name,
                full_name=full_name,
                carrier=normalize_name(match.group("carrier"), manifest),
                eq=normalize_name(match.group("eq"), manifest),
                fixture=fixture,
            )
        )
    return out


def scan_files(repo_root: Path, fixture_paths: list[Path]) -> list[Path]:
    files: list[Path] = []
    rel_dir = repo_root / "lean4" / "BEDC" / "Algebra" / "Rel"
    if rel_dir.exists():
        files.extend(sorted(rel_dir.rglob("*.lean")))
    derived_dir = repo_root / "lean4" / "BEDC" / "Derived"
    if derived_dir.exists():
        files.extend(sorted(derived_dir.rglob("*.lean")))
    files.extend(fixture_paths)
    return sorted({path.resolve() for path in files})


def relpath(repo_root: Path, path: Path) -> Path:
    try:
        return path.resolve().relative_to(repo_root)
    except ValueError:
        return path


def find_violations(manifest: Manifest, bundles: list[BundleDecl]) -> dict[str, list[BundleDecl]]:
    by_key: dict[str, list[BundleDecl]] = defaultdict(list)
    for bundle in bundles:
        if bundle.full_name in manifest.wrappers:
            continue
        if bundle.full_name in manifest.owners.get(bundle.key, frozenset()):
            by_key[bundle.key].append(bundle)
            continue
        by_key[bundle.key].append(bundle)
    return {key: value for key, value in by_key.items() if len(value) > 1}


def main() -> int:
    fixture_paths = [Path(arg).resolve() for arg in sys.argv[1:]]
    try:
        bridge_root = find_bridge_root()
        repo_root = find_repo_root(bridge_root)
        manifest = load_manifest(bridge_root)
    except RuntimeError as exc:
        print(f"{TOKEN}: {exc}", file=sys.stderr)
        return 2

    missing = [path for path in fixture_paths if not path.exists()]
    if missing:
        for path in missing:
            print(f"{TOKEN}: missing fixture {path}", file=sys.stderr)
        return 2

    fixtures = set(fixture_paths)
    bundles: list[BundleDecl] = []
    for path in scan_files(repo_root, fixture_paths):
        bundles.extend(parse_bundles(path, manifest, fixture=path in fixtures))

    violations = find_violations(manifest, bundles)
    if violations:
        for key, decls in sorted(violations.items()):
            print(f"{TOKEN}: duplicate RelCommRing constructor bundle for {key}")
            for decl in decls:
                print(
                    f"{relpath(repo_root, decl.path)}:{decl.line_no}: "
                    f"{decl.kind} `{decl.full_name}`"
                )
        print(
            "[ring-bundle] FAIL: "
            f"{sum(len(v) for v in violations.values())} bundle declaration(s) "
            f"across {len(violations)} duplicated carrier/equality pair(s); "
            f"manifest_wrappers={len(manifest.wrappers)}"
        )
        return 1

    print(
        "[ring-bundle] PASS: "
        f"audited {len(bundles)} RelCommRing constructor bundle(s); "
        "each carrier/equality pair has at most one non-wrapper source; "
        f"manifest_wrappers={len(manifest.wrappers)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
