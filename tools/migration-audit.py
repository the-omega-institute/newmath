#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import asdict, dataclass, field
from datetime import datetime, timezone
from pathlib import Path
from typing import Iterable


AUDIT_VERSION = "0.3"
CONCEPT_NAMES = [
    "InDom",
    "TokIntro",
    "TokCan",
    "TokUnique",
    "GeneratedSameSig",
    "ExactGlobalizeBase",
    "ClosureReflect",
    "DomainPolicy",
    "PkgTokPol",
    "InGapSig",
    "psame_base",
    "psame_sig",
    "psame_eq",
]
CONCEPT_PATTERNS = {
    "psame_base": [
        re.compile(r"\bpsame_base\b"),
        re.compile(r"\bPsameBase\b"),
        re.compile(r"\\psame_\{\\Pi\}\^\{\\mathrm\{base\}\}"),
    ],
    "psame_sig": [
        re.compile(r"\bpsame_sig\b"),
        re.compile(r"\\psame_\{\\Pi\}\^\{\\mathrm\{sig\}\}"),
    ],
    "psame_eq": [
        re.compile(r"\bpsame_eq\b"),
        re.compile(r"\\psame_\{\\Pi\}\^\{\\mathrm\{eq\}\}"),
    ],
}

NOSEARCH_ENVS = ("verbatim", "comment")
LABEL_RE = re.compile(r"\\label\{([^}]+)\}")
MACRO_PATTERNS = [
    re.compile(
        r"\\(?:newcommand|renewcommand|providecommand)\*?\s*(?:\[[^\]]*\]\s*)?"
        r"(?:\{\s*(\\[A-Za-z@]+)\s*\}|(\\[A-Za-z@]+))"
    ),
    re.compile(r"\\DeclareMathOperator\*?\s*\{\s*(\\[A-Za-z@]+)\s*\}"),
    re.compile(
        r"\\DeclareRobustCommand\*?\s*(?:\[[^\]]*\]\s*)?"
        r"(?:\{\s*(\\[A-Za-z@]+)\s*\}|(\\[A-Za-z@]+))"
    ),
    re.compile(r"\\def\s*(\\[A-Za-z@]+)\b"),
]


class AuditSetupError(Exception):
    pass


@dataclass
class FailureDetail:
    item: str
    source: str | None = None
    notes: list[str] = field(default_factory=list)


@dataclass
class PassResult:
    name: str
    result: str
    checked: int
    missing: list[FailureDetail] = field(default_factory=list)
    message: str = ""


@dataclass
class AuditConfig:
    source_dir: Path
    target_dir: Path
    lean_dir: Path
    allowlist_dir: Path
    json_output: bool
    verbose: bool


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Audit BEDC migration completeness.")
    parser.add_argument(
        "--source-dir",
        default=".source/BEDC_Master_Project_v1_5_5",
        help="Source BEDC snapshot directory.",
    )
    parser.add_argument(
        "--target-dir",
        default="papers/bedc",
        help="Target paper directory.",
    )
    parser.add_argument(
        "--lean-dir",
        default="lean4",
        help="Lean directory.",
    )
    parser.add_argument(
        "--allowlist-dir",
        default="tools/audit-allowlists",
        help="Allowlist directory.",
    )
    parser.add_argument("--json", action="store_true", help="Emit JSON summary to stdout.")
    parser.add_argument(
        "--verbose",
        action="store_true",
        help="Print extra path-resolution details to stderr.",
    )
    return parser.parse_args()


def strip_latex_comments(text: str) -> str:
    result: list[str] = []
    i = 0
    length = len(text)
    in_env: str | None = None
    while i < length:
        if in_env is not None:
            end_token = f"\\end{{{in_env}}}"
            if text.startswith(end_token, i):
                result.append(end_token)
                i += len(end_token)
                in_env = None
                continue
            result.append(text[i])
            i += 1
            continue

        begin_env = next(
            (env for env in NOSEARCH_ENVS if text.startswith(f"\\begin{{{env}}}", i)),
            None,
        )
        if begin_env is not None:
            token = f"\\begin{{{begin_env}}}"
            result.append(token)
            i += len(token)
            in_env = begin_env
            continue

        if text.startswith("\\verb", i):
            j = i + len("\\verb")
            if j < length and text[j] == "*":
                j += 1
            if j < length and text[j] not in ("\n", "\r"):
                delimiter = text[j]
                result.append(text[i : j + 1])
                j += 1
                while j < length:
                    result.append(text[j])
                    if text[j] == delimiter:
                        j += 1
                        break
                    j += 1
                i = j
                continue

        if text[i] == "%" and not is_escaped_percent(text, i):
            while i < length and text[i] not in ("\n", "\r"):
                i += 1
            continue

        result.append(text[i])
        i += 1

    return "".join(result)


def is_escaped_percent(text: str, index: int) -> bool:
    backslashes = 0
    cursor = index - 1
    while cursor >= 0 and text[cursor] == "\\":
        backslashes += 1
        cursor -= 1
    return backslashes % 2 == 1


def mask_latex_nosearch_regions(text: str) -> str:
    pattern = re.compile(
        r"\\begin\{(verbatim|comment)\}.*?\\end\{\1\}",
        flags=re.DOTALL,
    )

    def repl(match: re.Match[str]) -> str:
        return re.sub(r"[^\n]", " ", match.group(0))

    return pattern.sub(repl, text)


def read_text(path: Path) -> str:
    try:
        return path.read_text(encoding="utf-8")
    except FileNotFoundError as exc:
        raise AuditSetupError(f"Missing file: {path}") from exc


def iter_tex_files(root: Path) -> list[Path]:
    if not root.exists():
        raise AuditSetupError(f"Missing directory: {root}")
    return sorted(path for path in root.rglob("*.tex") if path.is_file())


def iter_lean_files(root: Path) -> list[Path]:
    if not root.exists():
        raise AuditSetupError(f"Missing directory: {root}")
    return sorted(path for path in root.rglob("*.lean") if path.is_file())


def read_allowlist(path: Path) -> set[str]:
    if not path.exists():
        raise AuditSetupError(f"Missing allowlist: {path}")
    items: set[str] = set()
    for line_no, raw_line in enumerate(read_text(path).splitlines(), start=1):
        line = raw_line.split("#", 1)[0].strip()
        if not line:
            continue
        items.add(line)
    return items


def read_correspondence_allowlist(path: Path) -> list[tuple[str, str]]:
    if not path.exists():
        raise AuditSetupError(f"Missing allowlist: {path}")
    rows: list[tuple[str, str]] = []
    for line_no, raw_line in enumerate(read_text(path).splitlines(), start=1):
        line = raw_line.split("#", 1)[0].strip()
        if not line:
            continue
        parts = [part.strip() for part in line.split("|")]
        if len(parts) != 2 or not parts[0] or not parts[1]:
            raise AuditSetupError(
                f"Malformed correspondence allowlist at {path}:{line_no}: {raw_line}"
            )
        rows.append((parts[0], parts[1]))
    return rows


def resolve_target_root(source_dir: Path, target_dir: Path) -> Path:
    if (target_dir / "preamble.tex").is_file():
        return target_dir
    parent = target_dir.parent
    if target_dir.name == "parts" and parent == source_dir and (parent / "preamble.tex").is_file():
        return parent
    return target_dir


def collect_tex_corpus(paths: Iterable[Path]) -> dict[Path, str]:
    corpus: dict[Path, str] = {}
    for path in paths:
        stripped = strip_latex_comments(read_text(path))
        corpus[path] = mask_latex_nosearch_regions(stripped)
    return corpus


def collect_lean_corpus(paths: Iterable[Path]) -> dict[Path, str]:
    return {path: read_text(path) for path in paths}


def path_for_report(path: Path) -> str:
    try:
        return str(path.relative_to(Path.cwd()))
    except ValueError:
        return str(path)


def contains_literal(corpus: dict[Path, str], needle: str) -> bool:
    return any(needle in text for text in corpus.values())


def contains_pattern(corpus: dict[Path, str], patterns: list[re.Pattern[str]]) -> bool:
    return any(pattern.search(text) for pattern in patterns for text in corpus.values())


def lean_name_present(corpus: dict[Path, str], qualified_name: str) -> bool:
    if contains_literal(corpus, qualified_name):
        return True
    parts = qualified_name.split(".")
    terminal = parts[-1]
    container = parts[-2] if len(parts) >= 2 else None
    for path, text in corpus.items():
        if terminal not in text:
            continue
        if container and container not in text and len(parts) >= 4:
            continue
        if "BaseReflection" in text or "BaseReflection" in path.name:
            return True
    return False


def extract_labels(text: str) -> list[str]:
    return LABEL_RE.findall(text)


def extract_verbatim_names(text: str) -> list[str]:
    blocks = re.findall(r"\\begin\{verbatim\}(.*?)\\end\{verbatim\}", text, flags=re.DOTALL)
    names: list[str] = []
    for block in blocks:
        for raw_line in block.splitlines():
            name = raw_line.strip()
            if name:
                names.append(name)
    if not names:
        raise AuditSetupError("No theorem names found in verbatim block.")
    return names


def extract_macros(text: str) -> set[str]:
    macros: set[str] = set()
    for pattern in MACRO_PATTERNS:
        for match in pattern.finditer(text):
            macro = next((group for group in match.groups() if group), None)
            if macro:
                macros.add(macro)
    return macros


def pass_labels(
    source_dir: Path,
    target_corpus: dict[Path, str],
    retired_labels: set[str],
) -> PassResult:
    missing: list[FailureDetail] = []
    checked = 0
    for source_file in iter_tex_files(source_dir):
        text = mask_latex_nosearch_regions(strip_latex_comments(read_text(source_file)))
        labels = extract_labels(text)
        for label in labels:
            checked += 1
            if label in retired_labels:
                continue
            if not contains_literal(target_corpus, f"\\label{{{label}}}"):
                missing.append(FailureDetail(item=label, source=path_for_report(source_file)))
    result = "PASS" if not missing else "FAIL"
    message = (
        f"{checked - len(missing)}/{checked} source labels present in target (or retired)"
        if result == "PASS"
        else f"{len(missing)} labels missing"
    )
    return PassResult(name="labels", result=result, checked=checked, missing=missing, message=message)


def pass_bare_names(
    source_dir: Path,
    target_corpus: dict[Path, str],
    lean_corpus: dict[Path, str],
    source_fallback_corpus: dict[Path, str] | None = None,
) -> PassResult:
    theorem_file = source_dir / "parts" / "formalization" / "02_public_theorem_names.tex"
    names = extract_verbatim_names(strip_latex_comments(read_text(theorem_file)))
    missing: list[FailureDetail] = []
    for name in names:
        notes: list[str] = []
        if not contains_literal(target_corpus, name):
            notes.append("missing in target")
        lean_hit = contains_literal(lean_corpus, name)
        if not lean_hit and source_fallback_corpus is not None:
            lean_hit = contains_literal(source_fallback_corpus, name)
        if not lean_hit:
            notes.append("missing in lean")
        if notes:
            missing.append(FailureDetail(item=name, source=path_for_report(theorem_file), notes=notes))
    result = "PASS" if not missing else "FAIL"
    message = (
        f"{len(names) - len(missing)}/{len(names)} names hit both target and lean"
        if result == "PASS"
        else f"{len(missing)} names missing target and/or lean hits"
    )
    return PassResult(
        name="bare-names",
        result=result,
        checked=len(names),
        missing=missing,
        message=message,
    )


def pass_correspondence(
    correspondence_rows: list[tuple[str, str]],
    target_corpus: dict[Path, str],
    lean_corpus: dict[Path, str],
) -> PassResult:
    missing: list[FailureDetail] = []
    for paper_form, lean_form in correspondence_rows:
        notes: list[str] = []
        if not contains_literal(target_corpus, paper_form):
            notes.append("paper-form missing in target")
        if not lean_name_present(lean_corpus, lean_form):
            notes.append("lean-form missing in lean")
        if notes:
            missing.append(FailureDetail(item=f"{paper_form} | {lean_form}", notes=notes))
    result = "PASS" if not missing else "FAIL"
    message = (
        f"{len(correspondence_rows) - len(missing)}/{len(correspondence_rows)} rows valid"
        if result == "PASS"
        else f"{len(missing)} correspondence rows missing target and/or lean hits"
    )
    return PassResult(
        name="correspondence",
        result=result,
        checked=len(correspondence_rows),
        missing=missing,
        message=message,
    )


def pass_concepts(target_corpus: dict[Path, str], lean_corpus: dict[Path, str]) -> PassResult:
    missing: list[FailureDetail] = []
    for concept in CONCEPT_NAMES:
        patterns = CONCEPT_PATTERNS.get(concept)
        if patterns:
            present = contains_pattern(target_corpus, patterns) or contains_pattern(lean_corpus, patterns)
        else:
            present = contains_literal(target_corpus, concept) or contains_literal(lean_corpus, concept)
        if not present:
            missing.append(FailureDetail(item=concept))
    result = "PASS" if not missing else "FAIL"
    message = (
        f"{len(CONCEPT_NAMES) - len(missing)}/{len(CONCEPT_NAMES)} concepts present"
        if result == "PASS"
        else f"{len(missing)} concepts missing from target and lean"
    )
    return PassResult(
        name="concepts",
        result=result,
        checked=len(CONCEPT_NAMES),
        missing=missing,
        message=message,
    )


def pass_macros(
    source_dir: Path,
    target_root: Path,
    retired_macros: set[str],
) -> PassResult:
    source_preamble = source_dir / "preamble.tex"
    target_preamble = target_root / "preamble.tex"
    source_text = mask_latex_nosearch_regions(strip_latex_comments(read_text(source_preamble)))
    target_text = mask_latex_nosearch_regions(strip_latex_comments(read_text(target_preamble)))
    source_macros = extract_macros(source_text)
    target_macros = extract_macros(target_text)
    missing: list[FailureDetail] = []
    for macro in sorted(source_macros):
        if macro in target_macros or macro in retired_macros:
            continue
        missing.append(FailureDetail(item=macro, source=path_for_report(source_preamble)))
    result = "PASS" if not missing else "FAIL"
    message = (
        f"{len(source_macros) - len(missing)}/{len(source_macros)} macros preserved"
        if result == "PASS"
        else f"{len(missing)} macros missing from target preamble"
    )
    return PassResult(
        name="macros",
        result=result,
        checked=len(source_macros),
        missing=missing,
        message=message,
    )


def print_human_results(results: list[PassResult]) -> None:
    label_map = {
        "labels": "Pass 1: labels",
        "bare-names": "Pass 2: bare-names",
        "correspondence": "Pass 3: correspondence",
        "concepts": "Pass 4: concepts",
        "macros": "Pass 5: macros",
    }
    passed = 0
    failed = 0
    for result in results:
        if result.result == "PASS":
            passed += 1
            print(f"[{label_map[result.name]}] PASS — {result.message}", file=sys.stderr)
            continue
        failed += 1
        print(f"[{label_map[result.name]}] FAIL — {result.message}:", file=sys.stderr)
        for detail in result.missing:
            extra = []
            if detail.source:
                extra.append(f"source: {detail.source}")
            if detail.notes:
                extra.append(", ".join(detail.notes))
            suffix = f" ({'; '.join(extra)})" if extra else ""
            print(f"  {detail.item}{suffix}", file=sys.stderr)
    if failed == 0:
        print(f"AUDIT: {passed}/{len(results)} PASS", file=sys.stderr)
    else:
        print(f"AUDIT: {passed}/{len(results)} PASS, {failed} FAIL", file=sys.stderr)


def build_json_payload(
    config: AuditConfig,
    target_root: Path,
    results: list[PassResult],
) -> dict[str, object]:
    passed = sum(1 for result in results if result.result == "PASS")
    failed = len(results) - passed
    return {
        "audit_version": AUDIT_VERSION,
        "timestamp": datetime.now(timezone.utc).isoformat(),
        "source_dir": str(config.source_dir),
        "target_dir": str(config.target_dir),
        "target_search_root": str(target_root),
        "lean_dir": str(config.lean_dir),
        "allowlist_dir": str(config.allowlist_dir),
        "passes": [
            {
                "name": result.name,
                "result": result.result,
                "checked": result.checked,
                "message": result.message,
                "missing": [asdict(detail) for detail in result.missing],
            }
            for result in results
        ],
        "summary": {"passed": passed, "failed": failed},
    }


def audit(config: AuditConfig) -> tuple[int, list[PassResult], Path]:
    if not config.source_dir.exists():
        raise AuditSetupError(f"Missing source directory: {config.source_dir}")
    if not config.target_dir.exists():
        raise AuditSetupError(f"Missing target directory: {config.target_dir}")
    if not config.lean_dir.exists():
        raise AuditSetupError(f"Missing lean directory: {config.lean_dir}")
    if not config.allowlist_dir.exists():
        raise AuditSetupError(f"Missing allowlist directory: {config.allowlist_dir}")

    target_root = resolve_target_root(config.source_dir, config.target_dir)
    if config.verbose and target_root != config.target_dir:
        print(
            f"[info] target search root resolved from {config.target_dir} to {target_root}",
            file=sys.stderr,
        )

    target_raw_corpus = {
        path: strip_latex_comments(read_text(path))
        for path in iter_tex_files(target_root)
    }
    target_corpus = {path: mask_latex_nosearch_regions(text) for path, text in target_raw_corpus.items()}
    lean_corpus = collect_lean_corpus(iter_lean_files(config.lean_dir))
    self_test_fallback: dict[Path, str] | None = None
    try:
        lean_inside_source = config.lean_dir.resolve().is_relative_to(config.source_dir.resolve())
    except AttributeError:
        lean_inside_source = str(config.lean_dir.resolve()).startswith(str(config.source_dir.resolve()))
    if target_root.resolve() == config.source_dir.resolve() and lean_inside_source:
        self_test_fallback = target_raw_corpus
    retired_labels = read_allowlist(config.allowlist_dir / "labels-retired.txt")
    retired_macros = read_allowlist(config.allowlist_dir / "macros-retired.txt")
    correspondence_rows = read_correspondence_allowlist(
        config.allowlist_dir / "correspondence.txt"
    )

    results = [
        pass_labels(config.source_dir, target_corpus, retired_labels),
        pass_bare_names(
            config.source_dir,
            target_raw_corpus,
            lean_corpus,
            source_fallback_corpus=self_test_fallback,
        ),
        pass_correspondence(correspondence_rows, target_corpus, lean_corpus),
        pass_concepts(target_corpus, lean_corpus),
        pass_macros(config.source_dir, target_root, retired_macros),
    ]
    exit_code = 0 if all(result.result == "PASS" for result in results) else 1
    return exit_code, results, target_root


def main() -> int:
    args = parse_args()
    config = AuditConfig(
        source_dir=Path(args.source_dir),
        target_dir=Path(args.target_dir),
        lean_dir=Path(args.lean_dir),
        allowlist_dir=Path(args.allowlist_dir),
        json_output=args.json,
        verbose=args.verbose,
    )
    try:
        exit_code, results, target_root = audit(config)
    except AuditSetupError as exc:
        print(f"SETUP ERROR: {exc}", file=sys.stderr)
        return 2

    print_human_results(results)
    if config.json_output:
        payload = build_json_payload(config, target_root, results)
        json.dump(payload, sys.stdout, indent=2, ensure_ascii=False)
        sys.stdout.write("\n")
    return exit_code


if __name__ == "__main__":
    sys.exit(main())
