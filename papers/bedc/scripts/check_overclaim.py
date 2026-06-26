#!/usr/bin/env python3
"""Gate RH-facing prose against overclaim patterns."""

from __future__ import annotations

from dataclasses import dataclass
import json
from pathlib import Path
import re
import sys
from typing import Any, Iterable, Mapping


ROOT = Path(__file__).resolve().parents[1]
LEDGER_PATH = ROOT / "rh_claim_ledger.json"
SCAN_ROOT = ROOT / "parts"
VISION_SCAN_DIRS = (
    Path("parts/visions/rh"),
    Path("parts/visions/axiszeckendorf"),
    Path("parts/visions/reality_constrained"),
)

VALID_F3_CLASSES = frozenset(
    {"reparametrization", "substantive-equivalence", "conditional"}
)

F1_EXPORT_RE = re.compile(
    r"\b(?:constructive|bedc)\b.{0,90}\b(?:proof|witness)\b\s+(?:of|for)\s+"
    r"(?:the\s+)?(?:bedc[- ]?)?(?:rh|riemann\s+hypothesis)\b"
    r".{0,160}\b(?:supplies|yields|provides|produces|gives)\b",
    re.IGNORECASE,
)
F1_OBJECT_RE_LIST = (
    re.compile(r"\bzero[- ]?count(?:ing)?\b", re.IGNORECASE),
    re.compile(r"\briemann.{0,12}von.{0,12}mangoldt\b", re.IGNORECASE),
    re.compile(r"\btrivial[- ]?zero.{0,90}classif", re.IGNORECASE),
    re.compile(
        r"\b(?:lower\s+bound|barrier|β|beta\s*\(\s*n\s*\))\b"
        r".{0,180}\b(?:every|unbounded|all)\b.{0,120}\bstrip\b",
        re.IGNORECASE,
    ),
    re.compile(
        r"\b(?:every|unbounded|all)\b.{0,120}\bstrip\b.{0,180}"
        r"\b(?:lower\s+bound|barrier|β|beta\s*\(\s*n\s*\))\b",
        re.IGNORECASE,
    ),
)
F2_RE = re.compile(
    r"\b(?:necessarily|inherently|mathematically\s+requires?|must\s+"
    r"(?:use|invoke|appeal\s+to|depend\s+on|import|assume|require))\b"
    r".{0,180}\b(?:classical(?:\.choice)?|quot\.sound|propext|axiom)\b",
    re.IGNORECASE,
)
F3_RE = re.compile(
    r"\b(?:equivalent\s+to|if\s+and\s+only\s+if|iff|characteri[sz]es|"
    r"reparametri\w*)\b.{0,220}\b(?:bedc[- ]?rh|rh|riemann\s+hypothesis)\b"
    r"|"
    r"\b(?:bedc[- ]?rh|rh|riemann\s+hypothesis)\b\s+"
    r"(?:is|are|predicate\s+is|statement\s+is)\s+.{0,120}"
    r"\b(?:equivalent\s+to|if\s+and\s+only\s+if|iff|characteri[sz]es|"
    r"reparametri\w*)\b",
    re.IGNORECASE,
)
SCOPE_PROSE_RE = re.compile(
    r"\b(?:scope|scoped|local|readout|reparameteri[sz]ation|coordinate|surface|"
    r"fixed-line|fixed-half)\b",
    re.IGNORECASE,
)
PREFILTER_RE = re.compile(
    r"rh|riemann|hypothesis|classical|choice|quot\.sound|propext|axiom|"
    r"equivalent|iff|characteri|reparametri|constructive|bedc",
    re.IGNORECASE,
)


@dataclass(frozen=True)
class OverclaimFinding:
    file: str
    line: int
    family: str
    message: str
    excerpt: str

    def to_text(self) -> str:
        hint = (
            f"{self.file}:{self.line}: {self.family}: {self.message}\n"
            f"  excerpt: {self.excerpt}"
        )
        if "ledger" in self.message:
            hint += "\n  ledger hint: add file + nearby anchor to rh_claim_ledger.json, or rewrite the prose."
        return hint


@dataclass(frozen=True)
class LedgerEntry:
    file: str
    anchor: str
    claim_class: str
    structure_used: str
    scope_status: str
    note: str


def _normalize_file(path: str) -> str:
    text = str(path).replace("\\", "/")
    for prefix in ("papers/bedc/", "./"):
        if text.startswith(prefix):
            text = text[len(prefix) :]
    return text


def _coerce_entry(raw: Mapping[str, Any]) -> LedgerEntry | None:
    values: dict[str, str] = {}
    for key in ("file", "anchor", "claim_class", "structure_used", "scope_status", "note"):
        value = raw.get(key)
        if not isinstance(value, str) or not value.strip():
            return None
        values[key] = value.strip()
    values["file"] = _normalize_file(values["file"])
    return LedgerEntry(**values)


class OverclaimLedger:
    def __init__(self, entries: list[LedgerEntry], diagnostics: list[OverclaimFinding]):
        self.entries = entries
        self.diagnostics = diagnostics

    @classmethod
    def from_path(cls, path: Path, paper_root: Path = ROOT) -> "OverclaimLedger":
        diagnostics: list[OverclaimFinding] = []
        if not path.exists():
            diagnostics.append(
                OverclaimFinding(
                    _normalize_file(str(path.relative_to(paper_root) if path.is_relative_to(paper_root) else path)),
                    1,
                    "LEDGER",
                    "missing rh_claim_ledger.json",
                    "",
                )
            )
            return cls([], diagnostics)
        try:
            payload = json.loads(path.read_text(encoding="utf-8"))
        except json.JSONDecodeError as exc:
            return cls(
                [],
                [
                    OverclaimFinding(
                        _normalize_file(str(path.relative_to(paper_root) if path.is_relative_to(paper_root) else path)),
                        exc.lineno,
                        "LEDGER",
                        f"invalid JSON: {exc.msg}",
                        "",
                    )
                ],
            )
        if not isinstance(payload, Mapping):
            diagnostics.append(
                OverclaimFinding(_normalize_file(str(path)), 1, "LEDGER", "ledger root must be a JSON object", "")
            )
            return cls([], diagnostics)
        if payload.get("schema_id") != "bedc-rh-claim-ledger":
            diagnostics.append(
                OverclaimFinding(
                    _normalize_file(str(path.relative_to(paper_root) if path.is_relative_to(paper_root) else path)),
                    1,
                    "LEDGER",
                    "schema_id must be bedc-rh-claim-ledger",
                    "",
                )
            )
        raw_entries = payload.get("entries")
        if not isinstance(raw_entries, list):
            diagnostics.append(
                OverclaimFinding(
                    _normalize_file(str(path.relative_to(paper_root) if path.is_relative_to(paper_root) else path)),
                    1,
                    "LEDGER",
                    "entries must be a list",
                    "",
                )
            )
            return cls([], diagnostics)
        entries: list[LedgerEntry] = []
        seen: set[tuple[str, str]] = set()
        for index, raw in enumerate(raw_entries, start=1):
            if not isinstance(raw, Mapping):
                diagnostics.append(
                    OverclaimFinding(_normalize_file(str(path)), index, "LEDGER", "entry must be a JSON object", "")
                )
                continue
            entry = _coerce_entry(raw)
            if entry is None:
                diagnostics.append(
                    OverclaimFinding(
                        _normalize_file(str(path)),
                        index,
                        "LEDGER",
                        "entry must contain nonempty file, anchor, claim_class, structure_used, scope_status, note",
                        "",
                    )
                )
                continue
            key = (entry.file, entry.anchor)
            if key in seen:
                diagnostics.append(
                    OverclaimFinding(
                        _normalize_file(str(path)),
                        index,
                        "LEDGER",
                        f"duplicate file+anchor entry: {entry.file} :: {entry.anchor}",
                        "",
                    )
                )
                continue
            seen.add(key)
            entries.append(entry)
        return cls(entries, diagnostics)

    def matches(self, file: str, raw_context: str, normalized_context: str) -> list[LedgerEntry]:
        rel = _normalize_file(file)
        matches: list[LedgerEntry] = []
        for entry in self.entries:
            if entry.file != rel:
                continue
            anchor_norm = _normalize_tex(entry.anchor)
            if entry.anchor in raw_context or (anchor_norm and anchor_norm in normalized_context):
                matches.append(entry)
        return matches


def _paper_rel(path: Path, root: Path) -> str:
    try:
        return path.relative_to(root).as_posix()
    except ValueError:
        return path.as_posix()


def _normalize_tex(text: str) -> str:
    text = text.replace(r"\_", "_")
    replacements = {
        r"\beta": " beta ",
        r"\Beta": " beta ",
        r"\RH": " RH ",
    }
    for src, dst in replacements.items():
        text = text.replace(src, dst)
    for _ in range(4):
        text = re.sub(r"\\(?:mathsf|mathrm|texttt|operatorname|text|emph)\{([^{}]*)\}", r"\1", text)
    text = re.sub(r"\\(?:autoref|ref|label)\{([^{}]*)\}", " ", text)
    text = re.sub(r"\\[A-Za-z]+\*?", " ", text)
    text = text.replace("~", " ")
    text = re.sub(r"[$`{}_^]", " ", text)
    text = text.replace("--", "-")
    return re.sub(r"\s+", " ", text).strip().lower()


def _excerpt(line: str) -> str:
    text = re.sub(r"\s+", " ", line.strip())
    return text[:220]


def _window(lines: list[str], start: int, before: int = 42, after: int = 8) -> str:
    lo = max(0, start - before)
    hi = min(len(lines), start + after + 1)
    return "\n".join(lines[lo:hi])


def _forward_window(lines: list[str], start: int, count: int = 4) -> str:
    return "\n".join(lines[start : min(len(lines), start + count)])


def _text_blocks(lines: list[str]) -> Iterable[tuple[int, list[str]]]:
    start: int | None = None
    current: list[str] = []
    for index, line in enumerate(lines, start=1):
        if not line.strip():
            if current and start is not None:
                yield start, current
            start = None
            current = []
            continue
        if start is None:
            start = index
        current.append(line)
    if current and start is not None:
        yield start, current


def _first_content_excerpt(block_lines: list[str]) -> str:
    for line in block_lines:
        if line.strip() and not line.lstrip().startswith("%"):
            return _excerpt(line)
    return ""


def _line_excerpt(block_lines: list[str], start_line: int, line_no: int) -> str:
    index = line_no - start_line
    if 0 <= index < len(block_lines):
        return _excerpt(block_lines[index])
    return _first_content_excerpt(block_lines)


def _f1_hits(normalized: str) -> bool:
    return bool(F1_EXPORT_RE.search(normalized)) and any(
        pattern.search(normalized) for pattern in F1_OBJECT_RE_LIST
    )


def _f2_hits(normalized: str) -> bool:
    match = F2_RE.search(normalized)
    if not match:
        return False
    span = match.group(0)
    return not re.search(r"\bno\s+(?:use\s+of\s+)?(?:classical|classical\.choice|quot\.sound|propext|axiom)", span)


def _f3_hits(normalized: str) -> bool:
    return bool(F3_RE.search(normalized))


def _family_hits(family: str, normalized: str) -> bool:
    if family == "F1":
        return _f1_hits(normalized)
    if family == "F2":
        return _f2_hits(normalized)
    if family == "F3":
        return _f3_hits(normalized)
    return False


def _trigger_line(start_line: int, block_lines: list[str], family: str) -> int:
    for offset, line in enumerate(block_lines):
        if _family_hits(family, _normalize_tex(line)):
            return start_line + offset
    for offset in range(len(block_lines)):
        local = "\n".join(block_lines[offset : offset + 6])
        if _family_hits(family, _normalize_tex(local)):
            return start_line + offset
    return start_line


def _missing_ledger_finding(file: str, line: int, family: str, excerpt: str) -> OverclaimFinding:
    return OverclaimFinding(file, line, family, "trigger has no matching ledger entry", excerpt)


def _f3_validation_finding(
    file: str, line: int, excerpt: str, entry: LedgerEntry, reason: str
) -> OverclaimFinding:
    return OverclaimFinding(
        file,
        line,
        "F3",
        f"ledger entry for anchor '{entry.anchor}' is not valid: {reason}",
        excerpt,
    )


def _candidate_tex_files(paper_root: Path) -> list[Path]:
    candidates: set[Path] = set()
    for rel_dir in VISION_SCAN_DIRS:
        directory = paper_root / rel_dir
        if directory.is_dir():
            candidates.update(directory.rglob("*.tex"))
    parts_root = paper_root / "parts"
    if parts_root.is_dir():
        for tex in parts_root.rglob("*.tex"):
            rel = tex.relative_to(paper_root).as_posix().lower()
            if "rh" in rel or "riemann" in rel:
                candidates.add(tex)
    return sorted(candidates)


def _validate_f3_entries(
    entries: Iterable[LedgerEntry],
    normalized_context: str,
    *,
    file: str,
    line: int,
    excerpt: str,
) -> list[OverclaimFinding]:
    findings: list[OverclaimFinding] = []
    valid = False
    for entry in entries:
        if entry.claim_class not in VALID_F3_CLASSES:
            findings.append(
                _f3_validation_finding(
                    file,
                    line,
                    excerpt,
                    entry,
                    "claim_class must be reparametrization, substantive-equivalence, or conditional",
                )
            )
            continue
        if entry.claim_class == "reparametrization":
            if not entry.structure_used:
                findings.append(_f3_validation_finding(file, line, excerpt, entry, "structure_used is required"))
                continue
            if entry.scope_status != "scoped":
                findings.append(
                    _f3_validation_finding(file, line, excerpt, entry, "reparametrization requires scope_status=scoped")
                )
                continue
            if not SCOPE_PROSE_RE.search(normalized_context):
                findings.append(
                    _f3_validation_finding(
                        file,
                        line,
                        excerpt,
                        entry,
                        "nearby prose must state the scope of the reparametrization",
                    )
                )
                continue
        valid = True
    return [] if valid else findings


def scan_overclaims(paper_root: Path = ROOT, ledger: OverclaimLedger | None = None) -> list[OverclaimFinding]:
    if ledger is None:
        ledger = OverclaimLedger.from_path(paper_root / "rh_claim_ledger.json", paper_root)
    findings: list[OverclaimFinding] = []
    seen: set[tuple[str, int, str]] = set()
    for tex in _candidate_tex_files(paper_root):
        rel = _paper_rel(tex, paper_root)
        lines = tex.read_text(encoding="utf-8").splitlines()
        for start_line, block_lines in _text_blocks(lines):
            block_text = "\n".join(block_lines)
            if all(line.lstrip().startswith("%") for line in block_lines):
                continue
            if all(line.lstrip().startswith(r"\concretizedIn") for line in block_lines):
                continue
            if not PREFILTER_RE.search(block_text):
                continue
            normalized_forward = _normalize_tex(block_text)
            checks = [
                ("F1", _f1_hits(normalized_forward)),
                ("F2", _f2_hits(normalized_forward)),
                ("F3", _f3_hits(normalized_forward)),
            ]
            for family, hit in checks:
                if not hit:
                    continue
                raw_context = _window(lines, start_line - 1)
                normalized_context = _normalize_tex(raw_context)
                key = (rel, start_line, family)
                if key in seen:
                    continue
                seen.add(key)
                trigger_line = _trigger_line(start_line, block_lines, family)
                excerpt = _line_excerpt(block_lines, start_line, trigger_line)
                if family == "F2":
                    findings.append(
                        OverclaimFinding(
                            rel,
                            trigger_line,
                            family,
                            "axiom-necessity wording must be rewritten as an implementation footprint claim",
                            excerpt,
                        )
                    )
                    continue
                matches = ledger.matches(rel, raw_context, normalized_context)
                if not matches:
                    findings.append(_missing_ledger_finding(rel, trigger_line, family, excerpt))
                    continue
                if family == "F3":
                    findings.extend(
                        _validate_f3_entries(
                            matches,
                            normalized_context,
                            file=rel,
                            line=trigger_line,
                            excerpt=excerpt,
                        )
                    )
    return findings


def main() -> int:
    ledger = OverclaimLedger.from_path(LEDGER_PATH, ROOT)
    findings = ledger.diagnostics + scan_overclaims(ROOT, ledger)
    if not findings:
        return 0
    print("BEDC anti-overclaim gate failed:", file=sys.stderr)
    for finding in findings:
        print(finding.to_text(), file=sys.stderr)
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
