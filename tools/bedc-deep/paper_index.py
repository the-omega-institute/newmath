#!/usr/bin/env python3
"""Build a compact BEDC paper index for prompt grounding."""

from __future__ import annotations

import argparse
import json
import os
import re
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parents[1]
PARTS_DIR = REPO_ROOT / "papers" / "bedc" / "parts"
STATE_DIR = SCRIPT_DIR / "state"
INDEX_PATH = STATE_DIR / "paper_index.json"

THEOREM_LIKE_ENVS = {"theorem", "lemma", "proposition", "corollary", "definition"}
ENV_RE = re.compile(r"\\begin\{([A-Za-z*]+)\}(?:\[([^\]]*)\])?")
LABEL_RE = re.compile(r"\\label\{([^}]+)\}")
INPUT_RE = re.compile(r"\\(?:input|include)\{([^}]+)\}")
CLOSURE_RE = re.compile(r"\\begin\{closurestatus\}\{([^}]*)\}")
LEAN_MARKER_RE = re.compile(r"\\lean(?:checked|variant|stmt|def|sorryd)\{")


def _now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def _repo_rel(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT))


def _line_for_offset(text: str, offset: int) -> int:
    return text.count("\n", 0, offset) + 1


def _prefix(label: str) -> str:
    return label.split(":", 1)[0] if ":" in label else ""


def _scan_file(path: Path) -> dict[str, Any]:
    text = path.read_text(encoding="utf-8", errors="replace")
    rel = _repo_rel(path)
    lines = text.splitlines()
    env_counts: dict[str, int] = {}
    labels: list[dict[str, Any]] = []
    theorem_like_labels: list[dict[str, Any]] = []

    env_starts: list[tuple[int, str, str]] = []
    for match in ENV_RE.finditer(text):
        env = match.group(1)
        title = (match.group(2) or "").strip()
        env_counts[env] = env_counts.get(env, 0) + 1
        env_starts.append((match.start(), env, title))

    env_starts.sort()
    env_idx = 0
    for match in LABEL_RE.finditer(text):
        env = ""
        title = ""
        while env_idx + 1 < len(env_starts) and env_starts[env_idx + 1][0] < match.start():
            env_idx += 1
        if env_starts and env_starts[env_idx][0] < match.start():
            env = env_starts[env_idx][1]
            title = env_starts[env_idx][2]
        label = match.group(1)
        rec = {
            "label": label,
            "prefix": _prefix(label),
            "env": env,
            "title": title,
            "file": rel,
            "line": _line_for_offset(text, match.start()),
        }
        labels.append(rec)
        if env in THEOREM_LIKE_ENVS or rec["prefix"] in {"thm", "lem", "prop", "cor", "def"}:
            theorem_like_labels.append(rec)

    input_count = len(INPUT_RE.findall(text))
    substantive_envs = sum(env_counts.get(env, 0) for env in THEOREM_LIKE_ENVS)
    closure_objects = [match.group(1) for match in CLOSURE_RE.finditer(text)]

    return {
        "file": rel,
        "line_count": len(lines),
        "input_count": input_count,
        "hub_like": input_count > 0 and substantive_envs == 0,
        "near_line_cap": len(lines) >= 760,
        "env_counts": env_counts,
        "labels": labels,
        "theorem_like_labels": theorem_like_labels,
        "closurestatus_count": len(closure_objects),
        "closurestatus_objects": closure_objects[:20],
        "lean_marker_count": len(LEAN_MARKER_RE.findall(text)),
    }


def build_index() -> dict[str, Any]:
    files: list[dict[str, Any]] = []
    labels: list[dict[str, Any]] = []
    theorem_like_labels: list[dict[str, Any]] = []
    label_prefix_counts: dict[str, int] = {}
    theme_counts: dict[str, dict[str, int]] = {}

    if PARTS_DIR.exists():
        for path in sorted(PARTS_DIR.rglob("*.tex")):
            item = _scan_file(path)
            files.append(item)
            labels.extend(item["labels"])
            theorem_like_labels.extend(item["theorem_like_labels"])

            rel_parts = Path(item["file"]).parts
            theme = rel_parts[3] if len(rel_parts) > 3 else "(root)"
            bucket = theme_counts.setdefault(theme, {"files": 0, "labels": 0, "theorem_like_labels": 0})
            bucket["files"] += 1
            bucket["labels"] += len(item["labels"])
            bucket["theorem_like_labels"] += len(item["theorem_like_labels"])

    for rec in labels:
        prefix = rec.get("prefix") or "(none)"
        label_prefix_counts[prefix] = label_prefix_counts.get(prefix, 0) + 1

    near_line_cap = [
        {"file": item["file"], "line_count": item["line_count"]}
        for item in files
        if item["near_line_cap"]
    ]
    hub_files = [
        {"file": item["file"], "input_count": item["input_count"]}
        for item in files
        if item["hub_like"]
    ]
    closure_files = [
        {"file": item["file"], "closurestatus_count": item["closurestatus_count"]}
        for item in files
        if item["closurestatus_count"]
    ]

    return {
        "generated_at": _now_iso(),
        "parts_dir": _repo_rel(PARTS_DIR),
        "summary": {
            "files": len(files),
            "labels": len(labels),
            "theorem_like_labels": len(theorem_like_labels),
            "label_prefix_counts": dict(sorted(label_prefix_counts.items())),
            "theme_counts": dict(sorted(theme_counts.items())),
            "near_line_cap_files": near_line_cap,
            "hub_files": hub_files,
            "closurestatus_files": closure_files,
        },
        "files": files,
        "labels": labels,
        "theorem_like_labels": theorem_like_labels,
    }


def save_index(index: dict[str, Any], path: Path = INDEX_PATH) -> Path:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_name(f"{path.name}.{os.getpid()}.tmp")
    tmp.write_text(json.dumps(index, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    tmp.replace(path)
    return path


def load_or_build(*, refresh: bool = True) -> dict[str, Any]:
    if not refresh and INDEX_PATH.exists():
        try:
            return json.loads(INDEX_PATH.read_text(encoding="utf-8"))
        except json.JSONDecodeError:
            pass
    index = build_index()
    save_index(index)
    return index


def _label_sort_key(rec: dict[str, Any]) -> tuple[int, str]:
    match = re.search(r"(\d+)", rec.get("file", ""))
    file_number = int(match.group(1)) if match else -1
    return (file_number, rec.get("label", ""))


def render_prompt_summary(index: dict[str, Any] | None = None, *, max_chars: int = 12000) -> str:
    idx = index or load_or_build()
    summary = idx.get("summary") or {}
    lines: list[str] = [
        "PAPER_INDEX compact coverage.",
        f"generated_at={idx.get('generated_at', '')}",
        (
            f"files={summary.get('files', 0)} labels={summary.get('labels', 0)} "
            f"theorem_like_labels={summary.get('theorem_like_labels', 0)}"
        ),
        "",
        "## Label Prefix Counts",
    ]

    for key, value in (summary.get("label_prefix_counts") or {}).items():
        lines.append(f"- {key}: {value}")

    lines.extend(["", "## Theme Counts"])
    for theme, counts in (summary.get("theme_counts") or {}).items():
        lines.append(
            f"- {theme}: files={counts.get('files', 0)} "
            f"labels={counts.get('labels', 0)} theorem_like={counts.get('theorem_like_labels', 0)}"
        )

    lines.extend(["", "## Near Line Cap Files"])
    near = summary.get("near_line_cap_files") or []
    if near:
        for item in near[:40]:
            lines.append(f"- {item.get('file')} lines={item.get('line_count')}")
    else:
        lines.append("(none)")

    lines.extend(["", "## Hub Files"])
    hubs = summary.get("hub_files") or []
    if hubs:
        for item in hubs[:80]:
            lines.append(f"- {item.get('file')} inputs={item.get('input_count')}")
    else:
        lines.append("(none)")

    lines.extend(["", "## Recent / High-Numbered Theorem-Like Labels"])
    labels = sorted(idx.get("theorem_like_labels") or [], key=_label_sort_key, reverse=True)
    for rec in labels[:260]:
        title = rec.get("title") or ""
        title_part = f" title={title}" if title else ""
        lines.append(
            f"- {rec.get('label')} env={rec.get('env')} "
            f"{rec.get('file')}:{rec.get('line')}{title_part}"
        )

    text = "\n".join(lines)
    if len(text) > max_chars:
        return text[: max_chars - 80].rstrip() + "\n... (paper index truncated by prompt cap)"
    return text


def main() -> int:
    parser = argparse.ArgumentParser(description="Build BEDC paper_index.json")
    parser.add_argument("--summary", action="store_true", help="Print compact prompt summary")
    parser.add_argument("--max-chars", type=int, default=12000)
    args = parser.parse_args()

    index = build_index()
    path = save_index(index)
    if args.summary:
        print(render_prompt_summary(index, max_chars=args.max_chars))
    else:
        summary = index["summary"]
        print(
            f"wrote {path} files={summary['files']} labels={summary['labels']} "
            f"theorem_like_labels={summary['theorem_like_labels']}"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
