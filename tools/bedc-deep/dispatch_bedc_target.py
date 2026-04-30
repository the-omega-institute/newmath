#!/usr/bin/env python3
"""Build BEDC deep-reasoning prompts from BOARD.md.

This script is intentionally read-only for the repository theory surface. It
does not run Lean, does not call Lake, and does not edit project source files.
"""

from __future__ import annotations

import argparse
import json
import re
from dataclasses import asdict, dataclass
from pathlib import Path


SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parents[1]
BOARD_PATH = SCRIPT_DIR / "BOARD.md"
MAX_CONTEXT_FILE_CHARS = 12000
MAX_CONTEXT_TOTAL_CHARS = 36000


@dataclass
class BedcTarget:
    target_id: str
    title: str
    fields: dict[str, str]
    body: str

    @property
    def slug(self) -> str:
        words = re.findall(r"[a-z0-9]+", self.title.lower())
        return f"{self.target_id.lower()}_{'_'.join(words[:5])}"


TARGET_HEADER = re.compile(r"^### (B-\d+)\s+-\s+(.+)$", re.MULTILINE)
TABLE_ROW = re.compile(r"^\|\s*([^|]+?)\s*\|\s*([^|]+?)\s*\|\s*$", re.MULTILINE)


def parse_board(path: Path = BOARD_PATH) -> dict[str, BedcTarget]:
    text = path.read_text(encoding="utf-8")
    matches = list(TARGET_HEADER.finditer(text))
    targets: dict[str, BedcTarget] = {}
    for i, match in enumerate(matches):
        start = match.end()
        end = matches[i + 1].start() if i + 1 < len(matches) else len(text)
        body = text[start:end].strip()
        fields: dict[str, str] = {}
        for row in TABLE_ROW.finditer(body):
            key = row.group(1).strip()
            value = row.group(2).strip()
            if key.lower() in {"field", "---"} or value == "---":
                continue
            fields[key] = value
        target = BedcTarget(
            target_id=match.group(1),
            title=match.group(2).strip(),
            fields=fields,
            body=body,
        )
        targets[target.target_id] = target
    return targets


def _extract_local_input_paths(target: BedcTarget) -> list[str]:
    paths: list[str] = []
    in_inputs = False
    for raw_line in target.body.splitlines():
        line = raw_line.strip()
        if line == "Local inputs:":
            in_inputs = True
            continue
        if in_inputs and not line:
            continue
        if in_inputs and not line.startswith("-"):
            break
        if in_inputs:
            m = re.search(r"`([^`]+)`", line)
            if m:
                paths.append(m.group(1))
    return paths


def _safe_context_path(rel: str) -> Path | None:
    path = (REPO_ROOT / rel).resolve()
    try:
        path.relative_to(REPO_ROOT)
    except ValueError:
        return None
    return path


def _read_context_file(path: Path) -> str:
    if not path.exists():
        return "[missing]"
    if path.is_dir():
        entries = sorted(
            str(p.relative_to(REPO_ROOT))
            for p in path.rglob("*")
            if p.is_file()
        )
        return "\n".join(entries[:120])
    text = path.read_text(encoding="utf-8", errors="replace")
    if len(text) > MAX_CONTEXT_FILE_CHARS:
        head = text[:MAX_CONTEXT_FILE_CHARS]
        return head + f"\n\n[truncated after {MAX_CONTEXT_FILE_CHARS} chars]"
    return text


def build_context_block(target: BedcTarget) -> str:
    blocks: list[str] = []
    total = 0
    for rel in _extract_local_input_paths(target):
        path = _safe_context_path(rel)
        if path is None:
            body = "[skipped: path outside repository]"
        else:
            body = _read_context_file(path)
        remaining = MAX_CONTEXT_TOTAL_CHARS - total
        if remaining <= 0:
            blocks.append("\n[context truncated: total budget reached]")
            break
        if len(body) > remaining:
            body = body[:remaining] + f"\n\n[truncated at total context budget {MAX_CONTEXT_TOTAL_CHARS} chars]"
        total += len(body)
        blocks.append(f"### {rel}\n\n```text\n{body}\n```")
    if not blocks:
        return "No local input excerpts were parsed from the target card."
    return "\n\n".join(blocks)


def build_initial_prompt(target: BedcTarget) -> str:
    payload = {
        "target_id": target.target_id,
        "title": target.title,
        "fields": target.fields,
        "body": target.body,
    }
    return f"""You are ChatGPT acting as a BEDC deep-reasoning oracle.

Your role is to analyze one BEDC proof-obligation target before any Lean work.

Hard boundary:
- Do not write Lean code.
- Do not propose editing `lean4/`.
- Do not propose editing `papers/bedc/`.
- Do not assume Mathlib.
- Do not introduce axioms.
- Do not treat naming or physical intuition as proof.
- Classify every substantive claim as one of:
  Derived, NeedsDefinition, NeedsSetupField, NarrativeOnly, TooStrong, False.

Project principle:
BEDC claims must be traceable to existing inductive objects, definitions,
structure or class fields, or already accepted propositions. If a claim needs a
policy assumption, say so directly.

Lane boundary:
This is not the automath outreach lane. The target is internal BEDC deepening:
strengthen the current BEDC paper state, clarify chapter placement, and produce
claim-packet material for later review. Do not aim at an external forum post,
GitHub issue, standalone short paper, journal targeting, or first-mover
publication. References should point inward to BEDC chapters and only outward
when a specific external fact is genuinely needed.

Target payload:
```json
{json.dumps(payload, ensure_ascii=False, indent=2)}
```

Local BEDC excerpts:
{build_context_block(target)}

Task:
Work on this target only. Identify the smallest precise claim that should be
tested next, the assumptions it needs, and the most likely obstruction. If the
claim is derivable, give a proof outline in ordinary mathematical prose. If it
is not derivable, classify the missing piece.

End with a line:
NEXT: <one precise follow-up question>
"""


def main() -> int:
    parser = argparse.ArgumentParser(description="BEDC deep-reasoning target dispatcher")
    parser.add_argument("target_id", nargs="?", help="Target id such as B-01")
    parser.add_argument("--list", action="store_true", help="List targets")
    parser.add_argument("--json", action="store_true", help="Print target as JSON")
    parser.add_argument("--prompt", action="store_true", help="Print the initial prompt")
    args = parser.parse_args()

    targets = parse_board()

    if args.list:
        for target in targets.values():
            obj = target.fields.get("Object", "")
            print(f"{target.target_id}\t{target.title}\t{obj}")
        return 0

    if not args.target_id:
        parser.error("target_id is required unless --list is used")

    target = targets.get(args.target_id)
    if target is None:
        known = ", ".join(targets)
        raise SystemExit(f"unknown target {args.target_id}; known targets: {known}")

    if args.json:
        print(json.dumps(asdict(target), ensure_ascii=False, indent=2))
        return 0

    if args.prompt:
        print(build_initial_prompt(target))
        return 0

    print(f"{target.target_id}: {target.title}")
    print(target.body)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
