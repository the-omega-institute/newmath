#!/usr/bin/env python3
"""Assimilate raw oracle prose into deterministic local bridge artifacts.

The oracle lane is intentionally candidate-only.  This script reads the raw
inbox, extracts the newest prose response, and writes a local plan that the
daemon and Codex can act on without asking the oracle to format JSON.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parents[1]
INBOX_PATH = SCRIPT_DIR / "oracle_inbox" / "candidates.jsonl"
OUT_DIR = SCRIPT_DIR / "state" / "oracle_assimilation"
LATEST_JSON = OUT_DIR / "latest_edge_defect_axis_plan.json"
LATEST_MD = OUT_DIR / "latest_edge_defect_axis_plan.md"
LATEST_MEMO_JSON = OUT_DIR / "latest_edge_defect_oracle_memo.json"
LATEST_MEMO_MD = OUT_DIR / "latest_edge_defect_oracle_memo.md"

ROUTE_RE = re.compile(r"^(?P<rank>[1-9][0-9]*)\.\s+(?P<name>.+?)\s*$")
FIELD_RE = re.compile(
    r"^(?P<label>Finite data sources?|Required fields|Construction|Why it is not explained by forbidden axes|"
    r"Exclusion controls|Failure mode|Why this is high value)\.\s*(?P<body>.*)$"
)


def now_iso() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat().replace("+00:00", "Z")


def read_jsonl(path: Path) -> list[dict[str, Any]]:
    if not path.exists():
        return []
    rows: list[dict[str, Any]] = []
    for line in path.read_text(encoding="utf-8").splitlines():
        if not line.strip():
            continue
        rows.append(json.loads(line))
    return rows


def latest_oracle_row(rows: list[dict[str, Any]]) -> dict[str, Any] | None:
    for row in reversed(rows):
        if row.get("oracle_response"):
            return row
    return None


def oracle_rows(rows: list[dict[str, Any]]) -> list[dict[str, Any]]:
    return [row for row in rows if row.get("oracle_response")]


def normalize_label(label: str) -> str:
    return (
        label.lower()
        .replace(" ", "_")
        .replace("/", "_")
        .replace("-", "_")
        .replace("?", "")
    )


def section_text(lines: list[str], start_heading: str, stop_headings: tuple[str, ...]) -> str:
    start = None
    for index, line in enumerate(lines):
        if line.strip() == start_heading:
            start = index + 1
            break
    if start is None:
        return ""
    end = len(lines)
    for index in range(start, len(lines)):
        stripped = lines[index].strip()
        if stripped in stop_headings or ROUTE_RE.match(stripped):
            end = index
            break
    return "\n".join(lines[start:end]).strip()


def split_paragraph_items(text: str) -> list[str]:
    items: list[str] = []
    current: list[str] = []
    for line in text.splitlines():
        stripped = line.strip()
        if not stripped:
            if current:
                items.append(" ".join(current).strip())
                current = []
            continue
        current.append(stripped)
    if current:
        items.append(" ".join(current).strip())
    return [item for item in items if item]


def parse_route_block(rank: int, name: str, block: str) -> dict[str, Any]:
    route: dict[str, Any] = {
        "rank": rank,
        "name": name,
        "route_id": re.sub(r"[^a-z0-9]+", "_", name.lower()).strip("_"),
    }
    current_key = "summary"
    buckets: dict[str, list[str]] = {current_key: []}
    for line in block.splitlines():
        stripped = line.strip()
        if not stripped:
            continue
        match = FIELD_RE.match(stripped)
        if match:
            current_key = normalize_label(match.group("label"))
            buckets.setdefault(current_key, [])
            body = match.group("body").strip()
            if body:
                buckets[current_key].append(body)
            continue
        buckets.setdefault(current_key, []).append(stripped)
    for key, values in buckets.items():
        if key == "required_fields":
            route[key] = [field.strip() for field in " ".join(values).split(",") if field.strip()]
        else:
            route[key] = " ".join(values).strip()
    return route


def parse_routes(lines: list[str]) -> list[dict[str, Any]]:
    routes: list[dict[str, Any]] = []
    starts: list[tuple[int, int, str]] = []
    for index, line in enumerate(lines):
        match = ROUTE_RE.match(line.strip())
        if match:
            starts.append((index, int(match.group("rank")), match.group("name")))
    for offset, (index, rank, name) in enumerate(starts):
        if not (1 <= rank <= 20):
            continue
        end = starts[offset + 1][0] if offset + 1 < len(starts) else len(lines)
        while end > index and lines[end - 1].strip() in {
            "Recommended execution order",
            "Minimal data request to Codex/local pipeline",
            "Hard rejection rules",
        }:
            end -= 1
        block_lines: list[str] = []
        for line in lines[index + 1 : end]:
            stripped = line.strip()
            if stripped in {
                "Recommended execution order",
                "Minimal data request to Codex/local pipeline",
                "Hard rejection rules",
            }:
                break
            block_lines.append(line)
        routes.append(parse_route_block(rank, name, "\n".join(block_lines)))
    return routes


def parse_data_requests(text: str) -> list[dict[str, str]]:
    requests: list[dict[str, str]] = []
    for item in split_paragraph_items(text):
        if ":" not in item:
            continue
        name, body = item.split(":", 1)
        requests.append({"name": name.strip(), "description": body.strip()})
    return requests


def build_plan(row: dict[str, Any]) -> dict[str, Any]:
    text = str(row.get("oracle_response") or "")
    lines = text.splitlines()
    routes = parse_routes(lines)
    execution = split_paragraph_items(
        section_text(
            lines,
            "Recommended execution order",
            ("Minimal data request to Codex/local pipeline", "Hard rejection rules"),
        )
    )
    data_requests = parse_data_requests(
        section_text(lines, "Minimal data request to Codex/local pipeline", ("Hard rejection rules",))
    )
    rejection_rules = split_paragraph_items(section_text(lines, "Hard rejection rules", ()))
    contract = section_text(lines, "Common admissibility contract", ("Exact projection test for  $u_{\\rm SerSplit}$",))
    exact_test = section_text(lines, "Exact projection test for  $u_{\\rm SerSplit}$", ("Strongest candidate routes",))

    return {
        "schema": "window_codon_oracle_assimilation.v1",
        "generated_ts": now_iso(),
        "source": {
            "inbox": str(INBOX_PATH.relative_to(REPO_ROOT)),
            "task_id": row.get("task_id"),
            "topic_id": row.get("topic_id"),
            "conversation_id": row.get("conversation_id"),
            "oracle_ts": row.get("ts"),
            "prompt_sha256": row.get("prompt_sha256"),
            "response_sha256": hashlib.sha256(text.encode("utf-8")).hexdigest(),
            "oracle_response_chars": len(text),
        },
        "candidate_only_boundary": (
            "The oracle output is treated only as a generator of auditable 61-codon vectors. "
            "It cannot update claims or verdicts without deterministic local experiments."
        ),
        "common_admissibility_contract": contract,
        "exact_projection_test": exact_test,
        "candidate_routes": routes,
        "recommended_execution_order": execution,
        "minimal_data_requests": data_requests,
        "hard_rejection_rules": rejection_rules,
        "local_next_artifacts": [
            "tools/window_codon_bridge/experiments/run_edge_defect_projection_harness.py",
            "tools/window_codon_bridge/state/oracle_assimilation/latest_edge_defect_axis_plan.json",
            "tools/window_codon_bridge/state/oracle_assimilation/latest_edge_defect_axis_plan.md",
        ],
    }


def plan_has_structured_work(plan: dict[str, Any]) -> bool:
    return bool(
        plan.get("candidate_routes")
        or plan.get("minimal_data_requests")
        or plan.get("hard_rejection_rules")
    )


def extract_next_question(text: str) -> str:
    marker = "sharpest next question is:"
    lower = text.lower()
    index = lower.rfind(marker)
    if index < 0:
        return ""
    return text[index + len(marker):].strip()


def extract_first_paragraph(text: str) -> str:
    for item in split_paragraph_items(text):
        if item:
            return item
    return ""


def extract_confounders(text: str) -> list[str]:
    out: list[str] = []
    for item in split_paragraph_items(text):
        stripped = item.strip()
        if stripped.startswith(("First,", "Second,", "Third,", "Fourth,", "Fifth,")):
            out.append(stripped)
        elif "must survive" in stripped or "has to survive" in stripped:
            out.append(stripped)
    return out


def build_memo(row: dict[str, Any]) -> dict[str, Any]:
    text = str(row.get("oracle_response") or "")
    return {
        "schema": "window_codon_oracle_memo.v1",
        "generated_ts": now_iso(),
        "source": {
            "inbox": str(INBOX_PATH.relative_to(REPO_ROOT)),
            "task_id": row.get("task_id"),
            "topic_id": row.get("topic_id"),
            "conversation_id": row.get("conversation_id"),
            "oracle_ts": row.get("ts"),
            "prompt_sha256": row.get("prompt_sha256"),
            "response_sha256": hashlib.sha256(text.encode("utf-8")).hexdigest(),
            "oracle_response_chars": len(text),
        },
        "strongest_mechanism": extract_first_paragraph(text),
        "decisive_confounders": extract_confounders(text),
        "sharpest_next_question": extract_next_question(text),
        "raw_response": text,
    }


def render_markdown(plan: dict[str, Any]) -> str:
    source = plan["source"]
    lines = [
        "# Edge-Defect Axis Oracle Assimilation",
        "",
        f"- schema: `{plan['schema']}`",
        f"- generated_ts: `{plan['generated_ts']}`",
        f"- source_task_id: `{source.get('task_id')}`",
        f"- source_conversation_id: `{source.get('conversation_id')}`",
        f"- oracle_response_chars: `{source.get('oracle_response_chars')}`",
        "",
        "## Boundary",
        "",
        plan["candidate_only_boundary"],
        "",
        "## Execution Order",
        "",
    ]
    for index, item in enumerate(plan.get("recommended_execution_order", []), start=1):
        lines.append(f"{index}. {item}")
    lines.extend(["", "## Candidate Routes", ""])
    for route in plan.get("candidate_routes", []):
        lines.append(f"### {route['rank']}. {route['name']}")
        summary = route.get("summary")
        if summary:
            lines.extend(["", str(summary)])
        for key in (
            "finite_data_source",
            "finite_data_sources",
            "construction",
            "exclusion_controls",
            "failure_mode",
        ):
            if route.get(key):
                title = key.replace("_", " ").title()
                lines.extend(["", f"**{title}.** {route[key]}"])
        if route.get("required_fields"):
            lines.extend(["", "**Required Fields.** " + ", ".join(route["required_fields"])])
        lines.append("")
    lines.extend(["## Minimal Data Requests", ""])
    for request in plan.get("minimal_data_requests", []):
        lines.append(f"- `{request['name']}`: {request['description']}")
    lines.extend(["", "## Hard Rejection Rules", ""])
    for item in plan.get("hard_rejection_rules", []):
        lines.append(f"- {item}")
    lines.append("")
    return "\n".join(lines)


def render_memo_markdown(memo: dict[str, Any]) -> str:
    source = memo["source"]
    lines = [
        "# Edge-Defect Oracle Memo",
        "",
        f"- schema: `{memo['schema']}`",
        f"- generated_ts: `{memo['generated_ts']}`",
        f"- source_task_id: `{source.get('task_id')}`",
        f"- source_conversation_id: `{source.get('conversation_id')}`",
        f"- oracle_response_chars: `{source.get('oracle_response_chars')}`",
        "",
        "## Strongest Mechanism",
        "",
        str(memo.get("strongest_mechanism") or ""),
        "",
        "## Decisive Confounders",
        "",
    ]
    for item in memo.get("decisive_confounders", []):
        lines.append(f"- {item}")
    lines.extend(["", "## Sharpest Next Question", "", str(memo.get("sharpest_next_question") or ""), ""])
    return "\n".join(lines)


def write_plan(plan: dict[str, Any]) -> None:
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    LATEST_JSON.write_text(json.dumps(plan, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    LATEST_MD.write_text(render_markdown(plan), encoding="utf-8")


def write_memo(memo: dict[str, Any]) -> None:
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    LATEST_MEMO_JSON.write_text(json.dumps(memo, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    LATEST_MEMO_MD.write_text(render_memo_markdown(memo), encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--dry-run", action="store_true")
    args = parser.parse_args()

    rows = read_jsonl(INBOX_PATH)
    response_rows = oracle_rows(rows)
    row = response_rows[-1] if response_rows else None
    if row is None:
        print(json.dumps({"status": "no_oracle_response", "inbox": str(INBOX_PATH)}, ensure_ascii=True))
        return 0
    memo = build_memo(row)
    latest_plan = None
    for candidate in reversed(response_rows):
        candidate_plan = build_plan(candidate)
        if plan_has_structured_work(candidate_plan):
            latest_plan = candidate_plan
            break
    if not args.dry_run:
        write_memo(memo)
        if latest_plan is not None:
            write_plan(latest_plan)
    print(
        json.dumps(
            {
                "status": "assimilated",
                "task_id": row.get("task_id"),
                "memo": str(LATEST_MEMO_JSON.relative_to(REPO_ROOT)),
                "memo_response_chars": memo["source"].get("oracle_response_chars"),
                "sharpest_next_question_present": bool(memo.get("sharpest_next_question")),
                "plan_task_id": latest_plan["source"].get("task_id") if latest_plan else None,
                "routes": len(latest_plan.get("candidate_routes", [])) if latest_plan else 0,
                "data_requests": len(latest_plan.get("minimal_data_requests", [])) if latest_plan else 0,
                "hard_rejection_rules": len(latest_plan.get("hard_rejection_rules", [])) if latest_plan else 0,
                "json": str(LATEST_JSON.relative_to(REPO_ROOT)),
                "markdown": str(LATEST_MD.relative_to(REPO_ROOT)),
                "dry_run": bool(args.dry_run),
            },
            ensure_ascii=True,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
