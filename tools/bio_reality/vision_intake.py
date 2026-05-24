#!/usr/bin/env python3
"""Vision intake for BioReality unattended loops."""

from __future__ import annotations

import argparse
import json
import re
import sys
import tempfile
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

try:
    from agent_bus import _event, stable_id
    from store import BioRealityPaths, BioRealityStore, read_jsonl
except ModuleNotFoundError:  # pragma: no cover
    sys.path.insert(0, str(Path(__file__).resolve().parent))
    from agent_bus import _event, stable_id
    from store import BioRealityPaths, BioRealityStore, read_jsonl


SCRIPT_DIR = Path(__file__).resolve().parent
VISION_DIR = SCRIPT_DIR / "vision"
LEDGER_PATH = VISION_DIR / "ledger" / "intake_evaluations.jsonl"
SLUG_RE = re.compile(r"^[a-z0-9][a-z0-9-]*$")


def now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def parse_scalar(value: str) -> Any:
    stripped = value.strip()
    if stripped in {"true", "false"}:
        return stripped == "true"
    if stripped.startswith('"') and stripped.endswith('"'):
        return stripped[1:-1]
    return stripped


def parse_front_matter(text: str) -> tuple[dict[str, Any], str]:
    if not text.startswith("---\n"):
        return {}, text
    end = text.find("\n---\n", 4)
    if end < 0:
        return {}, text
    raw = text[4:end].splitlines()
    body = text[end + 5 :]
    data: dict[str, Any] = {}
    current_key = ""
    for line in raw:
        if not line.strip():
            continue
        if line.startswith("  - ") and current_key:
            data.setdefault(current_key, []).append(parse_scalar(line[4:]))
            continue
        if ":" not in line or line.startswith(" "):
            continue
        key, value = line.split(":", 1)
        key = key.strip()
        value = value.strip()
        current_key = key
        if value:
            data[key] = parse_scalar(value)
        else:
            data[key] = []
    return data, body


def vision_files(vision_dir: Path) -> list[Path]:
    if not vision_dir.exists():
        return []
    return sorted(
        path
        for path in vision_dir.iterdir()
        if path.suffix == ".md" and path.name != "index.md" and not path.name.startswith("_")
    )


def _ids(records: list[dict[str, Any]], key: str) -> set[str]:
    return {str(record.get(key) or "") for record in records if record.get(key)}


def evaluate_vision(path: Path, store: BioRealityStore) -> dict[str, Any]:
    text = path.read_text(encoding="utf-8")
    front, body = parse_front_matter(text)
    slug = str(front.get("slug") or path.stem)
    contact_ids = _ids(store.load_contacts(), "contact_id")
    conjectures = store.load_conjectures()
    gate_results = read_jsonl(store.paths.gate_results)
    passed_gate_ids = {
        str(item.get("packet_id") or "")
        for item in gate_results
        if item.get("gate_status") == "gate_passed"
    }
    passed_conjecture_ids = {
        str(item.get("packet_id") or "")
        for item in gate_results
        if item.get("packet_kind") == "conjecture" and item.get("gate_status") == "gate_passed"
    }
    issues: list[str] = []
    if not SLUG_RE.match(slug):
        issues.append("slug must be short kebab-case ASCII")
    if not str(front.get("title") or "").strip():
        issues.append("title is required")
    if str(front.get("ripeness") or "") != "ready":
        issues.append("ripeness is not ready")
    if not body.strip():
        issues.append("vision body is empty")

    required_contacts = [str(item) for item in front.get("required_reality_contacts", []) if isinstance(item, str)]
    required_gates = [str(item) for item in front.get("required_gates", []) if isinstance(item, str)]
    forbidden_claims = [str(item) for item in front.get("forbidden_claims_to_check", []) if isinstance(item, str)]
    required_contact_set = set(required_contacts)
    already_materialized = any(
        str(conjecture.get("conjecture_id") or "") in passed_conjecture_ids
        and {
            str(item)
            for item in conjecture.get("reality_contact_refs", [])
            if isinstance(item, str)
        }
        == required_contact_set
        for conjecture in conjectures
    )
    for contact in required_contacts:
        if contact not in contact_ids:
            issues.append(f"missing reality contact: {contact}")
    for gate in required_gates:
        if gate not in passed_gate_ids:
            issues.append(f"gate not passed: {gate}")
    if not forbidden_claims:
        issues.append("forbidden_claims_to_check is empty")

    if already_materialized:
        decision = "already_materialized"
    else:
        decision = "ready" if not issues else "blocked"
    return {
        "row_id": stable_id("vision-row", {"slug": slug, "issues": issues, "decision": decision}),
        "checked_at": now_iso(),
        "slug": slug,
        "path": str(path),
        "title": str(front.get("title") or ""),
        "ripeness": str(front.get("ripeness") or ""),
        "decision": decision,
        "issues": issues,
        "target_paper_section": front.get("target_paper_section") if isinstance(front.get("target_paper_section"), list) else [],
        "required_reality_contacts": required_contacts,
        "required_gates": required_gates,
        "forbidden_claims_to_check": forbidden_claims,
    }


def append_rows(path: Path, rows: list[dict[str, Any]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("a", encoding="utf-8") as handle:
        for row in rows:
            handle.write(json.dumps(row, ensure_ascii=False, sort_keys=True) + "\n")


def events_from_rows(rows: list[dict[str, Any]]) -> list[dict[str, Any]]:
    events: list[dict[str, Any]] = []
    for row in rows:
        slug = str(row.get("slug") or "")
        decision = str(row.get("decision") or "")
        if decision == "ready":
            events.append(_event("vision_ready", "bio-V", "vision", slug, "vision is ready for research agent planning", row))
        elif decision == "already_materialized":
            row["skip_reason"] = "already_materialized"
        else:
            issues = row.get("issues") if isinstance(row.get("issues"), list) else []
            reason = "; ".join(str(issue) for issue in issues[:3]) or "vision blocked"
            events.append(_event("vision_blocked", "bio-V", "vision", slug, reason, row))
    return events


def merge_events(existing: list[dict[str, Any]], additions: list[dict[str, Any]]) -> list[dict[str, Any]]:
    by_id: dict[str, dict[str, Any]] = {}
    for event in existing + additions:
        event_id = str(event.get("event_id") or stable_id("event", event))
        by_id[event_id] = event
    return sorted(by_id.values(), key=lambda item: (str(item.get("source") or ""), str(item.get("subject_id") or ""), str(item.get("event_kind") or "")))


def run_vision_lane(store: BioRealityStore, *, write: bool = True) -> dict[str, Any]:
    rows = [evaluate_vision(path, store) for path in vision_files(store.paths.vision_dir)]
    events = events_from_rows(rows)
    if write:
        append_rows(store.paths.vision_ledger, rows)
        store.write_events(merge_events(store.load_events(), events))
    return {
        "lane": "bio-V",
        "visions": len(rows),
        "ready": sum(1 for row in rows if row.get("decision") == "ready"),
        "blocked": sum(1 for row in rows if row.get("decision") == "blocked"),
        "already_materialized": sum(1 for row in rows if row.get("decision") == "already_materialized"),
        "events": len(events),
    }


def self_test() -> int:
    with tempfile.TemporaryDirectory(prefix="bio-reality-vision-") as tmp:
        base = Path(tmp)
        vision_dir = base / "vision"
        vision_dir.mkdir(parents=True)
        (vision_dir / "dna-to-protein-boundary.md").write_text(
            "\n".join(
                [
                    "---",
                    "slug: dna-to-protein-boundary",
                    'title: "Separate code readback from protein realization"',
                    "target_paper_section:",
                    "  - papers/bio_reality/parts/codon_window_reality_boundary.tex",
                    "required_reality_contacts:",
                    "  - curated.standard.code.table",
                    "required_gates:",
                    "forbidden_claims_to_check:",
                    "  - local_tile_as_global_biological_law",
                    "ripeness: ready",
                    "---",
                    "",
                    "Use curated code reality only at the code-read layer.",
                ]
            ),
            encoding="utf-8",
        )
        paths = BioRealityPaths(
            root=SCRIPT_DIR,
            conjectures=base / "conjectures.jsonl",
            contacts=base / "contacts.jsonl",
            gate_results=base / "gate_results.jsonl",
            events=base / "events.jsonl",
            vision_dir=vision_dir,
            vision_ledger=vision_dir / "ledger" / "intake_evaluations.jsonl",
        )
        paths.contacts.write_text(
            json.dumps({"contact_id": "curated.standard.code.table"}, sort_keys=True) + "\n",
            encoding="utf-8",
        )
        store = BioRealityStore(paths)
        summary = run_vision_lane(store)
        events = store.load_events()
        if summary["visions"] != 1 or summary["ready"] != 1 or not events:
            print(json.dumps({"summary": summary, "events": events}, indent=2), file=sys.stderr)
            return 1
        paths.conjectures.write_text(
            json.dumps(
                {
                    "conjecture_id": "dna.to.protein.boundary.materialized",
                    "reality_contact_refs": ["curated.standard.code.table"],
                },
                sort_keys=True,
            )
            + "\n",
            encoding="utf-8",
        )
        paths.gate_results.write_text(
            json.dumps(
                {
                    "packet_kind": "conjecture",
                    "packet_id": "dna.to.protein.boundary.materialized",
                    "gate_status": "gate_passed",
                },
                sort_keys=True,
            )
            + "\n",
            encoding="utf-8",
        )
        materialized_summary = run_vision_lane(store)
        materialized_rows = store.load_vision_ledger()
        if materialized_summary["already_materialized"] < 1 or materialized_summary["events"] != 0:
            print(json.dumps({"summary": materialized_summary, "rows": materialized_rows[-2:]}, indent=2), file=sys.stderr)
            return 1
        last_row = materialized_rows[-1] if materialized_rows else {}
        if last_row.get("decision") != "already_materialized" or last_row.get("skip_reason") != "already_materialized":
            print(json.dumps(last_row, indent=2), file=sys.stderr)
            return 1
    print("[bio-reality-vision] self-test ok")
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Scan BioReality vision files into events")
    parser.add_argument("--vision-dir", default=str(BioRealityPaths.vision_dir))
    parser.add_argument("--vision-ledger", default=str(BioRealityPaths.vision_ledger))
    parser.add_argument("--events", default=str(BioRealityPaths.events))
    parser.add_argument("--no-write", action="store_true")
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args(argv)
    if args.self_test:
        return self_test()
    paths = BioRealityPaths(
        vision_dir=Path(args.vision_dir),
        vision_ledger=Path(args.vision_ledger),
        events=Path(args.events),
    )
    summary = run_vision_lane(BioRealityStore(paths), write=not args.no_write)
    print(json.dumps(summary, ensure_ascii=False, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
