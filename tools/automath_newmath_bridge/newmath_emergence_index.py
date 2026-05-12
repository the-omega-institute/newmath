#!/usr/bin/env python3
"""Build a compact emergence index for the NewMath/BEDC surface.

The bridge should not continuously force Automath material into NewMath.  This
index watches the NewMath side instead: active BOARD shape, completed archive,
paper coverage, proposals, and Automath bridge intake signals.  The output is a
durable direction map that helps the bridge decide what Automath evidence might
become relevant on a later low-frequency intake pass.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
from collections import Counter, defaultdict
from pathlib import Path
from typing import Any


SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parent.parent
BEDC_DIR = REPO_ROOT / "tools" / "bedc-deep"
BOARD_PATH = BEDC_DIR / "BOARD.md"
COMPLETED_BOARD_PATH = BEDC_DIR / "BOARD.completed.md"
PROPOSALS_DIR = REPO_ROOT / "papers" / "bedc" / "proposals"
PARTS_DIR = REPO_ROOT / "papers" / "bedc" / "parts"
BRIDGE_DIGEST = REPO_ROOT / "docs" / "bridge" / "automath-newmath-intake-digest.json"
DEFAULT_JSON = REPO_ROOT / "docs" / "bridge" / "newmath-emergence-index.json"
DEFAULT_MD = REPO_ROOT / "docs" / "bridge" / "newmath-emergence-index.md"

TARGET_HEADER = re.compile(r"^### (B-\d+)\s+-\s+(.+)$", re.MULTILINE)
LABEL_RE = re.compile(r"\\label\{([^}]+)\}")

DIMENSION_KEYWORDS: dict[str, tuple[str, ...]] = {
    "s1_carrier_readback": ("s1", "sone", "circle", "carrier-readback", "carrier readback", "cayley"),
    "field_selector_obstruction": ("ratup", "fieldup", "selector", "apartzero", "square descent", "zero-factor"),
    "real_constant_carrier": ("realconstant", "real constant", "constant rational", "real-up", "realup"),
    "name_certificate": ("namecert", "name-certificate", "name certificate", "certificate row"),
    "proof_obligation_gap": ("proof obligation", "proof-obligation", "gap-policy", "gap policy", "obligation"),
    "bridge_continuation": ("automath", "bridge continuation", "continuation target", "bridge evidence"),
    "obstruction": ("obstruction", "blocked", "incompatible", "cannot", "exclusion"),
    "coverage": ("coverage", "covers", "covered"),
    "determinacy": ("determinacy", "deterministic", "unique", "uniqueness"),
    "inversion": ("inversion", "inverse", "readback inversion"),
    "formalization": ("lean", "formalization", "leanchecked", "tastegate", "taste gate"),
}


def _read(path: Path) -> str:
    if not path.exists():
        return ""
    return path.read_text(encoding="utf-8", errors="replace")


def _git(args: list[str], *, timeout: int = 60) -> str:
    proc = subprocess.run(["git", *args], cwd=str(REPO_ROOT), text=True, capture_output=True, timeout=timeout, check=False)
    return proc.stdout.strip() if proc.returncode == 0 else ""


def _parse_targets(path: Path) -> list[dict[str, Any]]:
    text = _read(path)
    matches = list(TARGET_HEADER.finditer(text))
    targets: list[dict[str, Any]] = []
    for idx, match in enumerate(matches):
        start = match.end()
        end = matches[idx + 1].start() if idx + 1 < len(matches) else len(text)
        body = text[start:end].strip()
        targets.append(
            {
                "target_id": match.group(1),
                "title": match.group(2).strip(),
                "body": body,
                "path": str(path.relative_to(REPO_ROOT)),
            }
        )
    return targets


def _dimension_hits(text: str) -> list[str]:
    lower = text.lower()
    hits: list[str] = []
    for dimension, words in DIMENSION_KEYWORDS.items():
        if any(word in lower for word in words):
            hits.append(dimension)
    return hits or ["other"]


def _paper_surface() -> dict[str, Any]:
    label_prefix_counts: Counter[str] = Counter()
    theme_counts: dict[str, Counter[str]] = defaultdict(Counter)
    near_line_cap: list[dict[str, Any]] = []
    files = sorted(PARTS_DIR.rglob("*.tex")) if PARTS_DIR.exists() else []
    for path in files:
        text = _read(path)
        rel = str(path.relative_to(REPO_ROOT))
        labels = LABEL_RE.findall(text)
        for label in labels:
            prefix = label.split(":", 1)[0] if ":" in label else "(none)"
            label_prefix_counts[prefix] += 1
        parts = Path(rel).parts
        theme = parts[3] if len(parts) > 3 else "(root)"
        theme_counts[theme]["files"] += 1
        theme_counts[theme]["labels"] += len(labels)
        line_count = text.count("\n") + (1 if text else 0)
        if line_count >= 760:
            near_line_cap.append({"file": rel, "line_count": line_count})
    return {
        "files": len(files),
        "label_prefix_counts": dict(sorted(label_prefix_counts.items())),
        "theme_counts": {key: dict(value) for key, value in sorted(theme_counts.items())},
        "near_line_cap_files": near_line_cap[:20],
    }


def _proposal_surface() -> dict[str, Any]:
    buckets = {
        "pending": list(PROPOSALS_DIR.glob("*.md")) if PROPOSALS_DIR.exists() else [],
        "accepted": list((PROPOSALS_DIR / "accepted").glob("*.md")) if (PROPOSALS_DIR / "accepted").exists() else [],
        "rejected": list((PROPOSALS_DIR / "rejected").glob("*.md")) if (PROPOSALS_DIR / "rejected").exists() else [],
    }
    return {
        name: {
            "count": len(paths),
            "sample": [str(path.relative_to(REPO_ROOT)) for path in sorted(paths)[:12]],
        }
        for name, paths in buckets.items()
    }


def _bridge_digest() -> dict[str, Any]:
    if not BRIDGE_DIGEST.exists():
        return {}
    try:
        data = json.loads(BRIDGE_DIGEST.read_text(encoding="utf-8"))
    except json.JSONDecodeError:
        return {"status": "invalid_json"}
    return data if isinstance(data, dict) else {}


def _direction_rows(active: list[dict[str, Any]], completed: list[dict[str, Any]], digest: dict[str, Any]) -> list[dict[str, Any]]:
    counts: dict[str, Counter[str]] = defaultdict(Counter)
    samples: dict[str, list[str]] = defaultdict(list)
    for source, targets in (("active_board", active), ("completed_board", completed[-80:])):
        for target in targets:
            text = f"{target.get('title', '')}\n{target.get('body', '')}"
            for dimension in _dimension_hits(text):
                counts[dimension][source] += 1
                if len(samples[dimension]) < 5:
                    samples[dimension].append(f"{target.get('target_id')}: {target.get('title')}")
    for item in digest.get("candidate_surface") or []:
        if not isinstance(item, dict):
            continue
        mode = str(item.get("bridge_consumption_mode") or "")
        path = str(item.get("source_path") or "")
        reason = str(item.get("reason") or "")
        for dimension in _dimension_hits(" ".join([path, mode, reason, str(item.get("bridge_binder") or "")])):
            counts[dimension]["bridge_signal"] += 1
            if len(samples[dimension]) < 5:
                samples[dimension].append(f"bridge: {path} ({reason})")

    rows: list[dict[str, Any]] = []
    for dimension, counter in counts.items():
        active_count = counter.get("active_board", 0)
        completed_count = counter.get("completed_board", 0)
        bridge_count = counter.get("bridge_signal", 0)
        score = active_count * 5 + completed_count * 2 + bridge_count * 3
        if active_count and bridge_count:
            bridge_posture = "watch_for_automath_evidence"
        elif active_count:
            bridge_posture = "newmath_internal_growth"
        elif bridge_count:
            bridge_posture = "evidence_only_until_newmath_carrier_exists"
        else:
            bridge_posture = "archive_trend"
        rows.append(
            {
                "dimension": dimension,
                "score": score,
                "active_board": active_count,
                "completed_recent": completed_count,
                "bridge_signal": bridge_count,
                "bridge_posture": bridge_posture,
                "samples": samples.get(dimension, []),
            }
        )
    rows.sort(key=lambda row: (-int(row["score"]), str(row["dimension"])))
    return rows


def build_index() -> dict[str, Any]:
    active = _parse_targets(BOARD_PATH)
    completed = _parse_targets(COMPLETED_BOARD_PATH)
    digest = _bridge_digest()
    paper = _paper_surface()
    proposals = _proposal_surface()
    source_heads = {
        "head": _git(["rev-parse", "HEAD"]),
        "origin_auto_dev": _git(["rev-parse", "origin/auto-dev"]),
        "origin_codex_auto_dev": _git(["rev-parse", "origin/codex-auto-dev"]),
        "bedc_branch": _git(["rev-parse", "origin/bedc-claim-packet-pipeline"]),
    }
    direction_rows = _direction_rows(active, completed, digest)
    index = {
        "schema_version": "newmath-emergence-index-v1",
        "source_heads": source_heads,
        "active_board_count": len(active),
        "completed_board_count": len(completed),
        "paper_surface": paper,
        "proposal_surface": proposals,
        "bridge_intake": {
            "event_id": digest.get("event_id"),
            "eligible_candidates": digest.get("eligible_candidates"),
            "reason_counts": digest.get("reason_counts") or {},
            "minimal_next_action": digest.get("minimal_next_action"),
        },
        "directions": direction_rows,
    }
    stable_payload = json.dumps(index, ensure_ascii=True, sort_keys=True)
    index["event_id"] = hashlib.sha1(stable_payload.encode("utf-8")).hexdigest()[:16]
    return index


def render_markdown(index: dict[str, Any]) -> str:
    lines = [
        "# NewMath Emergence Index",
        "",
        "This durable index summarizes where NewMath/BEDC appears to be growing.",
        "It is a planning surface for low-frequency Automath bridge intake; it is not a BOARD queue.",
        "",
        "| Metric | Value |",
        "| --- | --- |",
        f"| Event id | `{index.get('event_id')}` |",
        f"| Active BOARD targets | `{index.get('active_board_count')}` |",
        f"| Completed BOARD targets | `{index.get('completed_board_count')}` |",
        f"| Bridge intake next action | `{(index.get('bridge_intake') or {}).get('minimal_next_action')}` |",
        "",
        "## Direction Scores",
        "",
        "| Direction | Score | Active | Recent completed | Bridge signal | Bridge posture |",
        "| --- | ---: | ---: | ---: | ---: | --- |",
    ]
    for row in index.get("directions") or []:
        lines.append(
            "| `{}` | {} | {} | {} | {} | `{}` |".format(
                row.get("dimension"),
                row.get("score"),
                row.get("active_board"),
                row.get("completed_recent"),
                row.get("bridge_signal"),
                row.get("bridge_posture"),
            )
        )
    if not index.get("directions"):
        lines.append("| _none_ | 0 | 0 | 0 | 0 |  |")
    lines.extend(["", "## Top Samples"])
    for row in (index.get("directions") or [])[:8]:
        lines.append("")
        lines.append(f"### {row.get('dimension')}")
        for sample in row.get("samples") or []:
            lines.append(f"- {sample}")
    lines.extend(
        [
            "",
            "## Bridge Policy",
            "",
            "- Run Automath-NewMath bridge intake at a low cadence, normally 12 hours.",
            "- Treat bridge signals as evidence until NewMath has a named BEDC-native carrier, classifier, obstruction, or proof-obligation landing.",
            "- Prefer continuation targets over broad research prompts.",
            "- Do not create paper or Lean writes from this index directly.",
        ]
    )
    return "\n".join(lines) + "\n"


def write_outputs(index: dict[str, Any], json_path: Path, md_path: Path) -> list[Path]:
    json_path.parent.mkdir(parents=True, exist_ok=True)
    md_path.parent.mkdir(parents=True, exist_ok=True)
    json_text = json.dumps(index, ensure_ascii=False, indent=2, sort_keys=True) + "\n"
    md_text = render_markdown(index)
    changed: list[Path] = []
    if not json_path.exists() or json_path.read_text(encoding="utf-8") != json_text:
        json_path.write_text(json_text, encoding="utf-8")
        changed.append(json_path)
    if not md_path.exists() or md_path.read_text(encoding="utf-8") != md_text:
        md_path.write_text(md_text, encoding="utf-8")
        changed.append(md_path)
    return changed


def commit_outputs(paths: list[Path], *, push: bool) -> dict[str, Any]:
    if not paths:
        return {"status": "nothing_to_commit"}
    rels = [str(path.relative_to(REPO_ROOT)) for path in paths]
    add = subprocess.run(["git", "add", *rels], cwd=str(REPO_ROOT), text=True, capture_output=True, check=False)
    if add.returncode != 0:
        return {"status": "add_failed", "stderr": add.stderr.strip()[:1000]}
    diff = subprocess.run(["git", "diff", "--cached", "--quiet"], cwd=str(REPO_ROOT), check=False)
    if diff.returncode == 0:
        return {"status": "nothing_to_commit"}
    commit = subprocess.run(
        ["git", "commit", "-m", "bridge(newmath): update emergence index"],
        cwd=str(REPO_ROOT),
        text=True,
        capture_output=True,
        check=False,
    )
    if commit.returncode != 0:
        return {"status": "commit_failed", "stderr": commit.stderr.strip()[:1000]}
    result: dict[str, Any] = {"status": "committed", "stdout": commit.stdout.strip()[:1000]}
    if push:
        branch = _git(["branch", "--show-current"])
        if branch.startswith("bridge/"):
            pushed = subprocess.run(["git", "push", "origin", branch], cwd=str(REPO_ROOT), text=True, capture_output=True, check=False)
            result["push"] = "ok" if pushed.returncode == 0 else pushed.stderr.strip()[:1000]
        else:
            result["push"] = f"skipped non-bridge branch {branch}"
    return result


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Build the NewMath emergence index")
    parser.add_argument("--json", default=str(DEFAULT_JSON))
    parser.add_argument("--markdown", default=str(DEFAULT_MD))
    parser.add_argument("--commit", action="store_true")
    parser.add_argument("--push", action="store_true")
    args = parser.parse_args(argv)

    index = build_index()
    changed = write_outputs(index, Path(args.json), Path(args.markdown))
    result = commit_outputs(changed, push=args.push) if args.commit else {"status": "not_committed", "changed": [str(p) for p in changed]}
    print(json.dumps({"event_id": index.get("event_id"), "changed": [str(p) for p in changed], "commit": result}, ensure_ascii=False, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
