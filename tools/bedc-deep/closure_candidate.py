#!/usr/bin/env python3
"""Post-writeback closure candidate review.

This module is intentionally paper-only and proposal-only. Stage 2 writes a
concrete theorem site, then calls this reviewer after `make` succeeds. The
reviewer records whether the touched chapter may need a chapter-level
closurestatus pass, but it does not edit paper files or Lean files.
"""

from __future__ import annotations

import argparse
import json
import re
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parents[1]
PARTS_DIR = REPO_ROOT / "papers" / "bedc" / "parts"
STATE_DIR = SCRIPT_DIR / "state" / "closure_candidates"
HUMAN_INBOX = SCRIPT_DIR / ".human_inbox.md"

CLOSURE_GRADES = (
    r"\seedClosure",
    r"\obligationClosure",
    r"\scopedClosure",
    r"\publicClosure",
    r"\bridgedClosure",
    r"\matureClosure",
)

REQUIRED_FIELDS = (
    "theoryclosure",
    "scopeclosed",
    "formalstatus",
    "leantarget",
    "bridgestatus",
    "notclaimed",
    "upgradepath",
)

CERTIFICATE_HINT_RE = re.compile(
    r"NameCert|semantic certificate|certificate obligations|closurestatus|"
    r"scopeclosed|carrier|classifier|exactness|ledger|stability",
    re.IGNORECASE,
)

BODY_ENV_RE = re.compile(
    r"\\begin\{(theorem|lemma|proposition|definition|corollary)\}"
    r"(.*?)\\end\{\1\}",
    re.DOTALL,
)


@dataclass
class ClosureBlock:
    object_name: str
    raw: str
    fields: dict[str, str]


def now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def now_tag() -> str:
    return datetime.now().strftime("%Y%m%d_%H%M%S")


def repo_rel(path: Path) -> str:
    try:
        return str(path.resolve().relative_to(REPO_ROOT))
    except ValueError:
        return str(path)


def read_text(path: Path) -> str:
    return path.read_text(encoding="utf-8", errors="replace")


def write_json(path: Path, data: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def append_human_inbox(item: str) -> None:
    HUMAN_INBOX.parent.mkdir(parents=True, exist_ok=True)
    block = f"\n## {now_iso()}\n\n- {item}\n"
    with open(HUMAN_INBOX, "a", encoding="utf-8") as f:
        f.write(block)


def extract_closure_blocks(text: str) -> list[ClosureBlock]:
    blocks: list[ClosureBlock] = []
    pattern = re.compile(r"\\begin\{closurestatus\}\{([^}]*)\}(.*?)\\end\{closurestatus\}", re.DOTALL)
    for match in pattern.finditer(text):
        body = match.group(2)
        fields: dict[str, str] = {}
        for field in REQUIRED_FIELDS:
            field_match = re.search(rf"\\{field}\{{(.*?)\}}", body, re.DOTALL)
            if field_match:
                fields[field] = " ".join(field_match.group(1).split())
        blocks.append(ClosureBlock(object_name=match.group(1).strip(), raw=match.group(0), fields=fields))
    return blocks


def extract_env_labels(text: str) -> list[dict[str, str]]:
    labels: list[dict[str, str]] = []
    for env_match in BODY_ENV_RE.finditer(text):
        env = env_match.group(1)
        body = env_match.group(2)
        label_match = re.search(r"\\label\{([^}]+)\}", body)
        if label_match:
            labels.append({"env": env, "label": label_match.group(1)})
    return labels


def macro_candidates(text: str) -> list[str]:
    found = set(re.findall(r"\\([A-Za-z][A-Za-z0-9]*Up)\b", text))
    found.update(re.findall(r"\\NameCert_\{\\([A-Za-z][A-Za-z0-9]*Up)\}", text))
    return sorted(found)


def closure_grade(block: ClosureBlock) -> str:
    value = block.fields.get("theoryclosure", "")
    for grade in CLOSURE_GRADES:
        if grade in value:
            return grade
    return value or "unknown"


def target_kind(tex_path: Path, text: str) -> str:
    name = tex_path.name.lower()
    if "closure_marker" in name:
        return "closure_marker"
    if any(token in name for token in ("namecert", "certificate", "phase_exit")):
        return "certificate_body"
    if "\\begin{closurestatus}" in text:
        return "closure_status_body"
    if CERTIFICATE_HINT_RE.search(text):
        return "certificate_adjacent"
    return "ordinary_body"


def missing_fields(block: ClosureBlock) -> list[str]:
    return [field for field in REQUIRED_FIELDS if not block.fields.get(field)]


def build_recommendation(
    *,
    tex_path: Path,
    file_text: str,
    appended_content: str,
    blocks: list[ClosureBlock],
) -> dict[str, Any]:
    labels = extract_env_labels(appended_content)
    file_labels = extract_env_labels(file_text)
    macros = macro_candidates(appended_content + "\n" + file_text[:12000])
    kind = target_kind(tex_path, file_text)
    label_text = " ".join(item["label"] for item in labels)
    appended_certificate_like = bool(
        CERTIFICATE_HINT_RE.search(appended_content)
        or re.search(r"cert|closure|obligation|scope|carrier|classifier|exactness|ledger|stability", label_text, re.IGNORECASE)
    )
    appended_has_closure_macro = bool(
        re.search(
            r"\\begin\{closurestatus\}|\\theoryclosure|\\formalstatus|"
            r"\\leantarget|\\bridgestatus|\\notclaimed|\\upgradepath",
            appended_content,
        )
    )

    reasons: list[str] = []
    action = "no_op"
    candidate_grade = ""
    object_name = blocks[0].object_name if len(blocks) == 1 else ""

    if appended_has_closure_macro:
        action = "alert_stage2_leak"
        reasons.append("appended content contains closurestatus field macros; Stage 2 should keep theorem-site content separate")

    if len(blocks) > 1:
        action = "proposal"
        reasons.append(f"file has {len(blocks)} closurestatus blocks; chapter-level status may need consolidation")

    if blocks:
        for block in blocks:
            mf = missing_fields(block)
            grade = closure_grade(block)
            if mf:
                action = "proposal"
                reasons.append(f"{block.object_name} closurestatus is missing fields: {', '.join(mf)}")
            if grade == r"\obligationClosure" and labels:
                action = "proposal"
                candidate_grade = r"\scopedClosure"
                reasons.append(
                    f"{block.object_name} is still obligationClosure and the accepted writeback added theorem-site labels"
                )
            elif (
                grade == r"\scopedClosure"
                and kind in {"certificate_body", "closure_status_body", "closure_marker"}
                and labels
                and appended_certificate_like
            ):
                action = "proposal" if action != "alert_stage2_leak" else action
                reasons.append(
                    f"{block.object_name} is already scopedClosure; review whether scopeclosed/notclaimed/upgradepath should mention the new accepted site"
                )
    elif kind in {"certificate_body", "closure_marker", "certificate_adjacent"}:
        action = "proposal"
        candidate_grade = r"\obligationClosure"
        object_name = "\\" + macros[0] if macros else ""
        reasons.append("certificate-like body has no closurestatus block")

    if not reasons:
        reasons.append("touched file does not require a closurestatus follow-up")

    return {
        "action": action,
        "candidate_grade": candidate_grade,
        "object_name": object_name,
        "target_kind": kind,
        "appended_certificate_like": appended_certificate_like,
        "labels_added": labels,
        "file_label_count": len(file_labels),
        "macro_candidates": macros[:12],
        "closure_blocks": [
            {
                "object_name": block.object_name,
                "grade": closure_grade(block),
                "fields_present": sorted(block.fields),
                "missing_fields": missing_fields(block),
            }
            for block in blocks
        ],
        "reasons": reasons,
    }


def analyze(
    *,
    target_id: str,
    target_title: str,
    tex_file: str,
    appended_content: str = "",
    no_inbox: bool = False,
) -> dict[str, Any]:
    tex_path = (REPO_ROOT / tex_file).resolve()
    try:
        tex_path.relative_to(PARTS_DIR)
    except ValueError:
        result = {
            "ok": False,
            "action": "error",
            "error": "tex_file is outside papers/bedc/parts",
            "target_id": target_id,
            "target_title": target_title,
            "tex_file": tex_file,
            "checked_at": now_iso(),
        }
        return persist_result(result, no_inbox=True)

    if not tex_path.exists():
        result = {
            "ok": False,
            "action": "error",
            "error": "tex_file does not exist",
            "target_id": target_id,
            "target_title": target_title,
            "tex_file": tex_file,
            "checked_at": now_iso(),
        }
        return persist_result(result, no_inbox=True)

    file_text = read_text(tex_path)
    blocks = extract_closure_blocks(file_text)
    recommendation = build_recommendation(
        tex_path=tex_path,
        file_text=file_text,
        appended_content=appended_content,
        blocks=blocks,
    )
    result = {
        "ok": True,
        "target_id": target_id,
        "target_title": target_title,
        "tex_file": repo_rel(tex_path),
        "checked_at": now_iso(),
        **recommendation,
        "policy": (
            "proposal_only: this post-writeback lane records closurestatus follow-up candidates "
            "and never edits paper or Lean files"
        ),
    }
    return persist_result(result, no_inbox=no_inbox)


def persist_result(result: dict[str, Any], *, no_inbox: bool) -> dict[str, Any]:
    target_id = str(result.get("target_id") or "unknown").lower()
    ts = now_tag()
    out_path = STATE_DIR / f"{target_id}_{ts}.json"
    latest_json = STATE_DIR / f"{target_id}_latest.json"
    latest_md = STATE_DIR / "latest.md"
    result["artifact"] = repo_rel(out_path)
    write_json(out_path, result)
    write_json(latest_json, result)
    latest_md.write_text(render_markdown(result), encoding="utf-8")

    if not no_inbox and result.get("ok") and result.get("action") != "no_op":
        reasons = "; ".join((result.get("reasons") or [])[:3])
        append_human_inbox(
            f"**closure_candidate** — {result.get('target_id')} touched "
            f"{result.get('tex_file')}: action={result.get('action')}, "
            f"candidate_grade={result.get('candidate_grade') or 'n/a'}. {reasons}. "
            f"Review {repo_rel(out_path)} before any closurestatus edit."
        )
    return result


def render_markdown(result: dict[str, Any]) -> str:
    lines = [
        "# closure candidate latest",
        "",
        f"- checked_at: {result.get('checked_at', '')}",
        f"- target: {result.get('target_id', '')} {result.get('target_title', '')}".rstrip(),
        f"- tex_file: {result.get('tex_file', '')}",
        f"- action: {result.get('action', '')}",
        f"- candidate_grade: {result.get('candidate_grade') or '(none)'}",
        f"- object_name: {result.get('object_name') or '(unknown)'}",
        "",
        "## Reasons",
    ]
    for reason in result.get("reasons") or []:
        lines.append(f"- {reason}")
    blocks = result.get("closure_blocks") or []
    if blocks:
        lines.extend(["", "## Existing Closure Blocks"])
        for block in blocks:
            lines.append(
                f"- {block.get('object_name')}: grade={block.get('grade')} "
                f"missing={','.join(block.get('missing_fields') or []) or 'none'}"
            )
    return "\n".join(lines).rstrip() + "\n"


def main() -> int:
    parser = argparse.ArgumentParser(description="Review a successful Stage 2 writeback for closurestatus follow-up")
    parser.add_argument("--target-id", required=True)
    parser.add_argument("--title", default="")
    parser.add_argument("--tex-file", required=True)
    parser.add_argument("--content-file", default="", help="accepted LaTeX block that was appended")
    parser.add_argument("--no-inbox", action="store_true")
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()

    content = ""
    if args.content_file:
        content_path = Path(args.content_file)
        if not content_path.is_absolute():
            content_path = REPO_ROOT / content_path
        if content_path.exists():
            content = read_text(content_path)

    result = analyze(
        target_id=args.target_id,
        target_title=args.title,
        tex_file=args.tex_file,
        appended_content=content,
        no_inbox=args.no_inbox,
    )
    print(json.dumps(result, ensure_ascii=False, indent=2) if args.json else render_markdown(result))
    return 0 if result.get("ok") else 1


if __name__ == "__main__":
    raise SystemExit(main())
