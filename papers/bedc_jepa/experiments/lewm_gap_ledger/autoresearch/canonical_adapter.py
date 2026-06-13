#!/usr/bin/env python3
"""Expose autoresearch findings as quality-lab claim-verdict pointer rows."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import re
import sys
from typing import Any, Mapping


AUTORESEARCH_ROOT = Path(__file__).resolve().parent
ARTICLE_ROOT = AUTORESEARCH_ROOT.parents[2]
PAPERS_ROOT = ARTICLE_ROOT.parent
QUALITY_LAB_ROOT = PAPERS_ROOT / "bedc-quality-lab"
QUALITY_LAB_PACKAGE_ROOT = QUALITY_LAB_ROOT

if str(QUALITY_LAB_PACKAGE_ROOT) not in sys.path:
    sys.path.insert(0, str(QUALITY_LAB_PACKAGE_ROOT))

from bedc_quality_lab.claim_terms import FORBIDDEN_POSITIVE_CLAIM_TERMS


FINDINGS_DIR = AUTORESEARCH_ROOT / "findings"
VERIFIED_FINDINGS_MD = FINDINGS_DIR / "verified_findings.md"
VERIFIED_FINDINGS_JSONL = FINDINGS_DIR / "verified_findings.jsonl"
CANONICAL_VERDICTS_JSONL = FINDINGS_DIR / "canonical_claim_verdicts.jsonl"
ADAPTER_SUMMARY_JSON = FINDINGS_DIR / "canonical_adapter_summary.json"

ARTICLE_REL_AUTORESEARCH_ROOT = "experiments/lewm_gap_ledger/autoresearch"
ARTICLE_REL_JSONL = f"{ARTICLE_REL_AUTORESEARCH_ROOT}/findings/verified_findings.jsonl"
ARTICLE_REL_MD = f"{ARTICLE_REL_AUTORESEARCH_ROOT}/findings/verified_findings.md"
ARTICLE_REL_SUMMARY = f"{ARTICLE_REL_AUTORESEARCH_ROOT}/findings/canonical_adapter_summary.json"

CLAIM_VERDICTS = {
    "positive": ("projected_positive_discovery", "projected-discovery-required"),
    "fail-closed": ("negative_discovery", "negative-discovery-failed-gate:autoresearch-fail-closed"),
}


def _read_jsonl(path: Path) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for line_index, line in enumerate(path.read_text(encoding="utf-8").splitlines()):
        if not line.strip():
            continue
        payload = json.loads(line)
        if not isinstance(payload, dict):
            raise ValueError(f"{path}:{line_index + 1}: expected object")
        payload["_jsonl_line_index"] = line_index
        rows.append(payload)
    return rows


def _markdown_claim_rows(path: Path) -> dict[str, dict[str, Any]]:
    claims: dict[str, dict[str, Any]] = {}
    row_index = 0
    for line in path.read_text(encoding="utf-8").splitlines():
        stripped = line.strip()
        if not stripped.startswith("| fi-"):
            continue
        cells = [cell.strip() for cell in stripped.strip("|").split("|")]
        if len(cells) < 7:
            continue
        hypothesis = cells[0]
        claim_text = cells[6]
        claims[hypothesis] = {
            "row_index": row_index,
            "forbidden_claim_term_hits": _term_hits(claim_text),
        }
        row_index += 1
    return claims


def _term_hits(text: object) -> list[str]:
    lowered = str(text).lower()
    return [term for term in FORBIDDEN_POSITIVE_CLAIM_TERMS if term.lower() in lowered]


def _slug(value: str) -> str:
    token = value.strip().lower()
    token = token.removeprefix("exp.").removeprefix("verdict.")
    token = token.replace(".", "-").replace("_", "-")
    token = re.sub(r"[^a-z0-9:-]+", "-", token).strip("-")
    if not token:
        raise ValueError(f"cannot derive slug from {value!r}")
    return token


def _claim_id(row: Mapping[str, Any]) -> str:
    experiment = _slug(str(row.get("experiment_ref") or row.get("finding_id") or "finding"))
    verdict = str(row.get("verdict_id") or "")
    suffix = ""
    if verdict:
        verdict_slug = _slug(verdict)
        if verdict_slug.startswith(experiment):
            suffix = verdict_slug.removeprefix(experiment).strip("-")
        else:
            suffix = verdict_slug
    return f"claim:autoresearch:{experiment}" + (f":{suffix}" if suffix else "")


def _terminal_node_id(claim_id: str) -> str:
    if not claim_id.startswith("claim:"):
        raise ValueError(f"claim_id must start with claim: {claim_id}")
    return "terminal:" + claim_id.removeprefix("claim:")


def _sha256_json(value: object) -> str:
    data = json.dumps(value, sort_keys=True, separators=(",", ":")).encode("utf-8")
    return hashlib.sha256(data).hexdigest()


def _summary_row(row: Mapping[str, Any], md_rows: Mapping[str, Mapping[str, Any]]) -> dict[str, Any]:
    experiment_ref = str(row.get("experiment_ref") or "")
    hypothesis = experiment_ref.removeprefix("exp.")
    jsonl_hits = _term_hits(row.get("reported_claim", ""))
    md_row = md_rows.get(hypothesis, {})
    md_hits = md_row.get("forbidden_claim_term_hits")
    combined_hits = sorted(set(jsonl_hits).union(md_hits if isinstance(md_hits, list) else []))
    md_row_index = md_row.get("row_index")
    if type(md_row_index) is not int:
        raise ValueError(f"missing markdown ledger row for {hypothesis}")
    authoritative = row.get("authoritative") is True
    gate_passed = row.get("gate_status") == "gate_passed"
    adversarial_ok = row.get("adversarial_verdict") in {"sound", "sound-but-scoped"}
    canonical_ready = authoritative and gate_passed and adversarial_ok and not combined_hits
    line_index = row["_jsonl_line_index"]
    return {
        "finding_id": row.get("finding_id"),
        "verdict_id": row.get("verdict_id"),
        "experiment_ref": experiment_ref,
        "status": row.get("status"),
        "authoritative": authoritative,
        "canonical_ready": canonical_ready,
        "forbidden_claim_term_hits": combined_hits,
        "source": f"{ARTICLE_REL_JSONL}:$.lines[{line_index}]",
        "ledger_pointer": f"{ARTICLE_REL_MD}:$.rows[{md_row_index}]",
    }


def _claim_verdict_row(summary: Mapping[str, Any], scorecard_hash: str, summary_index: int) -> dict[str, Any]:
    status = str(summary.get("status") or "")
    hits = summary.get("forbidden_claim_term_hits")
    if isinstance(hits, list) and hits:
        claim_verdict, reason = "negative_discovery", "forbidden-overclaim"
    else:
        if status not in CLAIM_VERDICTS:
            raise ValueError(f"unsupported finding status for canonical verdict: {status}")
        claim_verdict, reason = CLAIM_VERDICTS[status]

    claim_id = _claim_id(summary)
    return {
        "claim_graph_node_id": _terminal_node_id(claim_id),
        "claim_id": claim_id,
        "claim_verdict": claim_verdict,
        "formal_hardening_ready": bool(summary.get("canonical_ready")),
        "ledger_pointer": summary["ledger_pointer"],
        "reason": reason,
        "scorecard_hash": scorecard_hash,
        "scorecard_pointer": f"{ARTICLE_REL_SUMMARY}:$.findings[{summary_index}]",
        "scorecard_ready": bool(summary.get("canonical_ready")),
        "source": summary["source"],
    }


def build_outputs() -> tuple[list[dict[str, Any]], dict[str, Any]]:
    jsonl_rows = _read_jsonl(VERIFIED_FINDINGS_JSONL)
    md_rows = _markdown_claim_rows(VERIFIED_FINDINGS_MD)
    summaries = [_summary_row(row, md_rows) for row in jsonl_rows if row.get("authoritative") is True]
    scorecard_hash = _sha256_json(summaries)
    verdict_rows = [_claim_verdict_row(summary, scorecard_hash, index) for index, summary in enumerate(summaries)]
    forbidden_hit_count = sum(len(row["forbidden_claim_term_hits"]) for row in summaries)
    summary_payload = {
        "schema_id": "bedc-jepa-autoresearch:canonical-adapter-summary",
        "source_autoresearch_root": ARTICLE_REL_AUTORESEARCH_ROOT,
        "source_findings": [ARTICLE_REL_MD, ARTICLE_REL_JSONL],
        "quality_lab_forbidden_terms_source": "../bedc-quality-lab/bedc_quality_lab/claim_terms.py:FORBIDDEN_POSITIVE_CLAIM_TERMS",
        "quality_lab_claim_verdict_shape_source": "../bedc-quality-lab/reports/canonical/claim_verdicts.jsonl",
        "canonical_claim_verdicts": f"{ARTICLE_REL_AUTORESEARCH_ROOT}/findings/canonical_claim_verdicts.jsonl",
        "scorecard_hash": scorecard_hash,
        "forbidden_claim_term_hit_count": forbidden_hit_count,
        "findings": summaries,
    }
    return verdict_rows, summary_payload


def write_outputs() -> tuple[list[dict[str, Any]], dict[str, Any]]:
    rows, summary = build_outputs()
    CANONICAL_VERDICTS_JSONL.write_text(
        "".join(json.dumps(row, sort_keys=True) + "\n" for row in rows),
        encoding="utf-8",
    )
    ADAPTER_SUMMARY_JSON.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return rows, summary


def main() -> int:
    rows, summary = write_outputs()
    print(f"wrote {len(rows)} canonical claim-verdict pointer rows to {CANONICAL_VERDICTS_JSONL}")
    print(f"forbidden_claim_term_hit_count={summary['forbidden_claim_term_hit_count']}")
    print(f"scorecard_hash={summary['scorecard_hash']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
