#!/usr/bin/env python3
"""Deterministic BEDC burden-bearing candidate miner.

This source only proposes local paper targets that already have concrete
supporting labels in an appendable body file.  It avoids hub files,
conjecture/vision surfaces, terminal closurestatus files, and generic row
projection templates.
"""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path
from typing import Any

import board_archive
import paper_index
import verification_axis

from dispatch_bedc_target import REPO_ROOT


SOURCE = "research_lane:burden_candidate_miner"
MAX_FILE_LINES = 640
TITLE_MAX = 88
BLOCKED_PARTS_RE = re.compile(
    r"^papers/bedc/parts/(?:visions|conjectures)/",
    re.IGNORECASE,
)
BODY_PART_RE = re.compile(r"^papers/bedc/parts/")
PREFERRED_PART_RE = re.compile(
    r"^papers/bedc/parts/(?:concrete_instances|proof_sprint|proof_standing)/",
    re.IGNORECASE,
)
SKIP_BASENAMES = {
    "_index_files.tex",
    "00_concrete_instance_macros.tex",
    "00_large_model_macros.tex",
}

RATE_RE = re.compile(
    r"\b(cauchy|completion|complete|compact|continuity|continuous|limit|"
    r"convergence|converge|modulus|rate|tail|dyadic|regular|window|"
    r"tolerance|finite cover|finite-cover)\b",
    re.IGNORECASE,
)
EXHAUSTION_RE = re.compile(
    r"\b(exhaustion|coverage|cover|totality|saturation|complete|completion)\b",
    re.IGNORECASE,
)
DETERMINACY_RE = re.compile(
    r"\b(determinacy|deterministic|unique|uniqueness|normal|normalization|"
    r"confluence|canonical)\b",
    re.IGNORECASE,
)
EXACTNESS_ONLY_RE = re.compile(r"\b(exactness|exact)\b", re.IGNORECASE)
OBSTRUCTION_RE = re.compile(
    r"\b(countermodel|counterexample|failure|defeat|refutation|separation|"
    r"obstruction|refusal|nonescape|non-escape|impossib|boundary)\b",
    re.IGNORECASE,
)
STRICT_OBSTRUCTION_RE = re.compile(
    r"\b(countermodel|counterexample|failure|defeat|refutation|separation|"
    r"obstruction|refusal|nonescape|non-escape|impossib|frontier|blocked|"
    r"missing|excluded)\b",
    re.IGNORECASE,
)
WITNESS_RE = re.compile(
    r"\b(witness|selector|minimal|canonical|inhabit|admission)\b",
    re.IGNORECASE,
)
BRIDGE_RE = re.compile(
    r"\b(bridge|transport|route|handoff|readback|factor|continuation)\b",
    re.IGNORECASE,
)
SURFACE_ONLY_RE = re.compile(
    r"\b(carrier|classifier|namecert obligations?|obligation surface|"
    r"row scope|surface)\b",
    re.IGNORECASE,
)


def _verification_axis_item(rel: str, labels: list[dict[str, Any]], text: str) -> bool:
    label_surface = " ".join(_label_text(rec) for rec in labels)
    return verification_axis.has_verification_axis_surface(
        " ".join([rel, label_surface, text[:12000]])
    )


def _read(rel: str) -> str:
    try:
        return (REPO_ROOT / rel).read_text(encoding="utf-8", errors="replace")
    except OSError:
        return ""


def _body_file(item: dict[str, Any]) -> bool:
    rel = str(item.get("file") or "")
    if Path(rel).name in SKIP_BASENAMES:
        return False
    if not BODY_PART_RE.search(rel):
        return False
    if not PREFERRED_PART_RE.search(rel):
        return False
    if BLOCKED_PARTS_RE.search(rel):
        return False
    if item.get("hub_like"):
        return False
    if int(item.get("closurestatus_count") or 0) > 0:
        return False
    try:
        if int(item.get("line_count") or 0) >= MAX_FILE_LINES:
            return False
    except (TypeError, ValueError):
        return False
    return rel.endswith(".tex") and (REPO_ROOT / rel).exists()


def _clean_words(text: str) -> str:
    text = re.sub(r"\\[A-Za-z]+(?:\{[^}]*\})?", " ", text)
    text = re.sub(r"[^A-Za-z0-9]+", " ", text)
    return re.sub(r"\s+", " ", text).strip()


def _object_from_file(rel: str, labels: list[dict[str, Any]]) -> str:
    for rec in labels:
        title = _clean_words(str(rec.get("title") or ""))
        title = re.sub(
            r"\b(carrier|classifier|namecert|obligations?|surface|row|"
            r"scope|theorem|lemma|definition)\b",
            " ",
            title,
            flags=re.IGNORECASE,
        )
        title = re.sub(r"\s+", " ", title).strip()
        if title:
            return title[:46]
    name = Path(rel).name
    name = re.sub(r"^\d+[a-z]?_", "", name)
    name = re.sub(r"_namecert_construction\.tex$", "", name)
    name = re.sub(r"\.tex$", "", name)
    return name.replace("_", " ")[:46] or "BEDC packet"


def _label_text(rec: dict[str, Any]) -> str:
    return " ".join(
        str(rec.get(key) or "")
        for key in ("label", "title", "env")
    )


def _label_name(rec: dict[str, Any]) -> str:
    return str(rec.get("label") or "").strip()


def _select_labels(labels: list[dict[str, Any]], pattern: re.Pattern[str]) -> list[dict[str, Any]]:
    return [rec for rec in labels if pattern.search(_label_text(rec))]


def _non_surface_labels(labels: list[dict[str, Any]]) -> list[dict[str, Any]]:
    out: list[dict[str, Any]] = []
    for rec in labels:
        text = _label_text(rec)
        if SURFACE_ONLY_RE.search(text) and not (
            OBSTRUCTION_RE.search(text)
            or WITNESS_RE.search(text)
            or BRIDGE_RE.search(text)
            or DETERMINACY_RE.search(text)
            or EXHAUSTION_RE.search(text)
        ):
            continue
        out.append(rec)
    return out


def _support_label(labels: list[dict[str, Any]], primary: dict[str, Any]) -> dict[str, Any] | None:
    primary_label = _label_name(primary)
    preference = re.compile(
        r"\b(exactness|scope|closure|transport|stability|ledger|source|"
        r"obligation|admission|route|certificate|namecert)\b",
        re.IGNORECASE,
    )
    for rec in labels:
        if _label_name(rec) != primary_label and preference.search(_label_text(rec)):
            return rec
    for rec in labels:
        if _label_name(rec) != primary_label:
            return rec
    return None


def _budget(haystack: str) -> tuple[str, str]:
    if RATE_RE.search(haystack):
        return (
            "B2_rate_or_modulus",
            (
                "The target is bounded by the displayed finite rate, modulus, "
                "tail, window, tolerance, or cover rows already named in the "
                "local chapter; it does not import compactness or choice."
            ),
        )
    return (
        "B0_finite_witness",
        (
            "The target is a finite local implication over already displayed "
            "BEDC rows, labels, and witness records in the selected body file."
        ),
    )


def _base_packet(
    *,
    rel: str,
    obj: str,
    family: str,
    title: str,
    claim: str,
    primary: dict[str, Any],
    support: dict[str, Any] | None,
    haystack: str,
) -> dict[str, Any]:
    budget, budget_reason = _budget(haystack)
    primary_label = _label_name(primary)
    support_label = _label_name(support or {})
    bridge_like = family == "bridge_determinacy" or BRIDGE_RE.search(claim)
    witness_like = family == "minimal_witness" or WITNESS_RE.search(claim)
    return {
        "title": re.sub(r"\s+", " ", title).strip()[:TITLE_MAX],
        "claim": claim,
        "concrete_claim": claim,
        "source": SOURCE,
        "local_inputs": [rel],
        "fit_score": 9,
        "novelty": 8,
        "landing_kind": "existing_chapter_lemma",
        "tastegate_mode": "existing_chapter",
        "axiom_budget": budget,
        "strength_level": budget,
        "budget_reason": budget_reason,
        "existence_mode": "constructive_witness" if witness_like else "none",
        "witness_extractor": (
            "Use the named finite witness or selector row cited by "
            f"{primary_label}; the companion label {support_label or primary_label} "
            "keeps the witness inside the same displayed local packet."
            if witness_like
            else ""
        ),
        "cut_rank": "1" if bridge_like else "0",
        "elimination_plan": (
            "List the displayed route, transport, or readback rows cited by "
            f"{primary_label}; the proof must show that any consumer-facing "
            "use factors through those rows and rejects unlisted coordinates."
            if bridge_like
            else "No bridge carrier is introduced; the theorem stays in the selected body file and cites only its local labels."
        ),
        "equality_kind": "none",
        "interpretation_kind": "interpretation" if bridge_like else "none",
        "resource_trace": (
            f"Primary support is `{primary_label}` in `{rel}`"
            + (f" together with `{support_label}`." if support_label else ".")
            + " The task must derive one minimal theorem-like block from those named rows."
        ),
        "dependency_trace": (
            f"Depends on the selected body file `{rel}` and its cited BEDC labels; "
            "no external repository, marker-axis update, or closurestatus edit is used."
        ),
        "rate_modulus_surface": (
            "Any analytic reading is restricted to the displayed finite rate, modulus, tail, window, tolerance, or finite-cover rows in the selected file."
            if budget == "B2_rate_or_modulus"
            else ""
        ),
        "oracle_mode": "proof_search",
        "difficulty": "medium",
        "selection_rank": family,
        "rationale": (
            f"Burden miner selected {family} because `{primary_label}` already "
            f"carries nontrivial local support in `{rel}`. The BOARD target is "
            "one appendable existing-chapter theorem and is intentionally not a "
            "row-projection, marker-axis, or closurestatus task."
        ),
    }


def _candidate_for_item(item: dict[str, Any]) -> dict[str, Any] | None:
    rel = str(item.get("file") or "")
    labels = list(item.get("theorem_like_labels") or [])
    labels = [rec for rec in labels if _label_name(rec)]
    if len(labels) < 2:
        return None
    burden_labels = _non_surface_labels(labels)
    if len(burden_labels) < 2:
        return None
    text = _read(rel)
    if _verification_axis_item(rel, labels, text):
        return None
    haystack = " ".join([rel, text[:12000], *(_label_text(rec) for rec in labels)])
    obj = _object_from_file(rel, labels)

    candidates_by_family: list[tuple[str, list[dict[str, Any]]]] = [
        ("strict_obstruction", _select_labels(burden_labels, STRICT_OBSTRUCTION_RE)),
        ("determinacy", _select_labels(burden_labels, DETERMINACY_RE)),
        ("exhaustion_coverage", _select_labels(burden_labels, EXHAUSTION_RE)),
        ("minimal_witness", _select_labels(burden_labels, WITNESS_RE)),
        ("bridge_determinacy", _select_labels(burden_labels, BRIDGE_RE)),
    ]
    for family, hits in candidates_by_family:
        for primary in hits:
            if SURFACE_ONLY_RE.fullmatch(_clean_words(_label_text(primary)).lower().replace(" ", " ")):
                continue
            if family == "determinacy" and EXACTNESS_ONLY_RE.search(_label_text(primary)):
                continue
            support = _support_label(labels, primary)
            primary_label = _label_name(primary)
            support_label = _label_name(support or {})
            if family == "strict_obstruction":
                claim = (
                    f"Using \\autoref{{{primary_label}}}"
                    + (f" and \\autoref{{{support_label}}}" if support_label else "")
                    + f", prove a strict local obstruction lemma for {obj}: the displayed failure, refusal, separation, or countermodel row blocks only the named converse or reuse route in `{rel}`, and it cannot be reinterpreted as a global impossibility, host theorem, or hidden external validation."
                )
                title = f"{obj} strict obstruction corollary"
            elif family == "determinacy":
                claim = (
                    f"Using \\autoref{{{primary_label}}}"
                    + (f" with \\autoref{{{support_label}}}" if support_label else "")
                    + f", prove a determinacy corollary for {obj}: once the cited local rows are fixed, any accepted consumer use must pick the same finite route, normal form, or exactness decision named by the chapter, with no alternate hidden coordinate or duplicate classifier source."
                )
                title = f"{obj} determinacy corollary"
            elif family == "exhaustion_coverage":
                claim = (
                    f"Using \\autoref{{{primary_label}}}"
                    + (f" and \\autoref{{{support_label}}}" if support_label else "")
                    + f", prove a downstream coverage lemma for {obj}: every accepted local consumer is exhausted by the finite alternatives, ledgers, or coverage rows already enumerated in the selected file, and all excluded alternatives remain outside the BEDC packet."
                )
                title = f"{obj} downstream coverage lemma"
            elif family == "minimal_witness":
                claim = (
                    f"Using \\autoref{{{primary_label}}}"
                    + (f" and \\autoref{{{support_label}}}" if support_label else "")
                    + f", prove a minimal witness lemma for {obj}: the named witness or selector row is sufficient for the local admission/consumption claim, and any larger reading must factor back to that displayed finite witness rather than add an ambient choice object."
                )
                title = f"{obj} minimal witness lemma"
            else:
                claim = (
                    f"Using \\autoref{{{primary_label}}}"
                    + (f" with \\autoref{{{support_label}}}" if support_label else "")
                    + f", prove a bridge determinacy lemma for {obj}: every displayed route, transport, readback, or handoff used by a consumer factors through the cited local rows, while unlisted bridge coordinates remain unavailable."
                )
                title = f"{obj} bridge determinacy lemma"
            return _base_packet(
                rel=rel,
                obj=obj,
                family=family,
                title=title,
                claim=claim,
                primary=primary,
                support=support,
                haystack=haystack,
            )
    return None


def candidates_from_index(
    index: dict[str, Any],
    *,
    existing_titles: set[str] | None = None,
    limit: int = 20,
) -> list[dict[str, Any]]:
    existing = existing_titles if existing_titles is not None else set()
    out: list[dict[str, Any]] = []
    seen: set[str] = set()
    for item in index.get("files") or []:
        if limit > 0 and len(out) >= limit:
            break
        if not _body_file(item):
            continue
        candidate = _candidate_for_item(item)
        if not candidate:
            continue
        key = str(candidate.get("title") or "").strip().lower()
        if not key or key in seen or key in existing:
            continue
        seen.add(key)
        out.append(candidate)
    return out


def generate_candidates(*, limit: int = 20) -> list[dict[str, Any]]:
    if limit <= 0:
        return []
    try:
        index = paper_index.load_or_build()
    except Exception:
        return []
    existing_titles = board_archive.existing_target_titles(include_archive=True)
    return candidates_from_index(index, existing_titles=existing_titles, limit=limit)


def main() -> int:
    parser = argparse.ArgumentParser(description="Mine burden-bearing BEDC candidates")
    parser.add_argument("--limit", type=int, default=20)
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()
    candidates = generate_candidates(limit=args.limit)
    if args.json:
        print(json.dumps({"candidates": candidates}, ensure_ascii=False, indent=2))
    else:
        print(f"burden_candidate_miner candidates={len(candidates)}")
        for candidate in candidates:
            print(f"- {candidate.get('title')} [{candidate.get('selection_rank')}]")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
