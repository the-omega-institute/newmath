#!/usr/bin/env python3
"""Deterministic BEDC structural-relation candidate miner.

This module is a peripheral candidate-supply source.  It never writes paper
content and never appends BOARD directly.  The research lane revalidates every
packet through its local-input filter and logic packet gate before any optional
board_spawn intake.
"""

from __future__ import annotations

import argparse
import json
import re
from dataclasses import dataclass
from pathlib import Path
from typing import Any

import board_archive
import paper_index

from dispatch_bedc_target import REPO_ROOT


MAX_FILE_LINES = 660
TITLE_MAX = 88
SKIP_BASENAMES = {
    "_index_files.tex",
    "00_concrete_instance_macros.tex",
    "00_large_model_macros.tex",
}

BLOCKED_PARTS_RE = re.compile(
    r"^papers/bedc/parts/(?:visions|conjectures)/",
    re.IGNORECASE,
)
BODY_PART_RE = re.compile(r"^papers/bedc/parts/")
PREFERRED_LANDING_RE = re.compile(
    r"^papers/bedc/parts/(?:concrete_instances|proof_sprint|proof_standing)/",
    re.IGNORECASE,
)

FORGETFUL_RE = re.compile(
    r"\b(forgetful|forgets?|drop(?:s|ping)?|projection|projects?|"
    r"extends?|speciali[sz]ation|underlying|substructure)\b",
    re.IGNORECASE,
)
FORGETFUL_LABEL_RE = re.compile(
    r"(forget|forgetful|projection|underlying|substructure)",
    re.IGNORECASE,
)
EQUIVALENCE_RE = re.compile(
    r"\b(equivalence|equivalent|isomorphic|isomorphism|iff|two[- ]sided|"
    r"classifier equivalence|endpoint equivalence)\b",
    re.IGNORECASE,
)
MISSING_REVERSE_RE = re.compile(
    r"\b(forward|reverse|converse|left|right|only one direction|asymmetr|"
    r"bidirectional|two[- ]sided)\b",
    re.IGNORECASE,
)
MIRROR_TOKEN_PAIRS = (
    ("left", "right"),
    ("source", "target"),
    ("domain", "codomain"),
    ("append", "prepend"),
    ("prefix", "suffix"),
    ("primal", "dual"),
    ("input", "output"),
)
BRIDGE_RE = re.compile(
    r"\b(bridge|route|handoff|readback|continuation|factor|factors|"
    r"transport|intermediate|stdbridge|standard bridge)\b",
    re.IGNORECASE,
)
CUT_LABEL_RE = re.compile(
    r"(cut|elimin|route.*closure|bridge.*boundary|no-host|non[-_]?escape)",
    re.IGNORECASE,
)
SUBSTRATE_RE = re.compile(
    r"\b(rule\s*110|cellular|substrate|bisimulation|bisimilar|"
    r"row embedding|binary|fkernel|bhist)\b",
    re.IGNORECASE,
)
CLASSIFIER_RE = re.compile(
    r"\b(classifier|fiberwise|displayed[- ]certificate|pullback|reindex|"
    r"reindexing|natural transformation|boundary transport)\b",
    re.IGNORECASE,
)
COMPLETION_RE = re.compile(
    r"\b(completion|complete|cauchy|compact|continuity|continuous|limit|"
    r"modulus|rate|tail|finite cover)\b",
    re.IGNORECASE,
)


@dataclass(frozen=True)
class RelationHit:
    file_rel: str
    title_seed: str
    family: str
    claim: str
    fit: int
    novelty: int
    equality_kind: str
    interpretation_kind: str
    cut_rank: str
    rate_surface: str = ""


def _read(rel: str) -> str:
    try:
        return (REPO_ROOT / rel).read_text(encoding="utf-8", errors="replace")
    except OSError:
        return ""


def _clean_words(text: str) -> str:
    text = re.sub(r"\\[A-Za-z]+(?:\{[^}]*\})?", " ", text)
    text = re.sub(r"[^A-Za-z0-9]+", " ", text)
    return re.sub(r"\s+", " ", text).strip()


def _object_from_file(rel: str, item: dict[str, Any]) -> str:
    labels = item.get("theorem_like_labels") or item.get("labels") or []
    for rec in labels:
        title = _clean_words(str(rec.get("title") or ""))
        if title:
            title = re.sub(
                r"\b(carrier|obligation|surface|exactness|determinacy|theorem|lemma)\b",
                " ",
                title,
                flags=re.IGNORECASE,
            )
            title = re.sub(r"\s+", " ", title).strip()
            if title:
                return title[:42]
    name = Path(rel).name
    name = re.sub(r"^\d+_", "", name)
    name = re.sub(r"_namecert_construction\.tex$", "", name)
    name = re.sub(r"\.tex$", "", name)
    return name.replace("_", " ")[:42] or "BEDC packet"


def _label_haystack(item: dict[str, Any]) -> str:
    labels = item.get("theorem_like_labels") or item.get("labels") or []
    return " ".join(
        " ".join([
            str(rec.get("title") or ""),
            str(rec.get("label") or ""),
            str(rec.get("env") or ""),
        ])
        for rec in labels
    )


def _body_file(item: dict[str, Any]) -> bool:
    rel = str(item.get("file") or "")
    if Path(rel).name in SKIP_BASENAMES:
        return False
    if not BODY_PART_RE.search(rel):
        return False
    if not PREFERRED_LANDING_RE.search(rel):
        return False
    if BLOCKED_PARTS_RE.search(rel):
        return False
    if bool(item.get("hub_like")):
        return False
    try:
        if int(item.get("line_count") or 0) >= MAX_FILE_LINES:
            return False
    except (TypeError, ValueError):
        return False
    return rel.endswith(".tex") and (REPO_ROOT / rel).exists()


def _has_label(item: dict[str, Any], pattern: re.Pattern[str]) -> bool:
    return bool(pattern.search(_label_haystack(item)))


def _rate_surface(text: str) -> str:
    if not COMPLETION_RE.search(text):
        return ""
    return (
        "Any completion, Cauchy, compactness, continuity, or limit reading must "
        "stay on the displayed rate/modulus/tail/window/finite-cover rows of "
        "the listed local input."
    )


def _forgetful_hit(rel: str, obj: str, item: dict[str, Any], text: str) -> RelationHit | None:
    if not FORGETFUL_RE.search(text):
        return None
    if _has_label(item, FORGETFUL_LABEL_RE):
        return None
    claim = (
        f"{obj} should expose a BEDC-native forgetful projection lemma: the "
        "richer displayed carrier can be read by dropping named rows and "
        "retaining only the target carrier, classifier, ledger, and NameCert "
        "coordinates already present in the chapter. The candidate is not a "
        "new object; it asks the gate to test whether the projection is a "
        "small existing-chapter lemma. Local evidence is the listed chapter's "
        "displayed rows; the receiving gate must re-read those rows rather "
        "than trust a copied source excerpt."
    )
    return RelationHit(
        rel,
        f"{obj} forgetful projection boundary",
        "forgetful_projection",
        claim,
        8,
        6,
        "none",
        "quotient_projection",
        "0",
        _rate_surface(text),
    )


def _equivalence_hit(rel: str, obj: str, item: dict[str, Any], text: str) -> RelationHit | None:
    if not EQUIVALENCE_RE.search(text):
        return None
    labels = _label_haystack(item)
    if re.search(r"(two[-_ ]sided|bidirectional|converse|reverse.*equivalence)", labels, re.I):
        return None
    if not MISSING_REVERSE_RE.search(text):
        return None
    claim = (
        f"{obj} should be checked for an equivalence-completion lemma: every "
        "displayed forward classifier/readback implication named in the local "
        "chapter must either have the reverse implication on the same visible "
        "rows or be recorded as a one-way interpretation boundary. This is a "
        "candidate for closing the two-sided surface without importing a host "
        "equivalence object. Local evidence is the listed chapter's displayed "
        "rows; the receiving gate must re-read those rows rather than trust a "
        "copied source excerpt."
    )
    return RelationHit(
        rel,
        f"{obj} equivalence completion boundary",
        "equivalence_completion",
        claim,
        7,
        7,
        "equivalent",
        "interpretation",
        "0",
        _rate_surface(text),
    )


def _mirror_hit(rel: str, obj: str, item: dict[str, Any], text: str) -> RelationHit | None:
    labels = _label_haystack(item).lower()
    text_lower = text.lower()
    for left, right in MIRROR_TOKEN_PAIRS:
        left_in = left in text_lower or left in labels
        right_in = right in text_lower or right in labels
        if left_in == right_in:
            continue
        present = left if left_in else right
        missing = right if left_in else left
        claim = (
            f"{obj} should be checked for a mirror/dual counterpart lemma: the "
            f"local chapter has a visible {present} side but no matching "
            f"{missing} side in its theorem labels. The candidate asks whether "
            "the opposite side is obtained by renaming the same displayed "
            "history, observation, result, termination, and certificate rows, "
            "or whether the asymmetry must be recorded as a boundary."
        )
        return RelationHit(
            rel,
            f"{obj} {present}-{missing} mirror boundary",
            "mirror_dual",
            claim,
            7,
            6,
            "substrate_mirror",
            "interpretation",
            "0",
            _rate_surface(text),
        )
    return None


def _bridge_cut_hit(rel: str, obj: str, item: dict[str, Any], text: str) -> RelationHit | None:
    if not BRIDGE_RE.search(text):
        return None
    if _has_label(item, CUT_LABEL_RE):
        return None
    claim = (
        f"{obj} should expose a bridge cut-elimination boundary: every named "
        "route, handoff, readback, continuation, or intermediate carrier in "
        "the local chapter must be either projected away from the final "
        "consumer surface or declared noneliminable. The candidate is a small "
        "existing-chapter obligation over the displayed route rows only. "
        "Local evidence is the listed chapter's displayed rows; the receiving "
        "gate must re-read those rows rather than trust a copied source excerpt."
    )
    return RelationHit(
        rel,
        f"{obj} bridge cut elimination boundary",
        "bridge_cut",
        claim,
        8,
        7,
        "none",
        "interpretation",
        "1",
        _rate_surface(text),
    )


def _substrate_hit(rel: str, obj: str, item: dict[str, Any], text: str) -> RelationHit | None:
    if not SUBSTRATE_RE.search(text):
        return None
    if _has_label(item, re.compile(r"(bisim|substrate.*mirror|row.*embedding)", re.I)):
        return None
    claim = (
        f"{obj} should declare its substrate relation kind: any Rule110, "
        "cellular, binary, FKernel, or BHist substrate reading must be stated "
        "as bisimulation, row embedding, or substrate mirror rather than "
        "definitional equality. The candidate asks the receiving gate for the "
        "smallest local relation certificate on the displayed rows. Local "
        "evidence is the listed chapter's displayed rows; the receiving gate "
        "must re-read those rows rather than trust a copied source excerpt."
    )
    return RelationHit(
        rel,
        f"{obj} substrate bisimulation boundary",
        "bisimulation",
        claim,
        7,
        7,
        "bisimilar",
        "substrate_mirror",
        "1",
        _rate_surface(text),
    )


def _classifier_hit(rel: str, obj: str, item: dict[str, Any], text: str) -> RelationHit | None:
    if not CLASSIFIER_RE.search(text):
        return None
    if _has_label(item, re.compile(r"(pullback|reindex|classifier.*align|fiberwise)", re.I)):
        return None
    claim = (
        f"{obj} should be checked for a classifier-alignment lemma: the local "
        "classifier, fiberwise certificate, pullback, or reindexing surface "
        "must say exactly which displayed rows are transported and which rows "
        "are forgotten. The candidate is an existing-chapter ledger/obligation "
        "rather than a new chapter. Local evidence is the listed chapter's "
        "displayed rows; the receiving gate must re-read those rows rather "
        "than trust a copied source excerpt."
    )
    return RelationHit(
        rel,
        f"{obj} classifier alignment boundary",
        "classifier_alignment",
        claim,
        7,
        6,
        "equivalent",
        "faithful_embedding",
        "0",
        _rate_surface(text),
    )


def _candidate_from_hit(hit: RelationHit) -> dict[str, Any]:
    title = re.sub(r"\s+", " ", hit.title_seed).strip()[:TITLE_MAX]
    budget = "B2_rate_or_modulus" if hit.rate_surface else "B0_finite_witness"
    if hit.family in {"bridge_cut", "bisimulation"}:
        elimination = (
            "List the displayed intermediate route rows, project the final "
            "consumer-visible rows, and reject any unlisted host or source "
            "coordinate; noneliminable rows must remain named in the boundary."
        )
    else:
        elimination = (
            "No new bridge carrier is introduced; the relation is tested by "
            "projection, renaming, or interpretation of rows already visible "
            "in the listed chapter."
        )
    downstream = (
        "Downstream consumer: BEDC chapter-worthiness and logic-packet gates; "
        "only accepted packets may become BOARD targets."
    )
    return {
        "title": title,
        "claim": hit.claim,
        "concrete_claim": hit.claim,
        "relation_family": hit.family,
        "source_object": hit.file_rel,
        "target_object": "existing BEDC displayed surface",
        "direction": "obstruction" if hit.family.endswith("boundary") else "A_to_B",
        "local_inputs": [hit.file_rel],
        "fit_score": hit.fit,
        "novelty": hit.novelty,
        "landing_kind": "existing_chapter_lemma",
        "tastegate_mode": "existing_chapter",
        "axiom_budget": budget,
        "strength_level": budget,
        "budget_reason": (
            "The candidate is a finite structural relation over displayed "
            "local rows. It asks for projection, renaming, interpretation, or "
            "route elimination, not a new object or external theorem import."
        ),
        "existence_mode": "none",
        "witness_extractor": "",
        "cut_rank": hit.cut_rank,
        "elimination_plan": elimination,
        "equality_kind": hit.equality_kind,
        "interpretation_kind": hit.interpretation_kind,
        "resource_trace": (
            "Consumes only the listed chapter's displayed carrier, classifier, "
            "ledger, route, and NameCert rows; no copied oracle output or "
            "external repository coordinate is used."
        ),
        "dependency_trace": (
            "Depends only on theorem/definition labels and carrier rows already "
            f"present in {hit.file_rel}; unused ambient dependencies must be "
            "dropped by the receiving gate."
        ),
        "rate_modulus_surface": hit.rate_surface,
        "oracle_mode": "candidate_generation",
        "rationale": (
            f"Structural relation miner detected {hit.family} in "
            f"{hit.file_rel}. why_not_parameter_echo: the packet asks for a "
            "typed relation boundary with source/target/direction and an "
            "elimination plan, not another parameterized restatement. "
            "minimal_bedc_native_landing: existing chapter lemma or ledger row. "
            f"{downstream}"
        ),
        "source": "research_lane:structural_relation_miner",
    }


def generate_candidates(*, limit: int = 20) -> list[dict[str, Any]]:
    """Return deterministic structural-relation candidate packets."""
    if limit <= 0:
        return []
    try:
        index = paper_index.load_or_build()
    except Exception:
        return []

    candidates: list[dict[str, Any]] = []
    seen_titles: set[str] = set()
    existing_titles = board_archive.existing_target_titles(include_archive=True)
    scanners = (
        _bridge_cut_hit,
        _forgetful_hit,
        _classifier_hit,
        _equivalence_hit,
        _substrate_hit,
        _mirror_hit,
    )
    for item in index.get("files") or []:
        if len(candidates) >= limit:
            break
        if not _body_file(item):
            continue
        rel = str(item.get("file") or "")
        text = _read(rel)
        if not text:
            continue
        obj = _object_from_file(rel, item)
        for scanner in scanners:
            if len(candidates) >= limit:
                break
            hit = scanner(rel, obj, item, text)
            if not hit:
                continue
            candidate = _candidate_from_hit(hit)
            key = str(candidate.get("title") or "").strip().lower()
            if not key or key in seen_titles or key in existing_titles:
                continue
            seen_titles.add(key)
            candidates.append(candidate)
    return candidates


def main() -> int:
    parser = argparse.ArgumentParser(description="Mine BEDC structural relation candidates")
    parser.add_argument("--limit", type=int, default=20)
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()
    candidates = generate_candidates(limit=args.limit)
    if args.json:
        print(json.dumps({"candidates": candidates}, ensure_ascii=False, indent=2))
    else:
        print(f"structural_relation_miner candidates={len(candidates)}")
        for cand in candidates:
            print(f"- {cand.get('title')} [{cand.get('relation_family')}]")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
