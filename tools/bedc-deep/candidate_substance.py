#!/usr/bin/env python3
"""Substance gate for BEDC candidate packets."""

from __future__ import annotations

import re
from typing import Any

import verification_axis


SUBSTANCE_ECHO_RE = re.compile(
    r"local obligation row projection|"
    r"finite (?:displayed )?(?:row )?projection|"
    r"project(?:s|ed|ion)? (?:the )?(?:accepted )?carrier|"
    r"carrier row (?:and|together with) (?:its )?(?:local )?(?:certificate|NameCert) row|"
    r"records only the displayed carrier row|"
    r"every local obligation read factors through|"
    r"no (?:host|global|unlisted) (?:source )?row|"
    r"re-read those rows rather than trust a copied source excerpt|"
    r"consumes only the listed chapter'?s displayed carrier|"
    r"depends only on theorem/definition labels and carrier rows already present|"
    r"finite structural relation over displayed local rows|"
    r"displayed rows? (?:and|or) (?:no|not) hidden|"
    r"same displayed (?:packet|rows?) under row renaming",
    re.IGNORECASE,
)
SUBSTANCE_POSITIVE_RE = re.compile(
    r"\b(inversion|counterexample|obstruction|determinacy|uniqueness|"
    r"coverage|exhaustion|conservation|normal form|normal-form|"
    r"strict inequality|separation|minimal witness|canonical witness|"
    r"nontrivial witness|failure mode|classification)\b",
    re.IGNORECASE,
)
STRICT_OBSTRUCTION_CANDIDATE_RE = re.compile(
    r"\bstrict(?: local)? obstruction\b",
    re.IGNORECASE,
)
STRICT_OBSTRUCTION_EVIDENCE_RE = re.compile(
    r"\b(countermodel|counterexample|failure|defeat|refutation|separation|"
    r"refusal|nonescape|non-escape|impossib|frontier|blocked|missing|"
    r"excluded)\b",
    re.IGNORECASE,
)
BOARD_SURFACE_TITLE_RE = re.compile(
    r"\b("
    r"forgetful projection|classifier alignment|domain-codomain mirror|"
    r"substrate bisimulation|equivalence completion|local obligation row projection"
    r") boundary\b",
    re.IGNORECASE,
)
BOARD_TEMPLATE_ECHO_RE = re.compile(
    r"finite structural relation over displayed local rows|"
    r"asks for projection, renaming, interpretation, or route elimination|"
    r"consumes only the listed chapter'?s displayed carrier|"
    r"depends only on theorem/definition labels and carrier rows already present|"
    r"no copied oracle output or external repository coordinate|"
    r"no new bridge carrier is introduced",
    re.IGNORECASE,
)
BOARD_BURDEN_RE = re.compile(
    r"\b("
    r"inversion|counterexample|obstruction|determinacy|uniqueness|coverage|"
    r"exhaustion|conservation|normal form|normal-form|strict inequality|"
    r"separation|minimal witness|canonical witness|nontrivial witness|"
    r"failure mode|classification"
    r")\b",
    re.IGNORECASE,
)
STRUCTURAL_MINER_SOURCES = {
    "research_lane:structural_relation_miner",
}
SUBSTANCE_REJECTION_RE = re.compile(
    r"substance_echo_not_board_ready|structural_miner_requires_positive_substance|"
    r"weak_surface_target|strict_obstruction_requires_negative_evidence|"
    r"verification_axis_surface",
    re.IGNORECASE,
)


def packet_text(candidate: dict[str, Any]) -> str:
    return " ".join(
        str(candidate.get(key) or "")
        for key in (
            "title",
            "claim",
            "concrete_claim",
            "rationale",
            "budget_reason",
            "resource_trace",
            "dependency_trace",
            "elimination_plan",
        )
    )


def strict_obstruction_evidence_text(candidate: dict[str, Any]) -> str:
    title = STRICT_OBSTRUCTION_CANDIDATE_RE.sub(
        " ",
        str(candidate.get("title") or ""),
    )
    return " ".join(
        [
            title,
            str(candidate.get("rationale") or ""),
            str(candidate.get("budget_reason") or ""),
            str(candidate.get("resource_trace") or ""),
            str(candidate.get("dependency_trace") or ""),
            str(candidate.get("elimination_plan") or ""),
        ]
    )


def _body_section(body: str, header: str) -> str:
    in_section = False
    out: list[str] = []
    for raw_line in str(body or "").splitlines():
        line = raw_line.strip()
        if line == header:
            in_section = True
            continue
        if not in_section:
            continue
        if not line:
            if out:
                break
            continue
        if line.endswith(":") and not line.startswith("\\"):
            break
        out.append(line)
    return " ".join(out).strip()


def board_target_candidate(target: Any) -> dict[str, Any]:
    fields = getattr(target, "fields", {}) or {}
    body = getattr(target, "body", "") or ""
    return {
        "title": getattr(target, "title", "") or "",
        "claim": _body_section(body, "Problem:"),
        "rationale": _body_section(body, "Rationale:"),
        "source": fields.get("Source", ""),
        "budget_reason": _body_section(body, "Logic packet discipline:"),
        "resource_trace": body,
        "dependency_trace": body,
        "elimination_plan": body,
    }


def board_target_rejection(target: Any) -> str:
    candidate = board_target_candidate(target)
    reason = substance_rejection(candidate)
    if reason:
        return reason

    title = str(candidate.get("title") or "")
    source = str(candidate.get("source") or "").lower()
    full_text = packet_text(candidate)
    burden_text = " ".join(
        str(candidate.get(key) or "")
        for key in ("title", "claim")
    )
    if (
        BOARD_SURFACE_TITLE_RE.search(title)
        and ("board_spawn" in source or BOARD_TEMPLATE_ECHO_RE.search(full_text))
        and BOARD_TEMPLATE_ECHO_RE.search(full_text)
        and not BOARD_BURDEN_RE.search(burden_text)
    ):
        return "weak_surface_target"
    return ""


def substance_rejection(candidate: dict[str, Any]) -> str:
    """Reject candidates that only restate local row visibility."""
    text = packet_text(candidate)
    source = str(candidate.get("source") or "").strip()
    if verification_axis.has_verification_axis_surface(text, allow_negated_sentences=True):
        return "verification_axis_surface"
    if (
        STRICT_OBSTRUCTION_CANDIDATE_RE.search(text)
        and not STRICT_OBSTRUCTION_EVIDENCE_RE.search(
            strict_obstruction_evidence_text(candidate)
        )
    ):
        return "strict_obstruction_requires_negative_evidence"
    if SUBSTANCE_ECHO_RE.search(text) and not SUBSTANCE_POSITIVE_RE.search(text):
        return "substance_echo_not_board_ready"
    if source in STRUCTURAL_MINER_SOURCES and not SUBSTANCE_POSITIVE_RE.search(text):
        return "structural_miner_requires_positive_substance"
    return ""


def is_substance_rejection(reason: str) -> bool:
    return bool(SUBSTANCE_REJECTION_RE.search(str(reason or "")))
