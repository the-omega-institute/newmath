#!/usr/bin/env python3
"""Substance gate for BEDC candidate packets."""

from __future__ import annotations

import re
from typing import Any


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
STRUCTURAL_MINER_SOURCES = {
    "research_lane:structural_relation_miner",
}
SUBSTANCE_REJECTION_RE = re.compile(
    r"substance_echo_not_board_ready|structural_miner_requires_positive_substance",
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


def substance_rejection(candidate: dict[str, Any]) -> str:
    """Reject candidates that only restate local row visibility."""
    text = packet_text(candidate)
    source = str(candidate.get("source") or "").strip()
    if SUBSTANCE_ECHO_RE.search(text) and not SUBSTANCE_POSITIVE_RE.search(text):
        return "substance_echo_not_board_ready"
    if source in STRUCTURAL_MINER_SOURCES and not SUBSTANCE_POSITIVE_RE.search(text):
        return "structural_miner_requires_positive_substance"
    return ""


def is_substance_rejection(reason: str) -> bool:
    return bool(SUBSTANCE_REJECTION_RE.search(str(reason or "")))
