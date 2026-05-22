#!/usr/bin/env python3
"""Shared hard gate for verification-axis text in BEDC paper-content lanes."""

from __future__ import annotations

import re


FORBIDDEN_VERIFICATION_AXIS_PATTERNS: tuple[tuple[str, re.Pattern[str]], ...] = (
    ("lean_target_phrase", re.compile(r"\bLean[- ]target\b", re.IGNORECASE)),
    ("lean4_path", re.compile(r"\blean4/", re.IGNORECASE)),
    ("lean_marker_macro", re.compile(r"\\(?:leanchecked|leanvariant|leansorryd|leanstmt|leandef|leantarget)\b", re.IGNORECASE)),
    ("closurestatus_macro", re.compile(r"\\begin\{closurestatus\}|\\(?:theoryclosure|formalstatus|bridgestatus|notclaimed|upgradepath)\b", re.IGNORECASE)),
    ("verification_axis_phrase", re.compile(r"\bverification[- ]axis\b", re.IGNORECASE)),
    ("marker_only_phrase", re.compile(r"\bmarker[- ]only\b", re.IGNORECASE)),
    ("formal_target_phrase", re.compile(r"\bformal[- ]target\b", re.IGNORECASE)),
    ("formal_readiness_phrase", re.compile(r"\bformal[- ]readiness\b", re.IGNORECASE)),
    ("single_carrier_alignment", re.compile(r"\bsingle[-_ ]carrier[-_ ]alignment\b", re.IGNORECASE)),
    ("taste_gate_identifier", re.compile(r"\btaste[-_ ]gate\b|\\ChapterTasteGate\b|\bChapterTasteGate\b", re.IGNORECASE)),
    ("bedc_derived_target", re.compile(r"BEDC\.Derived\.[A-Za-z0-9_.\\]+", re.IGNORECASE)),
)


NEGATED_AXIS_CONTEXT_RE = re.compile(
    r"\b(?:not|no|without|avoid(?:s|ing)?|exclud(?:e|es|ed|ing)|rather than|instead of|does not|must not|never)\b",
    re.IGNORECASE,
)


def verification_axis_hits(text: str, *, allow_negated_sentences: bool = False) -> list[str]:
    """Return forbidden verification-axis surface codes found in text.

    The BEDC deep-writing lane may discuss only paper-side theory content.
    Lean/verification terms are allowed in separate governance and audit
    chapters, but not as generated BOARD targets or Stage 2 writebacks.
    """

    hits: list[str] = []
    source = str(text or "")
    if allow_negated_sentences:
        segments = re.split(r"(?<=[.!?])\s+|\n+", source)
    else:
        segments = [source]
    for segment in segments:
        if allow_negated_sentences and NEGATED_AXIS_CONTEXT_RE.search(segment):
            continue
        for code, pattern in FORBIDDEN_VERIFICATION_AXIS_PATTERNS:
            if pattern.search(segment) and code not in hits:
                hits.append(code)
    return hits


def has_verification_axis_surface(text: str, *, allow_negated_sentences: bool = False) -> bool:
    return bool(verification_axis_hits(text, allow_negated_sentences=allow_negated_sentences))
