"""High-impact claim review protocol gates."""

from __future__ import annotations

import json
from collections.abc import Mapping, Sequence
from pathlib import Path
from typing import Any

from bedc_quality_lab.claim_terms import HIGH_IMPACT_CLAIM_TERMS
from bedc_quality_lab.discovery_compiler.pointers import pointer_value, resolve_artifact_pointer


HIGH_IMPACT_REVIEW_POINTER = "$.high_impact_claim_review"
HIGH_IMPACT_REVIEW_POINTERS = (
    "$.high_impact_claim_review.scope_review_pointer",
    "$.high_impact_claim_review.risk_ledger_pointer",
    "$.high_impact_claim_review.external_validation_pointer",
)
HIGH_IMPACT_DOMAINS_POINTER = "$.high_impact_claim_review.impact_domains"
HIGH_IMPACT_DOMAINS = frozenset({"safety", "production", "real_model"})


def _text_for_term_scan(value: Any) -> str:
    if isinstance(value, (dict, list, tuple)):
        return json.dumps(value, sort_keys=True).lower()
    return str(value).lower()


def high_impact_domain_hits(value: Any) -> list[str]:
    if not isinstance(value, Sequence) or isinstance(value, (str, bytes)):
        return []
    return [str(item) for item in value if isinstance(item, str) and item in HIGH_IMPACT_DOMAINS]


def high_impact_term_hits(value: Any) -> list[str]:
    text = _text_for_term_scan(value)
    return [term for term in HIGH_IMPACT_CLAIM_TERMS if term in text]


def is_high_impact_claim(spec: Any, payload: Mapping[str, Any]) -> bool:
    if getattr(spec, "bundle_role", None) != "hg_p_core" or getattr(spec, "claim_promotion_eligible", True) is not True:
        return False
    domains = pointer_value(payload, HIGH_IMPACT_DOMAINS_POINTER)
    if high_impact_domain_hits(domains):
        return True
    claim = pointer_value(payload, getattr(spec, "positive_claim_pointer", None))
    return bool(high_impact_term_hits(claim))


def high_impact_review_failure_pointer(root: Path, spec: Any, payload: Mapping[str, Any]) -> str | None:
    if not is_high_impact_claim(spec, payload):
        return None
    review = pointer_value(payload, HIGH_IMPACT_REVIEW_POINTER)
    if not isinstance(review, Mapping):
        return HIGH_IMPACT_REVIEW_POINTER
    domains = pointer_value(payload, HIGH_IMPACT_DOMAINS_POINTER)
    if domains is not None:
        unknown_domains = (
            [
                str(item)
                for item in domains
                if not isinstance(item, str) or item not in HIGH_IMPACT_DOMAINS
            ]
            if isinstance(domains, Sequence) and not isinstance(domains, (str, bytes))
            else ["impact_domains"]
        )
        if unknown_domains:
            return HIGH_IMPACT_DOMAINS_POINTER
    for pointer in HIGH_IMPACT_REVIEW_POINTERS:
        cell = pointer_value(payload, pointer)
        if not isinstance(cell, str) or resolve_artifact_pointer(root, cell) is None:
            return pointer
    return None
