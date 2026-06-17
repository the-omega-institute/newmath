"""Single source for forbidden positive claim terms used by gates and reports."""

from __future__ import annotations


FORBIDDEN_POSITIVE_CLAIM_TERMS: tuple[str, ...] = (
    "full-lejepa",
    "global-quality",
    "full-tensor-namecert",
    "llm-behavior",
    "trained empirical superiority over Transformer",
    "training evidence beats Transformer",
    "LLM superiority",
    "production superiority",
)

HIGH_IMPACT_CLAIM_TERMS: tuple[str, ...] = (
    "safety",
    "production",
    "real-model",
    "real model",
    "deployment",
)
