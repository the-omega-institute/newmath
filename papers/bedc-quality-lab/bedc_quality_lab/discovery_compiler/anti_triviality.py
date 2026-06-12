"""Owner-local anti-triviality contract helpers."""

from __future__ import annotations

from typing import Any


ANTI_TRIVIALITY_POLICY = "positive_requires_all_four_controls"
ANTI_TRIVIALITY_FAMILIES = frozenset(
    {"scale_only", "metadata_only", "matched_random", "forbidden_column"}
)


def owner_local_anti_triviality_contract(
    *,
    recommended_level: str,
    scale_only_pointer: str,
    metadata_only_pointer: str,
    matched_random_pointer: str,
    forbidden_column_pointer: str,
    status: str = "pass",
    failed_gate: str | None = None,
) -> dict[str, Any]:
    return {
        "anti_triviality_policy": ANTI_TRIVIALITY_POLICY,
        "anti_triviality_recommended_level": recommended_level,
        "anti_triviality_failed_gate": failed_gate if status != "pass" else None,
        "anti_triviality_gate_evidence": {
            "scale_only": {"status": status, "pointer": scale_only_pointer},
            "metadata_only": {"status": status, "pointer": metadata_only_pointer},
            "matched_random": {"status": status, "pointer": matched_random_pointer},
            "forbidden_column": {"status": status, "pointer": forbidden_column_pointer},
        },
    }
