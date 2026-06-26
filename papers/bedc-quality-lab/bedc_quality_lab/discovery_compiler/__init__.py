"""Discovery compiler core exports."""

from .architecture_mutation import (
    ArchitectureMutationDraft,
    GateResult,
    build_architecture_mutation_drafts,
    is_architecture_mutation_candidate,
    require_witness_basis,
)
from .backend import BackendEvidenceAdapter, TheoryBackend
from .capsule import ClaimCapsule
from .compiler import compile_discovery, load_adapter
from .map import DiscoveryMapRow
from .negative_reports import build_negative_discovery_reports

__all__ = [
    "BackendEvidenceAdapter",
    "ArchitectureMutationDraft",
    "ClaimCapsule",
    "DiscoveryMapRow",
    "GateResult",
    "TheoryBackend",
    "build_architecture_mutation_drafts",
    "build_negative_discovery_reports",
    "compile_discovery",
    "is_architecture_mutation_candidate",
    "load_adapter",
    "require_witness_basis",
]
