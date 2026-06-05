"""Backend adapters for discovery compiler."""

from . import sigreg
from .attribution import GapHeadAttributionBackendEvidenceAdapter
from .model_discovery import ModelDiscoveryBackendEvidenceAdapter
from .sigreg import SIGRegBackendEvidenceAdapter

__all__ = [
    "GapHeadAttributionBackendEvidenceAdapter",
    "ModelDiscoveryBackendEvidenceAdapter",
    "SIGRegBackendEvidenceAdapter",
    "attribution",
    "current_lab",
    "lejepa",
    "model_discovery",
    "sigreg",
]
