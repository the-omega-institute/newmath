"""Backend adapters for discovery compiler."""

from . import sigreg
from .sigreg import SIGRegBackendEvidenceAdapter

__all__ = ["current_lab", "lejepa", "sigreg", "SIGRegBackendEvidenceAdapter"]
