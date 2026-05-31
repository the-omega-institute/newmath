"""Optional adapter for public MiniGrid-family environments."""

from __future__ import annotations

from dataclasses import dataclass, asdict
import importlib.util
import json
from pathlib import Path
from typing import Any


@dataclass(frozen=True)
class PublicMiniGridProbe:
    status: str
    environment_id: str
    observation_contract: str
    action_contract: str
    dependency_status: dict[str, str]
    benchmark_role: str
    cannot_claim: list[str]

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)

    def write_json(self, path: str | Path) -> None:
        target = Path(path)
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(json.dumps(self.to_dict(), indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _dependency_status() -> dict[str, str]:
    status = {}
    for name in ("gymnasium", "minigrid"):
        status[name] = "installed" if importlib.util.find_spec(name) is not None else "missing"
    return status


def build_public_minigrid_probe(environment_id: str = "MiniGrid-DoorKey-8x8-v0") -> PublicMiniGridProbe:
    deps = _dependency_status()
    available = all(value == "installed" for value in deps.values())
    return PublicMiniGridProbe(
        status="available" if available else "unavailable",
        environment_id=environment_id,
        observation_contract="Gymnasium reset/step observation with MiniGrid image channel",
        action_contract="Discrete MiniGrid action ids; adapter maps them to transition samples",
        dependency_status=deps,
        benchmark_role="public visual navigation benchmark adapter for BEDC-JEPA planning claims",
        cannot_claim=[] if available else ["public MiniGrid run was not executed in this environment"],
    )


def write_public_minigrid_probe(path: str | Path) -> PublicMiniGridProbe:
    probe = build_public_minigrid_probe()
    probe.write_json(path)
    return probe
