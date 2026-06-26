#!/usr/bin/env python3
"""Write the canonical MechanismDNA artifact."""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import json
from pathlib import Path
import sys
from typing import Any, Mapping, Sequence


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.mechanism_dna import (  # noqa: E402
    DEFAULT_DETERMINISTIC_SEED,
    JSON_ARTIFACT,
    MARKDOWN_ARTIFACT,
    audit_mechanism_dna,
    build_mechanism_dna,
    mechanism_dna_artifacts,
    render_mechanism_dna_markdown,
    stable_json,
)


def load_source_payloads(root: Path = ROOT) -> dict[str, Mapping[str, Any]]:
    payloads: dict[str, Mapping[str, Any]] = {}
    for artifact in mechanism_dna_artifacts():
        path = root / artifact
        if not path.exists():
            payloads[artifact] = {}
            continue
        loaded = json.loads(path.read_text(encoding="utf-8"))
        payloads[artifact] = loaded if isinstance(loaded, Mapping) else {}
    return payloads


def write_mechanism_dna(
    *,
    root: Path = ROOT,
    generated_at: str | None = None,
    deterministic_seed: int = DEFAULT_DETERMINISTIC_SEED,
) -> dict[str, Any]:
    timestamp = generated_at if generated_at is not None else datetime.now(timezone.utc).isoformat()
    source_payloads = load_source_payloads(root)
    payload = build_mechanism_dna(
        source_payloads,
        generated_at=timestamp,
        deterministic_seed=deterministic_seed,
    )
    audit = audit_mechanism_dna(payload, source_payloads)
    if audit.get("status") != "pass":
        failed_gates = audit.get("failed_gates")
        if isinstance(failed_gates, list):
            gate_summary = ", ".join(str(gate) for gate in failed_gates)
        else:
            gate_summary = str(failed_gates or audit.get("status") or "unknown")
        raise SystemExit(f"mechanism-dna audit failed: {gate_summary}")
    json_path = root / JSON_ARTIFACT
    markdown_path = root / MARKDOWN_ARTIFACT
    json_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.write_text(stable_json(payload), encoding="utf-8")
    markdown_path.write_text(render_mechanism_dna_markdown(payload), encoding="utf-8")
    return payload


def main(argv: Sequence[str] | None = None) -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--generated-at", default=None)
    parser.add_argument("--deterministic-seed", type=int, default=DEFAULT_DETERMINISTIC_SEED)
    args = parser.parse_args(argv)
    write_mechanism_dna(generated_at=args.generated_at, deterministic_seed=args.deterministic_seed)


if __name__ == "__main__":
    main()
