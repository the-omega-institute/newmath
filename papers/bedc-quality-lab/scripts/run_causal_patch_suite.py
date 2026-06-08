#!/usr/bin/env python3
"""Run the causal patch suite canonical producer."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys
from typing import Any, Mapping, Sequence


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.causal_patch_suite import (  # noqa: E402
    JSON_ARTIFACT,
    MARKDOWN_ARTIFACT,
    audit_causal_patch_suite,
    build_causal_patch_suite,
    load_source_artifacts,
    render_markdown,
)


def build_payload(*, root: Path = ROOT, generated_at: str | None = None) -> dict[str, Any]:
    return build_causal_patch_suite(source_artifacts=load_source_artifacts(root), generated_at=generated_at)


def _write_json(path: Path, payload: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def write_artifacts(*, root: Path = ROOT, generated_at: str | None = None) -> dict[str, Path]:
    payload = build_payload(root=root, generated_at=generated_at)
    audit = audit_causal_patch_suite(payload)
    if audit["status"] != "pass":
        raise ValueError(f"causal patch suite audit failed: {audit['failures']}")
    paths = {
        "json": root / JSON_ARTIFACT,
        "markdown": root / MARKDOWN_ARTIFACT,
    }
    _write_json(paths["json"], payload)
    paths["markdown"].parent.mkdir(parents=True, exist_ok=True)
    paths["markdown"].write_text(render_markdown(payload), encoding="utf-8")
    return paths


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--generated-at")
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)
    paths = write_artifacts(root=args.root, generated_at=args.generated_at)
    print(json.dumps({key: path.relative_to(args.root).as_posix() for key, path in paths.items()}, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
