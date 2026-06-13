#!/usr/bin/env python3
"""Run cold/cache equivalence checks for cache-backed canonical reports."""

from __future__ import annotations

import argparse
from contextlib import contextmanager
from datetime import datetime, timezone
import importlib
import json
import os
from pathlib import Path
import shutil
import sys
import tempfile
from typing import Any, Iterator, Literal, Mapping, Sequence


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.canonical_cache_equivalence import (
    OWNER_ARTIFACT,
    CacheEquivalenceTarget,
    cache_root_policy,
    run_equivalence_audit,
    select_targets,
    targets_by_id,
    write_owner_payload,
)
from scripts import run_canonical_reports as canonical_reports


TARGET_DEFAULT_DEVICES = {
    "dgt-l0-controls": "auto",
    "dgt-l1-controls": "cpu",
}


def _json_dump(payload: Mapping[str, Any]) -> str:
    return json.dumps(payload, sort_keys=True)


def _target_device(target: CacheEquivalenceTarget, override: str | None) -> str:
    return override or TARGET_DEFAULT_DEVICES[target.target_id]


def _write_target_outputs(target: CacheEquivalenceTarget, *, generated_at: str, device: str | None) -> None:
    requested_device = _target_device(target, device)
    if target.target_id == "dgt-l0-controls":
        from bedc_quality_lab import dgt_l0_controls

        payload = dgt_l0_controls.build_payload(generated_at=generated_at, requested_device=requested_device)
        dgt_l0_controls.write_artifacts(payload, root=ROOT, generated_at=generated_at)
        return
    if target.target_id == "dgt-l1-controls":
        from bedc_quality_lab import dgt_l1_controls

        payload = dgt_l1_controls.build_payload(generated_at=generated_at, requested_device=requested_device, root=ROOT)
        dgt_l1_controls.write_artifacts(payload, root=ROOT, generated_at=generated_at)
        return
    raise ValueError(f"unsupported cache equivalence target: {target.target_id}")


def _sanitize_event(event: Mapping[str, Any], *, leg: str, cache_root: Path) -> dict[str, Any]:
    row = {"leg": leg, **dict(event)}
    manifest_path = row.get("manifest_path")
    if isinstance(manifest_path, str):
        try:
            relative = Path(manifest_path).resolve().relative_to(cache_root.resolve())
        except ValueError:
            row["manifest_path"] = "cache-root/<outside>"
        else:
            row["manifest_path"] = f"cache-root/{relative.as_posix()}"
    return row


@contextmanager
def _cache_environment(cache_root: Path, events: list[dict[str, Any]], *, leg: str, target: CacheEquivalenceTarget) -> Iterator[None]:
    previous_env = os.environ.get("BEDC_QUALITY_LAB_CACHE_DIR")
    module = importlib.import_module(target.owner_module)
    previous_observer = getattr(module, "CELL_CACHE_EVENT_OBSERVER", None)

    def observe(event: Mapping[str, Any]) -> None:
        events.append(_sanitize_event(event, leg=leg, cache_root=cache_root))

    os.environ["BEDC_QUALITY_LAB_CACHE_DIR"] = cache_root.as_posix()
    setattr(module, "CELL_CACHE_EVENT_OBSERVER", observe)
    try:
        yield
    finally:
        if previous_env is None:
            os.environ.pop("BEDC_QUALITY_LAB_CACHE_DIR", None)
        else:
            os.environ["BEDC_QUALITY_LAB_CACHE_DIR"] = previous_env
        setattr(module, "CELL_CACHE_EVENT_OBSERVER", previous_observer)


def _run_target(
    target: CacheEquivalenceTarget,
    leg: Literal["cold", "cache"],
    generated_at: str,
    cache_root: Path,
    events: list[dict[str, Any]],
    *,
    device: str | None,
) -> Mapping[str, Any]:
    with _cache_environment(cache_root, events, leg=leg, target=target):
        _write_target_outputs(target, generated_at=generated_at, device=device)
    spec = canonical_reports._specs_by_name()[target.target_id]
    canonical_reports._write_fingerprint_sidecar(spec, generated_at=generated_at)
    return canonical_reports._run_spec(spec, mode="verify", generated_at=generated_at)


@contextmanager
def _run_cache_root(explicit_root: Path | None) -> Iterator[tuple[Path, Literal["temporary", "explicit"]]]:
    if explicit_root is None:
        with tempfile.TemporaryDirectory(prefix="bedc-cache-equivalence-") as temp_dir:
            yield Path(temp_dir), "temporary"
        return
    policy = cache_root_policy(explicit_root)
    if policy["status"] != "pass":
        raise ValueError("cache equivalence cache root must not live under .refactor-loop")
    explicit_root.mkdir(parents=True, exist_ok=True)
    temp_dir = Path(tempfile.mkdtemp(prefix="cache-equivalence-", dir=explicit_root))
    try:
        yield temp_dir, "explicit"
    finally:
        shutil.rmtree(temp_dir, ignore_errors=True)


def build_payload(
    *,
    only: str | None,
    generated_at: str,
    cache_root: Path | None,
    device: str | None,
) -> dict[str, Any]:
    selected = select_targets(only)
    unsupported = () if only is None or selected else (only,)
    with _run_cache_root(cache_root) as (run_root, cache_root_source):
        return run_equivalence_audit(
            root=ROOT,
            generated_at=generated_at,
            targets=selected,
            unsupported_targets=unsupported,
            cache_root=run_root,
            cache_root_source=cache_root_source,
            run_target=lambda target, leg, stamp, root, events: _run_target(
                target,
                leg,
                stamp,
                root,
                events,
                device=device,
            ),
        )


def _existing_generated_at(target: CacheEquivalenceTarget) -> str | None:
    path = ROOT / target.json_artifact
    if not path.exists():
        return None
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError:
        return None
    generated_at = payload.get("generated_at") if isinstance(payload, dict) else None
    return generated_at if isinstance(generated_at, str) and generated_at else None


def _generated_at(args: argparse.Namespace, selected: Sequence[CacheEquivalenceTarget]) -> str:
    if args.generated_at:
        return args.generated_at
    stamps = {stamp for target in selected if (stamp := _existing_generated_at(target)) is not None}
    if len(stamps) == 1:
        return next(iter(stamps))
    return canonical_reports._reusable_generated_at() or datetime.now(timezone.utc).isoformat()


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="Write the owner artifact and fail when a cache hardgate fails.")
    parser.add_argument("--only", metavar="TARGET", help="Run one cache-backed canonical target.")
    parser.add_argument("--cache-root", type=Path, default=None, help="Parent directory for the temporary audit cache root.")
    parser.add_argument("--generated-at", default=None, help="Stable timestamp for generated artifacts.")
    parser.add_argument("--device", choices=("auto", "cpu", "mps"), default=None, help="Override requested producer device.")
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> None:
    args = parse_args(argv)
    selected = select_targets(args.only)
    generated_at = _generated_at(args, selected)
    if args.only is not None and args.only not in targets_by_id():
        payload = build_payload(
            only=args.only,
            generated_at=generated_at,
            cache_root=args.cache_root,
            device=args.device,
        )
    else:
        payload = build_payload(
            only=args.only,
            generated_at=generated_at,
            cache_root=args.cache_root,
            device=args.device,
        )
    write_owner_payload(ROOT / OWNER_ARTIFACT, payload)
    print(_json_dump({"status": payload["status"], "target_count": payload["summary"]["target_count"]}))
    if args.check and payload["status"] != "pass":
        raise SystemExit(1)


if __name__ == "__main__":
    main()
