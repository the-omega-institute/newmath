#!/usr/bin/env python3
"""Compute dispatch source weights for BEDC lean/paper workers.

The balancer is intentionally a short-lived subprocess. It reads current
critical-path supply, recent git-log consumption, optional root config, then
writes `.dispatch_weights.json` for prompts to consume on the next dispatch.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
OUT_PATH = ROOT / ".dispatch_weights.json"
CONFIG_PATH = ROOT / ".balancer_config.json"

DEFAULTS = {
    "lean": {
        "weights": {
            "top": 0.50,
            "formal_axis_top": 0.25,
            "unformalized_top": 0.15,
            "carrier_isomorphism_capstone": 0.10,
        }
    },
    "paper": {
        "weights": {
            "top": 0.40,
            "top_root_unblocks": 0.30,
            "closure_mark": 0.20,
            "carrier_isomorphism_capstone": 0.10,
        }
    },
}


def _now_iso() -> str:
    return datetime.now(timezone.utc).isoformat()


def _load_config() -> dict[str, Any]:
    if not CONFIG_PATH.exists():
        return {}
    try:
        data = json.loads(CONFIG_PATH.read_text(encoding="utf-8"))
        return data if isinstance(data, dict) else {}
    except Exception:
        return {}


def _base_weights(side: str, config: dict[str, Any]) -> dict[str, float]:
    weights = dict(DEFAULTS[side]["weights"])
    side_cfg = config.get(side, {})
    if isinstance(side_cfg, dict) and isinstance(side_cfg.get("weights"), dict):
        for key, value in side_cfg["weights"].items():
            if key in weights:
                try:
                    weights[key] = max(0.0, float(value))
                except (TypeError, ValueError):
                    pass
    return _normalize(weights)


def _normalize(weights: dict[str, float]) -> dict[str, float]:
    total = sum(v for v in weights.values() if v > 0)
    if total <= 0:
        count = len(weights) or 1
        return {k: round(1.0 / count, 4) for k in weights}
    return {k: round(max(0.0, v) / total, 4) for k, v in weights.items()}


def _run_critical_path() -> tuple[dict[str, Any] | None, str | None]:
    env = os.environ.copy()
    env["BEDC_SKIP_DISPATCH_BALANCER"] = "1"
    try:
        result = subprocess.run(
            ["python3", str(ROOT / "lean4" / "scripts" / "critical_path.py")],
            cwd=str(ROOT),
            capture_output=True,
            text=True,
            check=False,
            timeout=90,
            env=env,
        )
    except subprocess.TimeoutExpired:
        return None, "critical_path.py timed out after 90s"
    except Exception as exc:
        return None, f"critical_path.py failed to start: {exc}"
    if result.returncode != 0:
        detail = (result.stderr or result.stdout or "").strip()
        return None, detail[:800] or f"critical_path.py exited {result.returncode}"
    try:
        payload = json.loads(result.stdout)
    except Exception as exc:
        return None, f"critical_path.py JSON parse failed: {exc}"
    return payload, None


def _count_list(payload: dict[str, Any], key: str) -> int:
    value = payload.get(key)
    return len(value) if isinstance(value, list) else 0


def _count_transition_items(payload: dict[str, Any]) -> int:
    transitions = payload.get("top_transitions")
    if not isinstance(transitions, dict):
        return 0
    return sum(len(v) for v in transitions.values() if isinstance(v, list))


def _carrier_supply(payload: dict[str, Any]) -> int:
    carrier = payload.get("carrier_isomorphism")
    if not isinstance(carrier, dict) or not carrier.get("available"):
        return 0
    buckets = carrier.get("phase2_top_buckets")
    return len(buckets) if isinstance(buckets, list) else 0


def _compute_supply(payload: dict[str, Any]) -> dict[str, dict[str, int]]:
    closure_mark = (
        _count_list(payload, "drift_chapters")
        + _count_list(payload, "bridge_sync_pending")
        + _count_transition_items(payload)
    )
    return {
        "lean": {
            "top": _count_list(payload, "top"),
            "formal_axis_top": _count_list(payload, "formal_axis_top"),
            "unformalized_top": _count_list(payload, "unformalized_top"),
            "carrier_isomorphism_capstone": _carrier_supply(payload),
        },
        "paper": {
            "top": _count_list(payload, "top"),
            "top_root_unblocks": _count_list(payload, "top_root_unblocks"),
            "closure_mark": closure_mark,
            "carrier_isomorphism_capstone": _carrier_supply(payload),
        },
    }


LEAN_PATTERNS = {
    "carrier_isomorphism_capstone": re.compile(r"carrier[-_ ]?isomorphism|capstone", re.I),
    "formal_axis_top": re.compile(r"formal[-_ ]?axis|TasteGate|bridge .*schema|axiomClean->bridgeCheck", re.I),
    "unformalized_top": re.compile(r"unformalized|paper theorem|missing theorem|prove .*label", re.I),
    "top": re.compile(r"\b(R\d+:|lean|formaliz|prove|bridge)\b", re.I),
}

PAPER_PATTERNS = {
    "carrier_isomorphism_capstone": re.compile(r"carrier[-_ ]?isomorphism|capstone", re.I),
    "top_root_unblocks": re.compile(r"root[-_ ]?unblock|root_unblocks", re.I),
    "closure_mark": re.compile(r"closure[_ -]?mark|drift|bridge sync|formalstatus|closurestatus", re.I),
    "top": re.compile(r"\b(P\d+:|paper|review|revise|chapter|theory)\b", re.I),
}


def _git_recent_subjects() -> list[str]:
    candidates = ["codex-auto-dev", "origin/codex-auto-dev", "HEAD"]
    for branch in candidates:
        try:
            result = subprocess.run(
                ["git", "log", branch, "--since=1h", "--no-merges", "--pretty=format:%h %s"],
                cwd=str(ROOT),
                capture_output=True,
                text=True,
                check=False,
                timeout=10,
            )
        except Exception:
            continue
        if result.returncode == 0:
            return [line.strip() for line in result.stdout.splitlines() if line.strip()]
    return []


def _classify_subject(subject: str, side: str) -> str | None:
    patterns = LEAN_PATTERNS if side == "lean" else PAPER_PATTERNS
    for source, pattern in patterns.items():
        if pattern.search(subject):
            return source
    return None


def _compute_consumption() -> tuple[dict[str, dict[str, int]], int]:
    subjects = _git_recent_subjects()
    consumption = {
        "lean": {key: 0 for key in DEFAULTS["lean"]["weights"]},
        "paper": {key: 0 for key in DEFAULTS["paper"]["weights"]},
    }
    for subject in subjects:
        lean_source = _classify_subject(subject, "lean")
        paper_source = _classify_subject(subject, "paper")
        if lean_source:
            consumption["lean"][lean_source] += 1
        if paper_source:
            consumption["paper"][paper_source] += 1
    return consumption, len(subjects)


def _adjust_weights(
    base: dict[str, float],
    supply: dict[str, int],
    consumption: dict[str, int],
    total_rounds: int,
) -> dict[str, float]:
    active = {key: weight for key, weight in base.items() if supply.get(key, 0) > 0 and weight > 0}
    if not active:
        return {key: 0.0 for key in base}

    adjusted = dict(active)
    if total_rounds > 0:
        for key, weight in active.items():
            expected = weight * total_rounds
            factor = 1.0
            if consumption.get(key, 0) > expected * 1.5:
                factor = 0.7
            elif consumption.get(key, 0) < expected * 0.5:
                factor = 1.2
            adjusted[key] = _cap_against_base(weight * factor, base[key])

    normalized_active = _normalize(adjusted)
    return {key: normalized_active.get(key, 0.0) for key in base}


def _cap_against_base(value: float, base_value: float) -> float:
    return min(base_value * 1.5, max(base_value * 0.5, value))


def _advice(side: str, weights: dict[str, float], supply: dict[str, int]) -> str:
    available = [(k, v) for k, v in weights.items() if supply.get(k, 0) > 0 and v > 0]
    if not available:
        return "No currently supplied source; use critical_path fallback gates."
    top = sorted(available, key=lambda item: item[1], reverse=True)[:2]
    if side == "lean":
        parts = [f"Pick {1 if w < 0.34 else 2} of 3 from {k}" for k, w in top]
        if weights.get("carrier_isomorphism_capstone", 0) >= 0.10 and supply.get("carrier_isomorphism_capstone", 0):
            parts.append("Consider 1 capstone draft if other sources are blocked")
    else:
        parts = [f"Pick {'2' if w >= 0.34 else '1'} of 5 from {k}" for k, w in top]
        if weights.get("carrier_isomorphism_capstone", 0) >= 0.10 and supply.get("carrier_isomorphism_capstone", 0):
            parts.append("Reserve at most 1 capstone NameCert seed when compatible with hard gates")
    return ". ".join(parts) + "."


def compute_payload() -> dict[str, Any]:
    critical_path, error = _run_critical_path()
    computed_at = _now_iso()
    if error is not None or critical_path is None:
        return {
            "computed_at": computed_at,
            "error": error or "critical_path.py returned no payload",
            "lean": {
                "weights": DEFAULTS["lean"]["weights"],
                "supply": {},
                "consumption_60min": {},
                "advice": "critical_path unavailable; use existing hard gates.",
            },
            "paper": {
                "weights": DEFAULTS["paper"]["weights"],
                "supply": {},
                "consumption_60min": {},
                "advice": "critical_path unavailable; use existing hard gates.",
            },
        }

    config = _load_config()
    supply = _compute_supply(critical_path)
    consumption, total_rounds = _compute_consumption()
    payload: dict[str, Any] = {"computed_at": computed_at}
    for side in ("lean", "paper"):
        base = _base_weights(side, config)
        weights = _adjust_weights(base, supply[side], consumption[side], total_rounds)
        payload[side] = {
            "weights": weights,
            "supply": supply[side],
            "consumption_60min": consumption[side],
            "advice": _advice(side, weights, supply[side]),
        }
    return payload


def _summary(payload: dict[str, Any]) -> str:
    lines = [f"computed_at: {payload.get('computed_at')}"]
    if payload.get("error"):
        lines.append(f"error: {payload['error']}")
    for side in ("lean", "paper"):
        side_payload = payload.get(side, {})
        lines.append(f"{side}:")
        lines.append(f"  weights: {json.dumps(side_payload.get('weights', {}), ensure_ascii=False, sort_keys=True)}")
        lines.append(f"  advice: {side_payload.get('advice', '')}")
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser(description="Compute BEDC dispatch source weights")
    parser.add_argument("--dry-run", action="store_true", help="print summary without writing .dispatch_weights.json")
    parser.add_argument("--json", action="store_true", help="print full JSON to stdout")
    args = parser.parse_args()

    payload = compute_payload()
    if args.json:
        print(json.dumps(payload, indent=2, ensure_ascii=False))
    else:
        print(_summary(payload))
    if not args.dry_run:
        OUT_PATH.write_text(json.dumps(payload, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
