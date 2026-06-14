#!/usr/bin/env python3
"""NyxID-backed candidate lane for the Window6--codon-Q6 bridge.

Oracle output is only an inbox signal.  It does not update claims,
experiments, verdicts, or paper status.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile
import time
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parents[1]
CLAIMS = SCRIPT_DIR / "registries" / "claims.json"
ORACLE_MANIFEST = SCRIPT_DIR / "registries" / "oracle_manifest.json"
STATE_PATH = SCRIPT_DIR / "state" / "oracle_lane_state.json"
INBOX_PATH = SCRIPT_DIR / "oracle_inbox" / "candidates.jsonl"
SELECTION_PACKET = REPO_ROOT / "papers" / "window_codon_bridge" / "data" / "codon_q6_selection_vectors.json"

OPEN_STATUSES = {"open", "needs_rerun"}
NYXID_CANDIDATES = (
    "nyxid",
    "/Users/lexa/.local/bin/nyxid",
    "/opt/homebrew/bin/nyxid",
    "/usr/local/bin/nyxid",
)


def now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def load_json(path: Path, default: Any = None) -> Any:
    if not path.exists():
        return default
    return json.loads(path.read_text(encoding="utf-8"))


def write_json(path: Path, obj: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, tmp = tempfile.mkstemp(dir=str(path.parent), suffix=".tmp")
    with os.fdopen(fd, "w", encoding="utf-8") as fh:
        json.dump(obj, fh, ensure_ascii=False, indent=1)
        fh.write("\n")
    os.replace(tmp, path)


def append_jsonl(path: Path, record: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("a", encoding="utf-8") as fh:
        fh.write(json.dumps(record, ensure_ascii=False, sort_keys=True) + "\n")


def sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def terminal_claims(claims_doc: dict[str, Any]) -> bool:
    claims = claims_doc.get("claims") or []
    if not claims:
        return False
    return all(str(claim.get("status") or "open") not in OPEN_STATUSES for claim in claims)


def latest_history_reason(claim: dict[str, Any]) -> str:
    history = claim.get("history") or []
    if not history:
        return ""
    last = history[-1] or {}
    return str(last.get("reason") or last.get("note") or "")


def selection_packet_summary() -> dict[str, Any]:
    if not SELECTION_PACKET.exists():
        return {"available": False, "path": str(SELECTION_PACKET.relative_to(REPO_ROOT))}
    data = load_json(SELECTION_PACKET, {})
    vectors = list(data.get("vectors") or [])
    fields: dict[str, int] = {}
    for row in vectors:
        if not isinstance(row, dict):
            continue
        for key, value in row.items():
            if value is not None:
                fields[key] = fields.get(key, 0) + 1
    return {
        "available": True,
        "path": str(SELECTION_PACKET.relative_to(REPO_ROOT)),
        "schema": data.get("schema"),
        "rows": len(vectors),
        "non_null_fields": dict(sorted(fields.items())),
        "has_d_resid4_loading": fields.get("d_resid4_loading", 0) > 0,
    }


def claim_by_id(claims_doc: dict[str, Any], claim_id: str) -> dict[str, Any] | None:
    for claim in claims_doc.get("claims") or []:
        if str(claim.get("claim_id") or "") == claim_id:
            return claim
    return None


def build_prompt(topic: dict[str, Any], claims_doc: dict[str, Any]) -> str:
    trigger_claim_id = str(topic.get("trigger_claim_id") or "")
    trigger = claim_by_id(claims_doc, trigger_claim_id) or {}
    packet = selection_packet_summary()
    reason = latest_history_reason(trigger)
    packet_json = json.dumps(packet, ensure_ascii=False, sort_keys=True)
    return (
        "You are an oracle candidate generator for the Window6--Codon-Q6 bridge. "
        "You are not a truth source, and you must not assert scientific verdicts.\n\n"
        "Current local result: the standard-code local-edge-hiding defect is exact: "
        "e_in=69, e_max=72, defect_support={Ser:2, Stop:1}. "
        "The Stop/Ser decomposition is a graph-theoretic fact, but the current local "
        "verdict is not a biological-axis certificate.\n\n"
        f"Trigger claim: {trigger_claim_id}\n"
        f"Trigger status: {trigger.get('status')}\n"
        f"Latest local reason: {reason}\n"
        f"Selection packet summary: {packet_json}\n\n"
        "Task: propose concrete, finite, auditable routes to construct an independent "
        "codon-level fourth residual axis d_resid4 for the 61 sense codons.  The route "
        "must be explicitly not explained by tRNA supply, f3/ramp, d_perp, GC, wobble, "
        "codon-pair effects, mRNA stability, or ribosome dwell.  Include finite data "
        "sources, required fields, normalization, exclusion controls, and the exact "
        "projection test for u_SerSplit.\n\n"
        "Return only JSON with this shape: "
        "{\"candidate_axes\":[{\"name\":\"...\",\"data_sources\":[\"...\"],"
        "\"construction\":\"...\",\"controls\":[\"...\"],\"audit_test\":\"...\","
        "\"failure_mode\":\"...\"}],\"data_requests\":[\"...\"],\"tests\":[\"...\"]}. "
        "Do not include prose outside JSON."
    )


def due_for_topic(state: dict[str, Any], topic_hash: str, cooldown_seconds: int) -> tuple[bool, str]:
    last_hash = str(state.get("last_topic_hash") or "")
    last_ts = float(state.get("last_attempt_epoch") or 0.0)
    if last_hash != topic_hash:
        return True, "topic_changed"
    age = time.time() - last_ts
    if age >= cooldown_seconds:
        return True, "cooldown_elapsed"
    return False, f"cooldown_active:{int(cooldown_seconds - age)}s"


def response_tail(text: str, limit: int = 4000) -> str:
    text = text or ""
    return text[-limit:]


def first_json_payload(value: Any) -> Any:
    if isinstance(value, dict) and any(key in value for key in ("candidate_axes", "data_requests", "tests")):
        return value
    if isinstance(value, list):
        for item in value:
            nested = first_json_payload(item)
            if nested is not None:
                return nested
        return value
    if isinstance(value, dict):
        for key in ("body", "response", "output", "text", "content"):
            if key in value:
                nested = first_json_payload(value[key])
                if nested is not None:
                    return nested
        for nested_value in value.values():
            nested = first_json_payload(nested_value)
            if nested is not None and nested is not value:
                return nested
        return value
    if not isinstance(value, str):
        return None
    stripped = value.strip()
    if not stripped:
        return None
    try:
        return json.loads(stripped)
    except json.JSONDecodeError:
        pass
    decoder = json.JSONDecoder()
    for index, char in enumerate(stripped):
        if char not in "[{":
            continue
        try:
            parsed, _end = decoder.raw_decode(stripped[index:])
            return parsed
        except json.JSONDecodeError:
            continue
    return None


def candidate_fields(payload: Any) -> dict[str, Any]:
    if not isinstance(payload, dict):
        return {}
    return {
        "candidate_axes": payload.get("candidate_axes") if isinstance(payload.get("candidate_axes"), list) else [],
        "data_requests": payload.get("data_requests") if isinstance(payload.get("data_requests"), list) else [],
        "tests": payload.get("tests") if isinstance(payload.get("tests"), list) else [],
    }


def nyxid_payload(prompt: str, model: str) -> dict[str, Any]:
    return {
        "model": model,
        "input": [
            {
                "role": "user",
                "content": [
                    {
                        "type": "input_text",
                        "text": prompt,
                    }
                ],
            }
        ],
        "text": {
            "format": {
                "type": "json_object",
            }
        },
    }


def nyxid_executable() -> str | None:
    for candidate in NYXID_CANDIDATES:
        if os.path.isabs(candidate):
            if os.access(candidate, os.X_OK):
                return candidate
            continue
        found = shutil.which(candidate)
        if found:
            return found
    return None


def run_nyxid(prompt: str, transport: dict[str, Any]) -> dict[str, Any]:
    service = str(transport.get("service") or "aevatar")
    path = str(transport.get("path") or "v1/responses")
    method = str(transport.get("method") or "POST")
    timeout_seconds = int(transport.get("timeout_seconds") or 180)
    model = str(transport.get("model") or "gpt-5")
    exe = nyxid_executable()
    if exe is None:
        return {
            "status": "transport_failed",
            "service": service,
            "path": path,
            "error": "nyxid executable not found",
            "response_text": "",
            "response_json": None,
        }
    payload = nyxid_payload(prompt, model)
    with tempfile.NamedTemporaryFile("w", encoding="utf-8", suffix=".json", delete=False) as fh:
        json.dump(payload, fh, ensure_ascii=False)
        payload_path = fh.name
    try:
        proc = subprocess.run(
            [
                exe,
                "proxy",
                "request",
                service,
                path,
                "--method",
                method,
                "--data",
                f"@{payload_path}",
                "--header",
                "Content-Type:application/json",
                "--output",
                "json",
            ],
            cwd=str(REPO_ROOT),
            capture_output=True,
            text=True,
            timeout=timeout_seconds,
        )
    except (OSError, subprocess.TimeoutExpired) as exc:
        return {
            "status": "transport_failed",
            "service": service,
            "path": path,
            "error": str(exc),
            "response_text": "",
            "response_json": None,
        }
    finally:
        try:
            os.unlink(payload_path)
        except OSError:
            pass
    response_text = (proc.stdout or "") + (("\n" + proc.stderr) if proc.stderr else "")
    parsed = None
    if proc.stdout.strip():
        try:
            parsed = json.loads(proc.stdout)
        except json.JSONDecodeError:
            parsed = None
    return {
        "status": "transport_success" if proc.returncode == 0 else "transport_failed",
        "service": service,
        "path": path,
        "returncode": proc.returncode,
        "response_text": response_text,
        "response_json": parsed,
        "error": "" if proc.returncode == 0 else response_tail(response_text, 1000),
    }


def run_oracle_lane(*, dry_run: bool = False) -> dict[str, Any]:
    manifest = load_json(ORACLE_MANIFEST, {})
    if not manifest.get("enabled", False):
        return {"ran": False, "reason": "disabled"}
    claims_doc = load_json(CLAIMS, {})
    if not terminal_claims(claims_doc):
        return {"ran": False, "reason": "claims_not_terminal"}
    topics = list(manifest.get("topics") or [])
    if not topics:
        return {"ran": False, "reason": "no_topics"}
    topic = topics[0]
    prompt = build_prompt(topic, claims_doc)
    topic_hash = sha256_text(json.dumps(topic, sort_keys=True) + "\n" + prompt)
    cooldown_seconds = int(manifest.get("cooldown_seconds") or 21600)
    state = load_json(STATE_PATH, {})
    due, due_reason = due_for_topic(state, topic_hash, cooldown_seconds)
    if not due:
        return {"ran": False, "reason": due_reason}

    record: dict[str, Any] = {
        "record_schema": "window_codon_oracle_candidate.v1",
        "ts": now_iso(),
        "source": "nyxid_oracle_lane",
        "topic_id": topic.get("topic_id"),
        "topic_hash": topic_hash,
        "prompt_sha256": sha256_text(prompt),
        "prompt": prompt,
        "claim_update_allowed": False,
        "verdict_update_allowed": False,
        "promotion_rule": "manual_or_deterministic_experiment_only",
    }
    if dry_run:
        record["status"] = "dry_run"
        record["candidate_axes"] = []
        record["data_requests"] = []
        record["tests"] = []
    else:
        result = run_nyxid(prompt, dict(manifest.get("transport") or {}))
        payload = first_json_payload(result.get("response_json"))
        if payload is None:
            payload = first_json_payload(result.get("response_text"))
        record.update(
            {
                "status": result.get("status"),
                "service": result.get("service"),
                "path": result.get("path"),
                "returncode": result.get("returncode"),
                "response_tail": response_tail(str(result.get("response_text") or "")),
                "oracle_json": payload,
                "error": result.get("error") or "",
            }
        )
        record.update(candidate_fields(payload))
    append_jsonl(INBOX_PATH, record)
    if record.get("status") != "transport_failed":
        write_json(
            STATE_PATH,
            {
                "last_attempt_ts": record["ts"],
                "last_attempt_epoch": time.time(),
                "last_topic_hash": topic_hash,
                "last_status": record.get("status"),
                "last_inbox": str(INBOX_PATH.relative_to(REPO_ROOT)),
            },
        )
    return {
        "ran": True,
        "status": record.get("status"),
        "topic_id": topic.get("topic_id"),
        "inbox": str(INBOX_PATH.relative_to(REPO_ROOT)),
        "candidate_axes": len(record.get("candidate_axes") or []),
        "data_requests": len(record.get("data_requests") or []),
        "tests": len(record.get("tests") or []),
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--dry-run", action="store_true")
    args = parser.parse_args()
    print(json.dumps(run_oracle_lane(dry_run=args.dry_run), ensure_ascii=False, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
