#!/usr/bin/env python3
"""NyxID oracle candidate lane for the Window6--codon-Q6 bridge.

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
PIN_PATH = SCRIPT_DIR / "state" / "omega_oracle_pin.json"
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


def load_oracle_pin() -> dict[str, Any]:
    pin = load_json(PIN_PATH, {})
    return pin if isinstance(pin, dict) else {}


def write_oracle_pin(*, pool: str, conversation_id: str, chatgpt_url: str = "") -> None:
    if not conversation_id:
        return
    current = load_oracle_pin()
    write_json(
        PIN_PATH,
        {
            "pool": pool,
            "conversation_id": conversation_id,
            "chatgpt_url": chatgpt_url or str(current.get("chatgpt_url") or ""),
            "updated_ts": now_iso(),
        },
    )


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
                fields[str(key)] = fields.get(str(key), 0) + 1
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
    question = str(topic.get("question") or "").strip()
    if question:
        return (
            "You are a deep-reasoning research oracle. Answer only the research "
            "question below. Do not ask for local files, do not design local "
            "automation, and do not format as JSON. Reason freely, challenge weak "
            "assumptions, and end with the sharpest next question to ask.\n\n"
            f"Research question:\n{question}"
        )

    return (
        "You are a deep-reasoning research oracle. The local pipeline did not "
        "provide a specific question, so give one concise research direction for "
        "the Window6--Codon-Q6 edge-defect program. Do not format as JSON."
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


def response_fields(text: str, payload: Any = None) -> dict[str, Any]:
    return {
        "oracle_response": text or "",
        "oracle_response_chars": len(text or ""),
        "response_tail": response_tail(text or ""),
        "structured_payload_present": payload is not None,
        "structured_payload": payload,
    }


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


def first_json_object(value: str) -> Any:
    stripped = value.strip()
    if not stripped:
        return None
    try:
        return json.loads(stripped)
    except json.JSONDecodeError:
        pass
    decoder = json.JSONDecoder()
    for index, char in enumerate(stripped):
        if char != "{":
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


def inbox_summary(record: dict[str, Any]) -> dict[str, Any]:
    return {
        "ran": True,
        "status": record.get("status"),
        "topic_id": record.get("topic_id"),
        "inbox": str(INBOX_PATH.relative_to(REPO_ROOT)),
        "oracle_response_chars": record.get("oracle_response_chars", 0),
        "structured_payload_present": bool(record.get("structured_payload_present")),
    }


def oracle_error_code(payload: Any) -> str:
    if not isinstance(payload, dict):
        return ""
    error = payload.get("error")
    if isinstance(error, dict):
        return str(error.get("error") or error.get("code") or error.get("error_code") or "")
    body = payload.get("body")
    if isinstance(body, dict):
        return str(body.get("error") or body.get("code") or body.get("error_code") or "")
    return str(payload.get("error") or payload.get("code") or payload.get("error_code") or "")


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
    kind = str(transport.get("kind") or "nyxid_oracle_cli")
    if kind == "nyxid_responses_api":
        return run_nyxid_proxy(prompt, transport)
    return run_nyxid_oracle_cli(prompt, transport)


def run_nyxid_proxy(prompt: str, transport: dict[str, Any]) -> dict[str, Any]:
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
    transport_ok = proc.returncode == 0 and not (
        isinstance(parsed, dict)
        and isinstance(parsed.get("error"), dict)
    )
    return {
        "status": "transport_success" if transport_ok else "transport_failed",
        "service": service,
        "path": path,
        "returncode": proc.returncode,
        "response_text": response_text,
        "response_json": parsed,
        "error": "" if transport_ok else response_tail(response_text, 1000),
    }


def run_nyxid_oracle_cli(prompt: str, transport: dict[str, Any]) -> dict[str, Any]:
    pool = str(transport.get("pool") or "omega-oracle")
    model = str(transport.get("model") or "")
    tag = str(transport.get("tag") or "window-codon-edge-defect-axis")
    state = load_json(STATE_PATH, {})
    pin = load_oracle_pin()
    conversation_id = str(transport.get("conversation_id") or pin.get("conversation_id") or state.get("conversation_id") or "")
    exe = nyxid_executable()
    if exe is None:
        return {
            "status": "transport_failed",
            "pool": pool,
            "error": "nyxid executable not found",
            "response_text": "",
            "response_json": None,
        }
    pool_status = run_nyxid_oracle_status(pool, transport)
    if pool_status.get("status") == "transport_success":
        status_json = pool_status.get("response_json")
        queued = int(status_json.get("queued") or 0) if isinstance(status_json, dict) else 0
        dispatched = int(status_json.get("dispatched") or 0) if isinstance(status_json, dict) else 0
        max_inflight_before_defer = int(transport.get("max_inflight_before_defer") or 1)
        if queued + dispatched >= max_inflight_before_defer:
            return {
                "status": "oracle_busy",
                "pool": pool,
                "queued": queued,
                "dispatched": dispatched,
                "error": "",
                "response_text": pool_status.get("response_text") or "",
                "response_json": status_json,
            }
    with tempfile.NamedTemporaryFile("w", encoding="utf-8", suffix=".txt", delete=False) as fh:
        fh.write(prompt)
        fh.write("\n")
        prompt_path = fh.name
    cmd = [
        exe,
        "oracle",
        "ask",
        pool,
        "--file",
        prompt_path,
        "--tag",
        tag,
        "--no-wait",
        "--output",
        "json",
    ]
    if model:
        cmd.extend(["--model", model])
    if not conversation_id:
        return {
            "status": "transport_failed",
            "pool": pool,
            "error": "conversation_id is required; refusing to create a new oracle conversation",
            "response_text": "",
            "response_json": None,
        }
    cmd.extend(["--conversation", conversation_id])
    try:
        proc = subprocess.run(
            cmd,
            cwd=str(REPO_ROOT),
            capture_output=True,
            text=True,
            timeout=int(transport.get("submit_timeout_seconds") or 120),
        )
    except (OSError, subprocess.TimeoutExpired) as exc:
        return {
            "status": "transport_failed",
            "pool": pool,
            "error": str(exc),
            "response_text": "",
            "response_json": None,
        }
    finally:
        try:
            os.unlink(prompt_path)
        except OSError:
            pass
    response_text = (proc.stdout or "") + (("\n" + proc.stderr) if proc.stderr else "")
    parsed = first_json_object(proc.stdout) if proc.stdout.strip() else None
    if not isinstance(parsed, dict):
        parsed = first_json_object(response_text)
    error = ""
    if isinstance(parsed, dict) and isinstance(parsed.get("error"), dict):
        error = response_tail(response_text, 1000)
    elif proc.returncode != 0:
        error = response_tail(response_text, 1000)
    status = "transport_success" if proc.returncode == 0 and not error else "transport_failed"
    return {
        "status": status,
        "pool": pool,
        "returncode": proc.returncode,
        "response_text": response_text,
        "response_json": parsed,
        "error": error,
        "task_id": parsed.get("task_id") if isinstance(parsed, dict) else None,
        "conversation_id": parsed.get("conversation_id") if isinstance(parsed, dict) else None,
        "chatgpt_url": parsed.get("chatgpt_url") if isinstance(parsed, dict) else None,
    }


def run_nyxid_oracle_status(pool: str, transport: dict[str, Any]) -> dict[str, Any]:
    exe = nyxid_executable()
    if exe is None:
        return {
            "status": "transport_failed",
            "pool": pool,
            "error": "nyxid executable not found",
            "response_text": "",
            "response_json": None,
        }
    try:
        proc = subprocess.run(
            [
                exe,
                "oracle",
                "status",
                pool,
                "--output",
                "json",
            ],
            cwd=str(REPO_ROOT),
            capture_output=True,
            text=True,
            timeout=int(transport.get("status_timeout_seconds") or 30),
        )
    except (OSError, subprocess.TimeoutExpired) as exc:
        return {
            "status": "transport_failed",
            "pool": pool,
            "error": str(exc),
            "response_text": "",
            "response_json": None,
        }
    response_text = (proc.stdout or "") + (("\n" + proc.stderr) if proc.stderr else "")
    parsed = first_json_object(proc.stdout) if proc.stdout.strip() else None
    if not isinstance(parsed, dict):
        parsed = first_json_object(response_text)
    error = ""
    if isinstance(parsed, dict) and isinstance(parsed.get("error"), dict):
        error = response_tail(response_text, 1000)
    elif proc.returncode != 0:
        error = response_tail(response_text, 1000)
    status = "transport_success" if proc.returncode == 0 and not error else "transport_failed"
    return {
        "status": status,
        "pool": pool,
        "returncode": proc.returncode,
        "response_text": response_text,
        "response_json": parsed,
        "error": error,
    }


def run_nyxid_oracle_result(task_id: str, transport: dict[str, Any]) -> dict[str, Any]:
    exe = nyxid_executable()
    if exe is None:
        return {
            "status": "transport_failed",
            "error": "nyxid executable not found",
            "response_text": "",
            "response_json": None,
        }
    try:
        proc = subprocess.run(
            [
                exe,
                "oracle",
                "result",
                task_id,
                "--output",
                "json",
            ],
            cwd=str(REPO_ROOT),
            capture_output=True,
            text=True,
            timeout=int(transport.get("result_timeout_seconds") or 60),
        )
    except (OSError, subprocess.TimeoutExpired) as exc:
        return {
            "status": "transport_failed",
            "error": str(exc),
            "response_text": "",
            "response_json": None,
        }
    response_text = (proc.stdout or "") + (("\n" + proc.stderr) if proc.stderr else "")
    parsed = first_json_object(proc.stdout) if proc.stdout.strip() else None
    if not isinstance(parsed, dict):
        parsed = first_json_object(response_text)
    error = ""
    if isinstance(parsed, dict) and isinstance(parsed.get("error"), dict):
        error = response_tail(response_text, 1000)
    elif proc.returncode != 0:
        error = response_tail(response_text, 1000)
    status = "transport_success" if proc.returncode == 0 and not error else "transport_failed"
    return {
        "status": status,
        "returncode": proc.returncode,
        "response_text": response_text,
        "response_json": parsed,
        "error": error,
        "task_id": task_id,
        "conversation_id": parsed.get("conversation_id") if isinstance(parsed, dict) else None,
        "chatgpt_url": parsed.get("chatgpt_url") if isinstance(parsed, dict) else None,
    }


def external_transport_allowed(transport: dict[str, Any]) -> tuple[bool, str]:
    allow_env = str(transport.get("allow_env") or "").strip()
    if not allow_env:
        return False, "transport requires an allow_env setting"
    if os.environ.get(allow_env) == "1":
        return True, allow_env
    return False, f"set {allow_env}=1 to allow NyxID transport"


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
    transport = dict(manifest.get("transport") or {})
    pending_task_id = str(state.get("pending_task_id") or "")
    if pending_task_id:
        allowed, allow_reason = external_transport_allowed(transport)
        if not allowed:
            return {"ran": False, "reason": allow_reason, "pending_task_id": pending_task_id}
        result = run_nyxid_oracle_result(pending_task_id, transport)
        parsed = result.get("response_json")
        task_status = str(parsed.get("status") or "") if isinstance(parsed, dict) else ""
        task_response = str(parsed.get("response") or "") if isinstance(parsed, dict) else ""
        if result.get("status") == "transport_success" and task_status != "completed":
            write_json(
                STATE_PATH,
                {
                    **state,
                    "last_status": "awaiting_oracle",
                    "last_check_ts": now_iso(),
                },
            )
            return {
                "ran": False,
                "reason": f"awaiting_oracle:{task_status or 'unknown'}",
                "pending_task_id": pending_task_id,
            }
        if result.get("status") != "transport_success":
            return {
                "ran": True,
                "status": result.get("status"),
                "pending_task_id": pending_task_id,
                "error": result.get("error") or "",
            }
        payload = first_json_payload(task_response)
        record: dict[str, Any] = {
            "record_schema": "window_codon_oracle_candidate.v1",
            "ts": now_iso(),
            "source": "nyxid_oracle_lane",
            "topic_id": state.get("pending_topic_id"),
            "topic_hash": state.get("last_topic_hash"),
            "prompt_sha256": state.get("last_prompt_sha256"),
            "claim_update_allowed": False,
            "verdict_update_allowed": False,
            "promotion_rule": "manual_or_deterministic_experiment_only",
            "status": "transport_success",
            "transport_kind": transport.get("kind"),
            "pool": transport.get("pool"),
            "task_id": pending_task_id,
            "conversation_id": result.get("conversation_id"),
            "chatgpt_url": result.get("chatgpt_url"),
            "error": "",
        }
        record.update(response_fields(task_response, payload))
        record.update(candidate_fields(payload))
        append_jsonl(INBOX_PATH, record)
        write_oracle_pin(
            pool=str(transport.get("pool") or ""),
            conversation_id=str(result.get("conversation_id") or state.get("conversation_id") or ""),
            chatgpt_url=str(result.get("chatgpt_url") or state.get("chatgpt_url") or ""),
        )
        write_json(
            STATE_PATH,
            {
                "last_attempt_ts": record["ts"],
                "last_attempt_epoch": time.time(),
                "last_topic_hash": state.get("last_topic_hash"),
                "last_prompt_sha256": state.get("last_prompt_sha256"),
                "last_status": record.get("status"),
                "last_inbox": str(INBOX_PATH.relative_to(REPO_ROOT)),
                "conversation_id": result.get("conversation_id") or state.get("conversation_id"),
                "chatgpt_url": result.get("chatgpt_url") or state.get("chatgpt_url"),
            },
        )
        return inbox_summary(record)
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
        allowed, allow_reason = external_transport_allowed(transport)
        if not allowed:
            record.update(
                {
                    "status": "prompt_ready",
                    "transport_kind": transport.get("kind"),
                    "pool": transport.get("pool"),
                    "transport_skipped": allow_reason,
                    "candidate_axes": [],
                    "data_requests": [],
                    "tests": [],
                }
            )
        else:
            result = run_nyxid(prompt, transport)
            if result.get("status") == "oracle_busy":
                return {
                    "ran": False,
                    "reason": "oracle_busy:active_tasks",
                    "topic_id": topic.get("topic_id"),
                    "pool": result.get("pool") or transport.get("pool"),
                    "queued": result.get("queued"),
                    "dispatched": result.get("dispatched"),
                }
            transport_payload = result.get("response_json")
            err_code = oracle_error_code(transport_payload)
            if err_code == "oracle_quota_exceeded":
                return {
                    "ran": False,
                    "reason": "oracle_busy:quota_exceeded",
                    "topic_id": topic.get("topic_id"),
                    "pool": transport.get("pool"),
                }
            response_text = ""
            response_payload = None
            if isinstance(transport_payload, dict) and transport_payload.get("response"):
                response_text = str(transport_payload.get("response") or "")
                response_payload = first_json_payload(response_text)
            payload = response_payload or first_json_payload(transport_payload)
            if payload is None:
                payload = first_json_payload(result.get("response_text"))
            record.update(
                {
                    "status": "submitted" if result.get("status") == "transport_success" else result.get("status"),
                    "service": result.get("service"),
                    "path": result.get("path"),
                    "transport_kind": transport.get("kind"),
                    "pool": result.get("pool") or transport.get("pool"),
                    "returncode": result.get("returncode"),
                    "error": result.get("error") or "",
                    "task_id": result.get("task_id"),
                    "conversation_id": result.get("conversation_id"),
                    "chatgpt_url": result.get("chatgpt_url"),
                }
            )
            record.update(response_fields(response_text or str(result.get("response_text") or ""), payload))
            record.update(candidate_fields(payload))
    if record.get("status") != "submitted":
        append_jsonl(INBOX_PATH, record)
    if record.get("status") != "transport_failed":
        write_oracle_pin(
            pool=str(transport.get("pool") or ""),
            conversation_id=str(record.get("conversation_id") or ""),
            chatgpt_url=str(record.get("chatgpt_url") or ""),
        )
        write_json(
            STATE_PATH,
            {
                "last_attempt_ts": record["ts"],
                "last_attempt_epoch": time.time(),
                "last_topic_hash": topic_hash,
                "last_prompt_sha256": record.get("prompt_sha256"),
                "last_status": record.get("status"),
                "last_inbox": str(INBOX_PATH.relative_to(REPO_ROOT)),
                "conversation_id": record.get("conversation_id"),
                "chatgpt_url": record.get("chatgpt_url"),
                "pending_task_id": record.get("task_id") if record.get("status") == "submitted" else None,
                "pending_topic_id": topic.get("topic_id") if record.get("status") == "submitted" else None,
            },
        )
    return inbox_summary(record)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--dry-run", action="store_true")
    args = parser.parse_args()
    print(json.dumps(run_oracle_lane(dry_run=args.dry_run), ensure_ascii=False, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
