#!/usr/bin/env python3
"""Fetch AAindex1 physicochemical scales for reassignment-specificity tests."""
from __future__ import annotations

from datetime import datetime, timezone
import hashlib
import json
import sys
import time
import urllib.error
import urllib.request
from pathlib import Path


EXPERIMENT_ID = "edge_hiding_reassignment_specificity_fetch_probe"
USER_AGENT = "edge-hiding-reassignment-specificity"
AAINDEX1_URL = "https://www.genome.jp/ftp/db/community/aaindex/aaindex1"
TARGET_INDICES = (
    "WOEC730101",
    "GRAR740102",
    "GRAR740103",
    "KYTJ820101",
)
AA_ORDER = tuple("ARNDCQEGHILKMFPSTWYV")

EXPERIMENT_DIR = Path(__file__).resolve().parent
REPO_ROOT = EXPERIMENT_DIR.parents[2]
CACHE_PATH = REPO_ROOT / "tools" / "window_codon_bridge" / "synced" / "edge_hiding_reassignment_specificity_aaindex1.json"


def now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def emit(status: str, **fields: object) -> None:
    payload = {"status": status, "experiment_id": EXPERIMENT_ID}
    payload.update(fields)
    print(json.dumps(payload, ensure_ascii=True, sort_keys=False, separators=(",", ":")))
    sys.exit(0 if status == "ok" else 3)


def fetch_text(url: str = AAINDEX1_URL, timeout: int = 45, attempts: int = 3) -> tuple[str, dict[str, object]]:
    last_error = "fetch_failed"
    for attempt in range(1, attempts + 1):
        request = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
        try:
            with urllib.request.urlopen(request, timeout=timeout) as response:
                payload = response.read()
                return payload.decode("utf-8", "replace"), {
                    "url": url,
                    "reachable": True,
                    "http_status": int(getattr(response, "status", 200)),
                    "byte_size": len(payload),
                    "sha256": hashlib.sha256(payload).hexdigest(),
                    "attempts": attempt,
                }
        except urllib.error.HTTPError as exc:
            last_error = f"HTTPError:{exc.code}"
        except urllib.error.URLError as exc:
            last_error = f"URLError:{exc.reason}"
        except TimeoutError:
            last_error = "TimeoutError"
        except Exception as exc:  # pragma: no cover - network boundary
            last_error = f"{type(exc).__name__}:{exc}"
        time.sleep(0.5 * attempt)
    return "", {"url": url, "reachable": False, "error": last_error, "attempts": attempts}


def parse_float_token(token: str) -> float:
    if token.upper() == "NA":
        raise ValueError("AAindex value is NA")
    return float(token)


def parse_index_record(record: str) -> dict[str, object]:
    lines = record.splitlines()
    header = ""
    description = ""
    values: dict[str, float] | None = None
    for line in lines:
        if line.startswith("H "):
            header = line.split(None, 1)[1].strip()
        elif line.startswith("D "):
            description = line[2:].strip()
    for idx, line in enumerate(lines):
        if not line.startswith("I "):
            continue
        pairs = line[1:].split()
        if len(pairs) != 10 or any("/" not in pair for pair in pairs):
            raise ValueError(f"{header} has unexpected AAindex I header")
        first_residues = [pair.split("/", 1)[0] for pair in pairs]
        second_residues = [pair.split("/", 1)[1] for pair in pairs]
        number_tokens: list[str] = []
        cursor = idx + 1
        while cursor < len(lines) and len(number_tokens) < 20:
            stripped = lines[cursor].strip()
            if stripped and stripped[0].isdigit() or stripped.startswith(("-", "+", ".")):
                number_tokens.extend(stripped.split())
            cursor += 1
        if len(number_tokens) < 20:
            raise ValueError(f"{header} has fewer than 20 numeric values")
        floats = [parse_float_token(token) for token in number_tokens[:20]]
        values = {}
        for residue, value in zip(first_residues, floats[:10]):
            values[residue] = value
        for residue, value in zip(second_residues, floats[10:20]):
            values[residue] = value
        break
    if not header:
        raise ValueError("AAindex record has no H line")
    if values is None:
        raise ValueError(f"{header} has no parseable I block")
    missing = [residue for residue in AA_ORDER if residue not in values]
    if missing:
        raise ValueError(f"{header} missing residues {missing}")
    return {
        "id": header,
        "description": description,
        "values": {residue: values[residue] for residue in AA_ORDER},
    }


def parse_aaindex1(text: str) -> dict[str, dict[str, object]]:
    records: dict[str, dict[str, object]] = {}
    for raw_record in text.split("//"):
        record = raw_record.strip()
        if not record:
            continue
        parsed = parse_index_record(record)
        index_id = str(parsed["id"])
        if index_id in TARGET_INDICES:
            records[index_id] = parsed
    missing = [index_id for index_id in TARGET_INDICES if index_id not in records]
    if missing:
        raise ValueError(f"AAindex1 missing target indices {missing}")
    return {index_id: records[index_id] for index_id in TARGET_INDICES}


def sample_values(records: dict[str, dict[str, object]]) -> dict[str, dict[str, float]]:
    out: dict[str, dict[str, float]] = {}
    for index_id, record in records.items():
        values = record["values"]
        assert isinstance(values, dict)
        out[index_id] = {residue: float(values[residue]) for residue in ("A", "R", "N", "D", "C")}
    return out


def build_panel(force_refresh: bool = True) -> dict[str, object]:
    if not force_refresh and CACHE_PATH.exists():
        return json.loads(CACHE_PATH.read_text(encoding="utf-8"))
    text, source = fetch_text()
    if not source.get("reachable") or not text:
        return {
            "status": "needs_external",
            "fetchable": False,
            "fetched_at": now_iso(),
            "source": source,
            "reason": "AAindex1 fetch did not return a parseable payload",
        }
    records = parse_aaindex1(text)
    panel = {
        "status": "ok",
        "fetchable": True,
        "fetched_at": now_iso(),
        "source": source,
        "target_indices": list(TARGET_INDICES),
        "aa_order": "".join(AA_ORDER),
        "records": records,
        "sample_values": sample_values(records),
    }
    CACHE_PATH.parent.mkdir(parents=True, exist_ok=True)
    CACHE_PATH.write_text(json.dumps(panel, ensure_ascii=True, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return panel


def main() -> None:
    try:
        panel = build_panel(force_refresh=True)
    except Exception as exc:
        emit("needs_external", fetchable=False, reason=f"{type(exc).__name__}:{exc}")
    if not panel.get("fetchable"):
        emit("needs_external", **panel)
    emit(
        "ok",
        fetchable=True,
        source=panel.get("source"),
        target_indices=panel.get("target_indices"),
        sample_values=panel.get("sample_values"),
        cache_path=str(CACHE_PATH),
    )


if __name__ == "__main__":
    main()
