#!/usr/bin/env python3
"""Fetch NCBI gc.prt genetic-code definitions for reassignment tests."""
from __future__ import annotations

from datetime import datetime, timezone
import hashlib
import json
import re
import sys
import time
import urllib.error
import urllib.request
from pathlib import Path
from typing import Any


EXPERIMENT_ID = "edge_hiding_alternative_code_reassignment_fetch_probe"
USER_AGENT = "edge-hiding-alternative-code-reassignment"
GC_PRT_URLS = (
    "https://ftp.ncbi.nlm.nih.gov/entrez/misc/data/gc.prt",
    "https://www.ncbi.nlm.nih.gov/IEB/ToolBox/C_DOC/lxr/source/data/gc.prt",
)

EXPERIMENT_DIR = Path(__file__).resolve().parent
REPO_ROOT = EXPERIMENT_DIR.parents[2]
CACHE_PATH = (
    REPO_ROOT
    / "tools"
    / "window_codon_bridge"
    / "synced"
    / "edge_hiding_alternative_code_reassignment_gc_prt.json"
)


def now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def emit(status: str, **fields: object) -> None:
    payload = {"status": status, "experiment_id": EXPERIMENT_ID}
    payload.update(fields)
    print(json.dumps(payload, ensure_ascii=True, sort_keys=False, separators=(",", ":")))
    sys.exit(0 if status == "ok" else 3)


def fetch_text(url: str, timeout: int = 45, attempts: int = 3) -> tuple[str, dict[str, object]]:
    last_error = "fetch_failed"
    for attempt in range(1, attempts + 1):
        request = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
        try:
            with urllib.request.urlopen(request, timeout=timeout) as response:
                payload = response.read()
                text = payload.decode("utf-8", "replace")
                return text, {
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


def parse_gc_prt(text: str) -> dict[str, object]:
    table_pos = text.find("Genetic-code-table ::=")
    if table_pos < 0:
        raise ValueError("gc.prt does not contain Genetic-code-table")
    outer_open = text.find("{", table_pos)
    if outer_open < 0:
        raise ValueError("gc.prt Genetic-code-table has no outer brace")
    blocks: list[str] = []
    depth = 0
    block_start: int | None = None
    for pos in range(outer_open, len(text)):
        char = text[pos]
        if char == "{":
            depth += 1
            if depth == 2:
                block_start = pos
        elif char == "}":
            if depth == 2 and block_start is not None:
                blocks.append(text[block_start : pos + 1])
                block_start = None
            depth -= 1
            if depth == 0:
                break
    tables: list[dict[str, object]] = []
    codon_order: list[str] | None = None
    for block in blocks:
        id_match = re.search(r"\bid\s+(\d+)\s*,", block)
        aa_match = re.search(r'\bncbieaa\s+"([^"]+)"', block)
        starts_match = re.search(r'\bsncbieaa\s+"([^"]+)"', block)
        base1_match = re.search(r"--\s*Base1\s+([TCAG]{64})", block)
        base2_match = re.search(r"--\s*Base2\s+([TCAG]{64})", block)
        base3_match = re.search(r"--\s*Base3\s+([TCAG]{64})", block)
        if not id_match or not aa_match:
            continue
        table_id = int(id_match.group(1))
        ncbieaa = aa_match.group(1)
        if len(ncbieaa) != 64:
            raise ValueError(f"table {table_id} ncbieaa length {len(ncbieaa)}, expected 64")
        names = re.findall(r'\bname\s+"([^"]+)"', block)
        if base1_match and base2_match and base3_match and codon_order is None:
            codon_order = [
                "".join(parts)
                for parts in zip(base1_match.group(1), base2_match.group(1), base3_match.group(1))
            ]
        tables.append(
            {
                "id": table_id,
                "name": names[0] if names else f"NCBI genetic code {table_id}",
                "aliases": names[1:],
                "ncbieaa": ncbieaa,
                "sncbieaa": starts_match.group(1) if starts_match else None,
            }
        )
    if codon_order is None:
        raise ValueError("gc.prt did not expose Base1/Base2/Base3 codon order")
    if len(codon_order) != 64 or len(set(codon_order)) != 64:
        raise ValueError("gc.prt Base1/Base2/Base3 codon order is not a 64-codon permutation")
    by_id = {int(table["id"]): table for table in tables}
    if 1 not in by_id:
        raise ValueError("gc.prt did not contain standard code id=1")
    nonstandard = [
        table
        for table in tables
        if int(table["id"]) != 1 and str(table["ncbieaa"]) != str(by_id[1]["ncbieaa"])
    ]
    return {
        "codon_order": codon_order,
        "tables": sorted(tables, key=lambda item: int(item["id"])),
        "standard_table_id": 1,
        "n_tables": len(tables),
        "n_nonstandard_aa_distinct": len(nonstandard),
    }


def build_panel(force_refresh: bool = True) -> dict[str, object]:
    if not force_refresh and CACHE_PATH.exists():
        return json.loads(CACHE_PATH.read_text(encoding="utf-8"))
    contacts: list[dict[str, object]] = []
    text = ""
    source: dict[str, object] | None = None
    for url in GC_PRT_URLS:
        text, contact = fetch_text(url)
        contacts.append(contact)
        if contact.get("reachable"):
            source = contact
            break
    if not text or source is None:
        return {
            "status": "needs_external",
            "fetchable": False,
            "fetched_at": now_iso(),
            "source": None,
            "contacts": contacts,
            "reason": "NCBI gc.prt fetch did not return a parseable payload",
        }
    parsed = parse_gc_prt(text)
    panel = {
        "status": "ok",
        "fetchable": True,
        "fetched_at": now_iso(),
        "source": source,
        "contacts": contacts,
        **parsed,
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
        n_tables=panel.get("n_tables"),
        n_nonstandard_aa_distinct=panel.get("n_nonstandard_aa_distinct"),
        cache_path=str(CACHE_PATH),
    )


if __name__ == "__main__":
    main()
