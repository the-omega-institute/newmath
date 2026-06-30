#!/usr/bin/env python3
"""Fetch probe for the codon-E1 missense-error-cost orientation panel."""
from __future__ import annotations

from collections import Counter
import hashlib
import json
import re
import sys
import urllib.error
import urllib.request
from pathlib import Path

from _edgehide_spec_fetch_probe import build_panel as build_aaindex_panel


EXPERIMENT_ID = "codon_e1_missense_error_cost_fetch_probe"
CLAIM_ID = "bridge.genetic_code.codon_e1_missense_error_cost_orientation"
USER_AGENT = "codon-e1-missense-error-cost-orientation"
MIN_GENERA = 4
KAZUSA_URL = "https://www.kazusa.or.jp/codon/cgi-bin/showcodon.cgi?species={taxid}&aa=1&style=N"

SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parents[2]
SUPPLY_PANEL_PATH = (
    REPO_ROOT
    / "tools"
    / "window_codon_bridge"
    / "synced"
    / "codon_e1_trna_decoding_supply_orientation_panel.json"
)
PANEL_CACHE_PATH = (
    REPO_ROOT
    / "tools"
    / "window_codon_bridge"
    / "synced"
    / "codon_e1_missense_error_cost_orientation_panel.json"
)

EUKARYOTE_ROSTER = (
    ("Saccharomyces cerevisiae", "saccharomyces", 4932),
    ("Schizosaccharomyces pombe", "schizosaccharomyces", 4896),
    ("Candida albicans", "candida", 5476),
    ("Drosophila melanogaster", "drosophila", 7227),
    ("Caenorhabditis elegans", "caenorhabditis", 6239),
    ("Arabidopsis thaliana", "arabidopsis", 3702),
    ("Dictyostelium discoideum", "dictyostelium", 44689),
    ("Chlamydomonas reinhardtii", "chlamydomonas", 3055),
    ("Homo sapiens", "homo", 9606),
    ("Mus musculus", "mus", 10090),
)

ARCHAEA_HINTS = (
    "archaea",
    "archaeot",
    "pyrococcus",
    "picrophilus",
    "methano",
    "sulfolobus",
    "halo",
    "thermo-archaeal",
    "thermococcus",
    "halobacter",
)

BASES_RNA = ("U", "C", "A", "G")
CODON_RE = re.compile(r"\b([UCAG]{3})\s+([A-Z*])\s+[-+]?[0-9.]+\s+[-+]?[0-9.]+\s+\(\s*([0-9]+)\s*\)")


def codon_order_rna() -> list[str]:
    return [a + b + c for a in BASES_RNA for b in BASES_RNA for c in BASES_RNA]


def fetch_text(url: str, timeout: int = 45, attempts: int = 2) -> tuple[str, dict[str, object]]:
    last_error = "fetch_failed"
    for attempt in range(1, attempts + 1):
        request = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
        try:
            with urllib.request.urlopen(request, timeout=timeout) as response:
                payload = response.read()
                return payload.decode("iso-8859-1", "replace"), {
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
    return "", {"url": url, "reachable": False, "error": last_error, "attempts": attempts}


def classify_domain(row: dict[str, object]) -> str:
    text = f"{row.get('organism', '')} {row.get('genus', '')}".lower()
    return "Archaea" if any(hint in text for hint in ARCHAEA_HINTS) else "Bacteria"


def load_supply_panel() -> tuple[list[dict[str, object]], dict[str, object]]:
    if not SUPPLY_PANEL_PATH.exists():
        return [], {"path": str(SUPPLY_PANEL_PATH), "status": "missing"}
    try:
        panel = json.loads(SUPPLY_PANEL_PATH.read_text(encoding="utf-8"))
    except Exception as exc:
        return [], {"path": str(SUPPLY_PANEL_PATH), "status": "parse_failed", "error": f"{type(exc).__name__}:{exc}"}
    organisms = []
    for entry in panel.get("organisms", []):
        if not isinstance(entry, dict):
            continue
        counts = entry.get("codon_counts_rna")
        if not isinstance(counts, dict):
            continue
        organisms.append(
            {
                "organism": str(entry.get("organism", "")),
                "genus": str(entry.get("genus", "")).lower(),
                "domain": classify_domain(entry),
                "transl_table": int(entry.get("transl_table", 11)),
                "codon_counts_rna": {codon: int(counts.get(codon, 0)) for codon in codon_order_rna()},
                "source": "codon_e1_trna_decoding_supply_orientation_panel",
            }
        )
    return organisms, {"path": str(SUPPLY_PANEL_PATH), "status": "ok", "n_organisms": len(organisms)}


def parse_kazusa_counts(text: str) -> dict[str, int]:
    counts = {codon: 0 for codon in codon_order_rna()}
    seen = set()
    for codon, _aa, count_text in CODON_RE.findall(text):
        counts[codon] = int(count_text)
        seen.add(codon)
    if len(seen) < 64:
        raise ValueError(f"Kazusa page yielded {len(seen)} codon rows")
    return counts


def fetch_eukaryote_row(organism: str, genus: str, taxid: int) -> dict[str, object]:
    url = KAZUSA_URL.format(taxid=taxid)
    text, contact = fetch_text(url)
    if not text:
        return {
            "organism": organism,
            "genus": genus,
            "domain": "Eukaryota",
            "transl_table": 1,
            "ok": False,
            "drop_reason": "kazusa_unreachable",
            "source_contact": contact,
        }
    try:
        counts = parse_kazusa_counts(text)
    except Exception as exc:
        return {
            "organism": organism,
            "genus": genus,
            "domain": "Eukaryota",
            "transl_table": 1,
            "ok": False,
            "drop_reason": "kazusa_parse_failed",
            "exception": f"{type(exc).__name__}:{exc}",
            "source_contact": contact,
        }
    return {
        "organism": organism,
        "genus": genus,
        "domain": "Eukaryota",
        "transl_table": 1,
        "codon_counts_rna": counts,
        "ok": True,
        "source": "Kazusa CUTG codon usage table",
        "source_contact": contact,
    }


def domain_summary(organisms: list[dict[str, object]]) -> dict[str, dict[str, int]]:
    out: dict[str, dict[str, int]] = {}
    for row in organisms:
        domain = str(row["domain"])
        genus = str(row["genus"])
        out.setdefault(domain, {"organisms": 0, "genera": 0})
        out[domain]["organisms"] += 1
    genera: dict[str, set[str]] = {}
    for row in organisms:
        genera.setdefault(str(row["domain"]), set()).add(str(row["genus"]))
    for domain, values in genera.items():
        out.setdefault(domain, {"organisms": 0, "genera": 0})
        out[domain]["genera"] = len(values)
    return dict(sorted(out.items()))


def build_panel(force_refresh: bool = False) -> dict[str, object]:
    if not force_refresh and PANEL_CACHE_PATH.exists():
        return json.loads(PANEL_CACHE_PATH.read_text(encoding="utf-8"))

    organisms, supply_source = load_supply_panel()
    attempts = []
    for organism, genus, taxid in EUKARYOTE_ROSTER:
        row = fetch_eukaryote_row(organism, genus, taxid)
        attempts.append({key: row.get(key) for key in ("organism", "genus", "ok", "drop_reason", "source_contact")})
        if row.get("ok"):
            organisms.append({key: value for key, value in row.items() if key not in {"ok", "drop_reason"}})

    try:
        aaindex_panel = build_aaindex_panel(force_refresh=False)
    except Exception as exc:
        aaindex_panel = {
            "status": "needs_external",
            "fetchable": False,
            "reason": f"{type(exc).__name__}:{exc}",
        }

    summary = domain_summary(organisms)
    thick_domains = [domain for domain, values in summary.items() if int(values.get("genera", 0)) >= MIN_GENERA]
    status = "ok" if len(thick_domains) >= 2 and aaindex_panel.get("status") == "ok" else "needs_external"
    panel = {
        "status": status,
        "experiment_id": EXPERIMENT_ID,
        "claim_id": CLAIM_ID,
        "panel_target": "Bacteria + Archaea from frozen supply panel; Eukaryota from fixed Kazusa CUTG roster",
        "source_status": {
            "supply_panel": supply_source,
            "eukaryote_attempts": attempts,
            "aaindex_status": aaindex_panel.get("status"),
        },
        "min_genera_per_certifying_domain": MIN_GENERA,
        "domain_summary": summary,
        "thick_domains": sorted(thick_domains),
        "n_domains": len(summary),
        "n_organisms": len(organisms),
        "n_genera": len({str(row["genus"]) for row in organisms}),
        "organisms": organisms,
        "aaindex": aaindex_panel,
    }
    PANEL_CACHE_PATH.parent.mkdir(parents=True, exist_ok=True)
    PANEL_CACHE_PATH.write_text(json.dumps(panel, ensure_ascii=True, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return panel


def emit(payload: dict[str, object]) -> None:
    print(json.dumps(payload, ensure_ascii=True, sort_keys=False, separators=(",", ":")))
    sys.exit(0 if payload.get("status") == "ok" else 3)


def main() -> None:
    panel = build_panel(force_refresh=True)
    emit(
        {
            "status": panel.get("status"),
            "experiment_id": EXPERIMENT_ID,
            "claim_id": CLAIM_ID,
            "domain_summary": panel.get("domain_summary"),
            "thick_domains": panel.get("thick_domains"),
            "n_organisms": panel.get("n_organisms"),
            "cache_path": str(PANEL_CACHE_PATH),
        }
    )


if __name__ == "__main__":
    main()
