#!/usr/bin/env python3
"""Fetch and support probe for non-mitochondrial reassignment edge hiding.

The xlsx reader is intentionally stdlib-only: xlsx files are ZIP archives of
OpenXML sheets, with sharedStrings.xml providing most text cells.
"""
from __future__ import annotations

from collections import defaultdict
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
import math
from pathlib import Path
import re
import sys
import time
import urllib.error
import urllib.request
import zipfile
import xml.etree.ElementTree as ET
from typing import Any


EXPERIMENT_ID = "edge_hiding_nonmito_generalization_fetch_probe"
USER_AGENT = "edge-hiding-nonmito-generalization"
GITHUB_RAW = "https://raw.githubusercontent.com/kshulgina/ShulginaEddy_21_genetic_codes/master"
MIN_STRATUM_SIZE = 20

EXPERIMENT_DIR = Path(__file__).resolve().parent
REPO_ROOT = EXPERIMENT_DIR.parents[2]
ALT_PATH = EXPERIMENT_DIR / "run_edge_hiding_alternative_code_reassignment.py"
CACHE_PATH = (
    REPO_ROOT
    / "tools"
    / "window_codon_bridge"
    / "synced"
    / "edge_hiding_nonmito_generalization_panel.json"
)

BASES = ("T", "C", "A", "G")
AA3_TO_1 = {
    "Ala": "A",
    "Arg": "R",
    "Asn": "N",
    "Asp": "D",
    "Cys": "C",
    "Gln": "Q",
    "Glu": "E",
    "Gly": "G",
    "His": "H",
    "Ile": "I",
    "Leu": "L",
    "Lys": "K",
    "Met": "M",
    "Phe": "F",
    "Pro": "P",
    "Ser": "S",
    "Thr": "T",
    "Trp": "W",
    "Tyr": "Y",
    "Val": "V",
    "Stop": "*",
}
AA1_TO_3 = {value: key for key, value in AA3_TO_1.items()}

EVENT_SPECS: tuple[dict[str, object], ...] = (
    {
        "event_id": "Bacilli_AGG_Met",
        "directory": "Bacilli_AGG_Met",
        "reassignments": {"AGG": "M"},
    },
    {
        "event_id": "Peptacetobacter_CGG_Gln",
        "directory": "Peptacetobacter_CGG_Gln",
        "reassignments": {"CGG": "Q"},
    },
    {
        "event_id": "Bacilli_CGG_Trp",
        "directory": "Bacilli_CGG_Trp",
        "reassignments": {"CGG": "W"},
    },
    {
        "event_id": "Anaerococcus_CGG_Trp",
        "directory": "Anaerococcus_CGG_Trp",
        "reassignments": {"CGG": "W"},
    },
    {
        "event_id": "Absconditabacteria_CGA_CGG_Trp",
        "directory": "Absconditabacteria_CGA_CGG_Trp",
        "reassignments": {"CGA": "W", "CGG": "W"},
    },
)

XML_NS = {
    "a": "http://schemas.openxmlformats.org/spreadsheetml/2006/main",
    "r": "http://schemas.openxmlformats.org/officeDocument/2006/relationships",
    "rel": "http://schemas.openxmlformats.org/package/2006/relationships",
}


def load_alt_module() -> Any:
    spec = importlib.util.spec_from_file_location("_edgehide_alt_reassign", ALT_PATH)
    if spec is None or spec.loader is None:
        raise RuntimeError("could not load run_edge_hiding_alternative_code_reassignment.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


ALT = load_alt_module()


def now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def emit(status: str, **fields: object) -> None:
    payload = {"status": status, "experiment_id": EXPERIMENT_ID}
    payload.update(fields)
    print(json.dumps(payload, ensure_ascii=True, sort_keys=False, separators=(",", ":")))
    sys.exit(0 if status == "ok" else 3)


def fetch_bytes(url: str, timeout: int = 45, attempts: int = 3) -> tuple[bytes, dict[str, object]]:
    last_error = "fetch_failed"
    for attempt in range(1, attempts + 1):
        request = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
        try:
            with urllib.request.urlopen(request, timeout=timeout) as response:
                payload = response.read()
                return payload, {
                    "url": url,
                    "reachable": True,
                    "http_status": int(getattr(response, "status", 200)),
                    "byte_size": len(payload),
                    "sha256": hashlib.sha256(payload).hexdigest(),
                    "attempts": attempt,
                }
        except urllib.error.HTTPError as exc:
            last_error = f"HTTPError:{exc.code}"
            if exc.code != 429:
                break
        except urllib.error.URLError as exc:
            last_error = f"URLError:{exc.reason}"
        except TimeoutError:
            last_error = "TimeoutError"
        except Exception as exc:  # pragma: no cover - network boundary
            last_error = f"{type(exc).__name__}:{exc}"
        time.sleep(0.5 * attempt)
    return b"", {"url": url, "reachable": False, "error": last_error, "attempts": attempts}


def col_number(col_ref: str) -> int:
    out = 0
    for char in col_ref:
        out = out * 26 + ord(char) - ord("A") + 1
    return out


def parse_cell_ref(ref: str) -> tuple[str, int]:
    match = re.fullmatch(r"([A-Z]+)([0-9]+)", ref)
    if not match:
        return ref, 0
    return match.group(1), int(match.group(2))


def read_xlsx_rows(payload: bytes) -> list[dict[str, str]]:
    with zipfile.ZipFile(PathLikeBytes(payload)) as archive:
        shared: list[str] = []
        if "xl/sharedStrings.xml" in archive.namelist():
            root = ET.fromstring(archive.read("xl/sharedStrings.xml"))
            for si in root.findall("a:si", XML_NS):
                shared.append("".join(node.text or "" for node in si.findall(".//a:t", XML_NS)))
        workbook = ET.fromstring(archive.read("xl/workbook.xml"))
        rel_root = ET.fromstring(archive.read("xl/_rels/workbook.xml.rels"))
        rels = {rel.attrib["Id"]: rel.attrib["Target"] for rel in rel_root}
        first_sheet = workbook.find(".//a:sheet", XML_NS)
        if first_sheet is None:
            raise ValueError("xlsx workbook has no sheets")
        rel_id = first_sheet.attrib["{http://schemas.openxmlformats.org/officeDocument/2006/relationships}id"]
        target = rels[rel_id]
        sheet_path = target.lstrip("/")
        if not sheet_path.startswith("xl/"):
            sheet_path = f"xl/{sheet_path}"
        sheet = ET.fromstring(archive.read(sheet_path))
        rows: list[dict[str, str]] = []
        for row in sheet.findall(".//a:sheetData/a:row", XML_NS):
            row_out: dict[str, str] = {}
            for cell in row.findall("a:c", XML_NS):
                ref = cell.attrib.get("r", "")
                col, _row_num = parse_cell_ref(ref)
                cell_type = cell.attrib.get("t")
                value_node = cell.find("a:v", XML_NS)
                value = "" if value_node is None else value_node.text or ""
                if cell_type == "s" and value:
                    value = shared[int(value)]
                elif cell_type == "inlineStr":
                    value = "".join(node.text or "" for node in cell.findall(".//a:t", XML_NS))
                row_out[col] = value.strip()
            rows.append(row_out)
        return rows


class PathLikeBytes:
    def __init__(self, payload: bytes):
        self.payload = payload
        self.offset = 0

    def read(self, size: int = -1) -> bytes:
        if size is None or size < 0:
            size = len(self.payload) - self.offset
        start = self.offset
        end = min(len(self.payload), self.offset + size)
        self.offset = end
        return self.payload[start:end]

    def seek(self, offset: int, whence: int = 0) -> int:
        if whence == 0:
            self.offset = offset
        elif whence == 1:
            self.offset += offset
        elif whence == 2:
            self.offset = len(self.payload) + offset
        else:
            raise ValueError("bad whence")
        return self.offset

    def tell(self) -> int:
        return self.offset

    def seekable(self) -> bool:
        return True


def parse_float(value: str) -> float | None:
    if value is None:
        return None
    text = str(value).strip()
    if not text or text == "?":
        return None
    try:
        return float(text)
    except ValueError:
        return None


def median(values: list[float]) -> float | None:
    if not values:
        return None
    ordered = sorted(values)
    mid = len(ordered) // 2
    if len(ordered) % 2:
        return ordered[mid]
    return (ordered[mid - 1] + ordered[mid]) / 2.0


def round_float(value: float | None, digits: int = 12) -> float | None:
    if value is None:
        return None
    if not math.isfinite(value):
        return value
    rounded = round(value, digits)
    return 0.0 if rounded == -0.0 else rounded


def dna(codon: str) -> str:
    return codon.upper().replace("U", "T")


def rna(codon: str) -> str:
    return codon.upper().replace("T", "U")


def codon_order() -> list[str]:
    return ["".join(parts) for parts in zip("T" * 16 + "C" * 16 + "A" * 16 + "G" * 16, "TTTTCCCCAAAAGGGG" * 4, "TCAG" * 16)]


def standard_code_from_gc_prt() -> tuple[list[str], list[str]]:
    probe = ALT.load_probe_module()
    panel = probe.build_panel(force_refresh=True)
    if not panel.get("fetchable"):
        raise RuntimeError("NCBI gc.prt standard-code fetch failed")
    codons = list(panel["codon_order"])
    tables = list(panel["tables"])
    standard_rows = [table for table in tables if int(table["id"]) == 1]
    if len(standard_rows) != 1:
        raise RuntimeError("gc.prt did not expose a unique standard code id=1")
    return codons, list(str(standard_rows[0]["ncbieaa"]))


def infer_header(rows: list[dict[str, str]]) -> tuple[int, dict[str, str]]:
    for idx, row in enumerate(rows):
        if any(value == "GenBank accession" for value in row.values()):
            return idx, row
    raise ValueError("xlsx sheet has no GenBank accession header row")


def normalize_aa_value(value: str) -> str | None:
    text = str(value).strip()
    if not text or text == "?":
        return None
    if text in AA3_TO_1:
        return AA3_TO_1[text]
    if len(text) == 1 and text in set(AA1_TO_3):
        return text
    return None


def codon_usage_columns(header: dict[str, str]) -> dict[str, str]:
    out: dict[str, str] = {}
    for col, label in header.items():
        if re.fullmatch(r"[ACGUTacgut]{3}", label.strip()):
            out[dna(label)] = col
    return out


def inferred_columns(header: dict[str, str]) -> dict[str, str]:
    out: dict[str, str] = {}
    for col, label in header.items():
        match = re.fullmatch(r"Inferred\s+([ACGUTacgut]{3})", label.strip())
        if match:
            out[dna(match.group(1))] = col
    return out


def family_codons(standard: list[str], codons: list[str], source_aa: str) -> list[str]:
    return [codon for codon, aa in zip(codons, standard) if aa == source_aa]


def group_rows(
    rows: list[dict[str, str]],
    header_idx: int,
    header: dict[str, str],
    event_codons: list[str],
    source_aa: str,
    target_by_codon: dict[str, str],
) -> tuple[list[dict[str, object]], list[dict[str, object]]]:
    accession_col = next(col for col, label in header.items() if label == "GenBank accession")
    inferred = inferred_columns(header)
    gc_col = next((col for col, label in header.items() if label == "Genomic GC content"), None)
    reassigned_rows: list[dict[str, object]] = []
    outgroup_rows: list[dict[str, object]] = []
    current_group = ""
    for row in rows[header_idx + 1 :]:
        if row.get("A"):
            current_group = row.get("A", "")
        accession = row.get(accession_col, "")
        if not accession:
            continue
        inferred_values = {
            codon: normalize_aa_value(row.get(inferred.get(codon, ""), "")) for codon in event_codons
        }
        known_values = [value for value in inferred_values.values() if value is not None]
        if not known_values:
            continue
        record = {
            "accession": accession,
            "group_label": current_group,
            "inferred": inferred_values,
            "genomic_gc": parse_float(row.get(gc_col or "", "")),
            "row": row,
        }
        if all(inferred_values.get(codon) == target_by_codon[codon] for codon in event_codons):
            reassigned_rows.append(record)
        if all(inferred_values.get(codon) == source_aa for codon in event_codons):
            outgroup_rows.append(record)
    return reassigned_rows, outgroup_rows


def relative_family_usage(
    rows: list[dict[str, object]],
    usage_cols: dict[str, str],
    family: list[str],
) -> dict[str, list[float]]:
    values: dict[str, list[float]] = {codon: [] for codon in family}
    for record in rows:
        row = record["row"]
        assert isinstance(row, dict)
        raw = {codon: parse_float(str(row.get(usage_cols.get(codon, ""), ""))) for codon in family}
        if any(value is None for value in raw.values()):
            continue
        total = sum(float(value) for value in raw.values() if value is not None)
        if total <= 0.0:
            continue
        for codon, value in raw.items():
            assert value is not None
            values[codon].append(float(value) / total)
    return values


def availability_profile(rows: list[dict[str, object]], usage_cols: dict[str, str], family: list[str]) -> dict[str, object]:
    rel_values = relative_family_usage(rows, usage_cols, family)
    availability = {codon: median(values) for codon, values in rel_values.items()}
    rscu = {
        codon: (None if availability[codon] is None else availability[codon] * len(family))
        for codon in family
    }
    complete_codons = [codon for codon, value in availability.items() if value is not None]
    ranked = sorted(
        (float(value), codon)
        for codon, value in availability.items()
        if value is not None
    )
    bins: dict[str, int] = {}
    n = len(ranked)
    for pos, (_value, codon) in enumerate(ranked):
        bins[codon] = min(2, (pos * 3) // max(n, 1))
    return {
        "n_rows_with_complete_family_usage": min((len(values) for values in rel_values.values()), default=0),
        "availability": {codon: round_float(value) for codon, value in availability.items()},
        "rscu": {codon: round_float(value) for codon, value in rscu.items()},
        "rank_tercile": bins,
        "complete_codons": complete_codons,
    }


def enumerate_candidate_sets(
    standard: list[str],
    codons: list[str],
    matrix: dict[tuple[str, str], int],
) -> list[dict[str, object]]:
    grouped = ALT.source_targets(matrix)
    source_options: list[tuple[str, list[dict[int, str]]]] = []
    for source in sorted(grouped):
        indices = [idx for idx, label in enumerate(standard) if label == source]
        source_options.append((source, ALT.assignment_options(indices, grouped[source])))
    candidates: list[dict[str, object]] = []

    def rec(pos: int, updates: dict[int, str]) -> None:
        if pos == len(source_options):
            changed_codons = sorted(codons[index] for index in updates)
            candidates.append(
                {
                    "codons": changed_codons,
                    "updates": {codons[index]: label for index, label in sorted(updates.items())},
                }
            )
            return
        _source, options = source_options[pos]
        for option in options:
            next_updates = dict(updates)
            next_updates.update(option)
            rec(pos + 1, next_updates)

    rec(0, {})
    return candidates


def third_gc(codon: str) -> str:
    return "GC3" if codon[2] in {"G", "C"} else "AT3"


def signature_for(codons: list[str], rank_bins: dict[str, int]) -> list[tuple[int, str]]:
    return sorted((rank_bins.get(codon, -1), third_gc(codon)) for codon in codons)


def relaxed_signature_match(
    observed: list[tuple[int, str]],
    candidate: list[tuple[int, str]],
    radius: int | None,
    require_gc: bool,
) -> bool:
    if len(observed) != len(candidate):
        return False
    used = [False] * len(candidate)
    for obs_bin, obs_gc in observed:
        hit = None
        for idx, (cand_bin, cand_gc) in enumerate(candidate):
            if used[idx]:
                continue
            if require_gc and cand_gc != obs_gc:
                continue
            if radius is not None and (obs_bin < 0 or cand_bin < 0 or abs(obs_bin - cand_bin) > radius):
                continue
            hit = idx
            break
        if hit is None:
            return False
        used[hit] = True
    return True


def matched_candidates(
    candidates: list[dict[str, object]],
    observed_codons: list[str],
    rank_bins: dict[str, int],
) -> dict[str, object]:
    observed_sig = signature_for(observed_codons, rank_bins)
    exact = [
        candidate
        for candidate in candidates
        if signature_for(list(candidate["codons"]), rank_bins) == observed_sig  # type: ignore[arg-type]
    ]
    if len(exact) >= MIN_STRATUM_SIZE:
        selected = exact
        rule = "availability_tercile_and_third_gc"
    else:
        selected = exact
        rule = "availability_tercile_and_third_gc_low_support"
        for radius in (1, 2):
            relaxed = [
                candidate
                for candidate in candidates
                if relaxed_signature_match(
                    observed_sig,
                    signature_for(list(candidate["codons"]), rank_bins),  # type: ignore[arg-type]
                    radius,
                    require_gc=True,
                )
            ]
            if len(relaxed) > len(selected):
                selected = relaxed
                rule = f"availability_adjacent_tercile_radius_{radius}_and_third_gc_low_support"
            if len(selected) >= MIN_STRATUM_SIZE:
                break
        if len(selected) < MIN_STRATUM_SIZE:
            same_gc = [
                candidate
                for candidate in candidates
                if relaxed_signature_match(
                    observed_sig,
                    signature_for(list(candidate["codons"]), rank_bins),  # type: ignore[arg-type]
                    None,
                    require_gc=True,
                )
            ]
            if len(same_gc) > len(selected):
                selected = same_gc
                rule = "third_gc_only_after_availability_relaxation_low_support"
        if len(selected) < 2:
            selected = candidates
            rule = "all_transition_matrix_candidates_degenerate_availability_gc"
    observed_set = set(observed_codons)
    has_unobserved_candidate = any(set(candidate["codons"]) != observed_set for candidate in selected)  # type: ignore[arg-type]
    return {
        "rule": rule,
        "observed_signature": [[rank_bin, gc] for rank_bin, gc in observed_sig],
        "matched_support": len(selected),
        "low_support": len(selected) < MIN_STRATUM_SIZE,
        "nondegenerate": bool(has_unobserved_candidate),
        "candidate_codons": [candidate["codons"] for candidate in selected],
    }


def event_panel(spec: dict[str, object], codons: list[str], standard: list[str]) -> dict[str, object]:
    event_id = str(spec["event_id"])
    directory = str(spec["directory"])
    reassignments = {dna(codon): str(aa) for codon, aa in dict(spec["reassignments"]).items()}
    source_aas = {standard[codons.index(codon)] for codon in reassignments}
    if len(source_aas) != 1:
        raise ValueError(f"{event_id} crosses source amino-acid families: {sorted(source_aas)}")
    source_aa = next(iter(source_aas))
    matrix = ALT.transition_matrix(standard, [reassignments.get(codon, aa) for codon, aa in zip(codons, standard)])
    key = ALT.cluster_key(matrix)
    url = f"{GITHUB_RAW}/{directory}/{directory}_genomes_info.xlsx"
    payload, contact = fetch_bytes(url)
    if not payload:
        return {
            "event_id": event_id,
            "status": "needs_external",
            "reason": "xlsx fetch failed",
            "source": contact,
        }
    rows = read_xlsx_rows(payload)
    header_idx, header = infer_header(rows)
    usage_cols = codon_usage_columns(header)
    family = family_codons(standard, codons, source_aa)
    inferred = inferred_columns(header)
    missing_usage = [codon for codon in family if codon not in usage_cols]
    missing_inferred = [codon for codon in reassignments if codon not in inferred]
    reassigned_rows, outgroup_rows = group_rows(
        rows,
        header_idx,
        header,
        list(reassignments),
        source_aa,
        reassignments,
    )
    outgroup_profile = availability_profile(outgroup_rows, usage_cols, family) if not missing_usage else {}
    candidates = enumerate_candidate_sets(standard, codons, matrix)
    observed_codons = sorted(reassignments)
    support = (
        matched_candidates(candidates, observed_codons, dict(outgroup_profile.get("rank_tercile", {})))
        if outgroup_profile and not missing_usage
        else {
            "rule": "unavailable",
            "matched_support": 0,
            "low_support": True,
            "nondegenerate": False,
            "candidate_codons": [],
            "observed_signature": [],
        }
    )
    reassigned_gc_values = [float(row["genomic_gc"]) for row in reassigned_rows if row.get("genomic_gc") is not None]
    outgroup_gc_values = [float(row["genomic_gc"]) for row in outgroup_rows if row.get("genomic_gc") is not None]
    usable = (
        not missing_usage
        and not missing_inferred
        and len(reassigned_rows) > 0
        and len(outgroup_rows) > 0
        and bool(outgroup_profile.get("complete_codons"))
        and int(support["matched_support"]) > 0
    )
    return {
        "event_id": event_id,
        "status": "ok" if usable else "needs_external",
        "directory": directory,
        "source": contact,
        "reassigned_codons": [rna(codon) for codon in observed_codons],
        "reassignments": {rna(codon): aa for codon, aa in reassignments.items()},
        "source_aa": source_aa,
        "source_aa_name": AA1_TO_3.get(source_aa, source_aa),
        "target_aas": sorted(set(reassignments.values())),
        "transition_matrix": {f"{source}>{target}": count for (source, target), count in matrix.items()},
        "cluster_key": key,
        "xlsx_header_row": header_idx + 1,
        "inferred_columns": {rna(codon): inferred.get(codon) for codon in reassignments},
        "codon_usage_columns": {rna(codon): usage_cols.get(codon) for codon in family},
        "missing_usage_columns": [rna(codon) for codon in missing_usage],
        "missing_inferred_columns": [rna(codon) for codon in missing_inferred],
        "n_reassigned_rows": len(reassigned_rows),
        "n_outgroup_rows": len(outgroup_rows),
        "reassigned_accessions_sample": [row["accession"] for row in reassigned_rows[:8]],
        "outgroup_accessions_sample": [row["accession"] for row in outgroup_rows[:8]],
        "outgroup_usage_available": bool(outgroup_profile.get("complete_codons")) if outgroup_profile else False,
        "outgroup_availability": {
            "family_codons": [rna(codon) for codon in family],
            "relative_usage_median": {
                rna(codon): value for codon, value in dict(outgroup_profile.get("availability", {})).items()
            },
            "rscu_median": {rna(codon): value for codon, value in dict(outgroup_profile.get("rscu", {})).items()},
            "rank_tercile": {rna(codon): value for codon, value in dict(outgroup_profile.get("rank_tercile", {})).items()},
            "n_rows_with_complete_family_usage": outgroup_profile.get("n_rows_with_complete_family_usage", 0),
        },
        "genomic_gc": {
            "reassigned_median": round_float(median(reassigned_gc_values)),
            "outgroup_median": round_float(median(outgroup_gc_values)),
        },
        "transition_support_size": int(ALT.null_support_size(standard, matrix)),
        "matched_support": support,
        "candidate_count": len(candidates),
        "usable": usable,
        "reason": None if usable else "missing reassigned codon, outgroup usage, or nonempty matched null support",
    }


def build_panel(force_refresh: bool = False) -> dict[str, object]:
    if CACHE_PATH.exists() and not force_refresh:
        return json.loads(CACHE_PATH.read_text(encoding="utf-8"))
    codons, standard = standard_code_from_gc_prt()
    events = [event_panel(spec, codons, standard) for spec in EVENT_SPECS]
    usable_events = [event for event in events if event.get("usable")]
    cluster_keys = sorted({str(event["cluster_key"]) for event in usable_events})
    degenerate = [event["event_id"] for event in usable_events if not event["matched_support"]["nondegenerate"]]  # type: ignore[index]
    support_gate = len(cluster_keys) >= 3 and not degenerate
    fetchable = len(usable_events) == len(EVENT_SPECS) and bool(usable_events)
    panel = {
        "status": "ok" if fetchable and support_gate else "needs_external",
        "fetched_at": now_iso(),
        "source_repo": "kshulgina/ShulginaEddy_21_genetic_codes",
        "fetchable": fetchable,
        "codon_order": codons,
        "standard_labels": standard,
        "events": events,
        "n_events": len(events),
        "n_usable_events": len(usable_events),
        "independent_cluster_count": len(cluster_keys),
        "independent_clusters": cluster_keys,
        "support_gate": {
            "passed": support_gate,
            "requires_independent_clusters_at_least": 3,
            "requires_each_matched_stratum_nondegenerate": True,
            "degenerate_events": degenerate,
            "low_support_events": [
                event["event_id"]
                for event in usable_events
                if event["matched_support"]["low_support"]  # type: ignore[index]
            ],
        },
    }
    if not fetchable:
        panel["reason"] = "not all five event xlsx panels yielded reassigned codons and outgroup usage"
    elif not support_gate:
        panel["reason"] = "support audit failed: independent clusters <3 or matched strata degenerate"
    else:
        panel["reason"] = None
    CACHE_PATH.parent.mkdir(parents=True, exist_ok=True)
    CACHE_PATH.write_text(json.dumps(panel, ensure_ascii=True, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return panel


def main() -> None:
    try:
        panel = build_panel(force_refresh=True)
    except Exception as exc:
        emit("needs_external", reason=f"{type(exc).__name__}:{exc}")
    compact_events = [
        {
            "event_id": event["event_id"],
            "status": event["status"],
            "reassigned_codons": event.get("reassigned_codons"),
            "n_reassigned_rows": event.get("n_reassigned_rows"),
            "n_outgroup_rows": event.get("n_outgroup_rows"),
            "outgroup_usage_available": event.get("outgroup_usage_available"),
            "cluster_key": event.get("cluster_key"),
            "transition_support_size": event.get("transition_support_size"),
            "matched_support": event.get("matched_support", {}).get("matched_support") if isinstance(event.get("matched_support"), dict) else None,
            "matched_rule": event.get("matched_support", {}).get("rule") if isinstance(event.get("matched_support"), dict) else None,
            "nondegenerate": event.get("matched_support", {}).get("nondegenerate") if isinstance(event.get("matched_support"), dict) else None,
            "low_support": event.get("matched_support", {}).get("low_support") if isinstance(event.get("matched_support"), dict) else None,
        }
        for event in panel.get("events", [])
    ]
    if panel.get("status") != "ok":
        emit(
            "needs_external",
            reason=str(panel.get("reason") or "support audit failed"),
            probe={
                "n_usable_events": panel.get("n_usable_events"),
                "independent_cluster_count": panel.get("independent_cluster_count"),
                "support_gate": panel.get("support_gate"),
                "events": compact_events,
                "cache_path": str(CACHE_PATH),
            },
        )
    emit(
        "ok",
        n_usable_events=panel.get("n_usable_events"),
        independent_cluster_count=panel.get("independent_cluster_count"),
        support_gate=panel.get("support_gate"),
        events=compact_events,
        cache_path=str(CACHE_PATH),
    )


if __name__ == "__main__":
    main()
