#!/usr/bin/env python3
"""Fetch per-protein structural-order readouts from AlphaFold DB.

The readout is AlphaFold DB globalMetricValue, verified against the mean
per-residue pLDDT stored as CA B-factors in one fetched PDB sample. Proteins
without a real fetched AlphaFold API payload are skipped.
"""

from __future__ import annotations

import datetime as _dt
import gzip
import hashlib
import json
import pathlib
import re
import sys
import time
import urllib.error
import urllib.parse
import urllib.request


DATA_DIR = pathlib.Path(__file__).resolve().parent
USER_AGENT = "FibonacciReality-StructuralOrder/1.0"
ALPHAFOLD_API_BASE = "https://alphafold.ebi.ac.uk/api/prediction/"
UNIPROT_STREAM = "https://rest.uniprot.org/uniprotkb/stream"
RAW_PAYLOAD_SEPARATOR = b"\n--FibonacciReality-structural-order-payload-boundary--\n"

ORGANISMS = [
    {
        "organism": "saccharomyces_cerevisiae",
        "organism_label": "Saccharomyces cerevisiae S288C",
        "ncbi_taxid": "4932",
        "uniprot_proteome": "UP000002311",
        "uniprot_taxid": "559292",
        "joined_path": "cds_codon_abundance_saccharomyces_cerevisiae.json",
        "id_mapping_method": "STRING suffix systematic ORF name is matched to UniProtKB reviewed proteome gene names for UP000002311.",
    },
    {
        "organism": "escherichia_coli_k12_mg1655",
        "organism_label": "Escherichia coli K-12 substr. MG1655",
        "ncbi_taxid": "511145",
        "uniprot_proteome": "UP000000625",
        "uniprot_taxid": "83333",
        "joined_path": "cds_codon_abundance_escherichia_coli_k12_mg1655.json",
        "id_mapping_method": "STRING suffix b-number locus tag is matched to UniProtKB reviewed proteome gene names for UP000000625.",
    },
    {
        "organism": "homo_sapiens",
        "organism_label": "Homo sapiens",
        "ncbi_taxid": "9606",
        "uniprot_proteome": "UP000005640",
        "uniprot_taxid": "9606",
        "joined_path": "cds_codon_abundance_homo_sapiens.json",
        "id_mapping_method": "STRING suffix Ensembl protein identifier requires a UniProt cross-reference path and is not attempted by default in the narrow yeast/E. coli campaign.",
        "skip_by_default": True,
    },
]


def now_utc() -> str:
    return _dt.datetime.now(_dt.UTC).replace(microsecond=0).isoformat()


def fetch_bytes(url: str, timeout: int = 120) -> bytes:
    request = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
    with urllib.request.urlopen(request, timeout=timeout) as response:
        if int(response.status) != 200:
            raise urllib.error.URLError(f"HTTP {response.status}")
        return response.read()


def sha256_hex(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def decode_payload(raw: bytes) -> str:
    if raw[:2] == b"\x1f\x8b":
        return gzip.decompress(raw).decode("utf-8", "replace")
    return raw.decode("utf-8", "replace")


def uniprot_stream_url(entry: dict[str, str]) -> str:
    fields = "accession,id,gene_names,organism_id,reviewed"
    query = f"(proteome:{entry['uniprot_proteome']}) AND (reviewed:true)"
    return UNIPROT_STREAM + "?" + urllib.parse.urlencode(
        {
            "compressed": "true",
            "format": "tsv",
            "fields": fields,
            "query": query,
        }
    )


def suffix_of(protein_id: str) -> str:
    if "." in protein_id:
        return protein_id.split(".", 1)[1]
    return protein_id


def strip_version(identifier: str) -> str:
    if re.search(r"\.[0-9]+$", identifier):
        return identifier.rsplit(".", 1)[0]
    return identifier


def split_identifiers(text: str) -> list[str]:
    values: list[str] = []
    for token in re.split(r"[\s;,]+", text.strip()):
        token = token.strip()
        if not token:
            continue
        values.append(token)
        bare = strip_version(token)
        if bare != token:
            values.append(bare)
    return values


def parse_uniprot_tsv(text: str) -> tuple[dict[str, str], int]:
    lines = [line for line in text.splitlines() if line.strip()]
    if not lines:
        raise ValueError("empty UniProt TSV")
    header = lines[0].split("\t")
    index = {name: pos for pos, name in enumerate(header)}
    accession_by_identifier: dict[str, str] = {}
    row_count = 0
    for line in lines[1:]:
        parts = line.split("\t")
        if len(parts) < len(header):
            parts += [""] * (len(header) - len(parts))
        accession = parts[index["Entry"]].strip()
        if not accession:
            continue
        row_count += 1
        candidates = {accession, strip_version(accession)}
        for column in ("Entry Name", "Gene Names"):
            if column in index:
                candidates.update(split_identifiers(parts[index[column]]))
        for candidate in candidates:
            if candidate:
                accession_by_identifier.setdefault(candidate, accession)
    return accession_by_identifier, row_count


def load_joined_proteins(path: pathlib.Path) -> tuple[dict[str, object], list[str]]:
    with path.open(encoding="utf-8") as handle:
        payload = json.load(handle)
    proteins = [str(row.get("protein_id", "")) for row in payload.get("joined", [])]
    proteins = [protein for protein in proteins if protein]
    return payload, proteins


def parse_alphafold_prediction(raw: bytes) -> dict[str, object] | None:
    try:
        payload = json.loads(raw.decode("utf-8"))
    except json.JSONDecodeError:
        return None
    if not isinstance(payload, list) or not payload:
        return None
    best = payload[0]
    if not isinstance(best, dict):
        return None
    metric = best.get("globalMetricValue")
    try:
        value = float(metric)
    except (TypeError, ValueError):
        return None
    if value < 0 or value > 100:
        return None
    best["globalMetricValue"] = value
    return best


def fetch_alphafold_for_accessions(accessions: list[str]) -> tuple[dict[str, dict[str, object]], dict[str, str], bytes]:
    order_by_accession: dict[str, dict[str, object]] = {}
    failures: dict[str, str] = {}
    raw_chunks: list[bytes] = []
    for pos, accession in enumerate(accessions, start=1):
        url = ALPHAFOLD_API_BASE + urllib.parse.quote(accession)
        try:
            raw = fetch_bytes(url, timeout=90)
        except (urllib.error.URLError, TimeoutError, OSError) as exc:
            failures[accession] = f"fetch_failed:{exc}"
            continue
        raw_chunks.append(url.encode("utf-8") + b"\n" + raw)
        prediction = parse_alphafold_prediction(raw)
        if prediction is None:
            failures[accession] = "no_valid_globalMetricValue"
            continue
        order_by_accession[accession] = {
            "structural_order": float(prediction["globalMetricValue"]),
            "entry_id": prediction.get("entryId"),
            "tax_id": prediction.get("taxId"),
            "pdb_url": prediction.get("pdbUrl"),
            "cif_url": prediction.get("cifUrl"),
            "fraction_plddt_very_low": prediction.get("fractionPlddtVeryLow"),
            "fraction_plddt_low": prediction.get("fractionPlddtLow"),
            "fraction_plddt_confident": prediction.get("fractionPlddtConfident"),
            "fraction_plddt_very_high": prediction.get("fractionPlddtVeryHigh"),
        }
        if pos % 1000 == 0:
            print(f"fetched AlphaFold API payloads: {pos}/{len(accessions)}", file=sys.stderr)
        time.sleep(0.02)
    return order_by_accession, failures, RAW_PAYLOAD_SEPARATOR.join(raw_chunks)


def mean_ca_bfactor_from_pdb(raw: bytes) -> tuple[float, int]:
    values: list[float] = []
    for line in raw.decode("utf-8", "replace").splitlines():
        if not line.startswith("ATOM"):
            continue
        if line[12:16].strip() != "CA":
            continue
        try:
            values.append(float(line[60:66]))
        except ValueError:
            continue
    if not values:
        raise ValueError("no CA B-factor values parsed from PDB")
    return sum(values) / len(values), len(values)


def sample_verification(proteins: list[dict[str, object]], order_by_accession: dict[str, dict[str, object]]) -> dict[str, object] | None:
    for protein in proteins:
        accession = str(protein["uniprot"])
        info = order_by_accession.get(accession, {})
        pdb_url = info.get("pdb_url")
        if not isinstance(pdb_url, str) or not pdb_url:
            continue
        raw = fetch_bytes(pdb_url, timeout=120)
        mean_bfactor, n_ca = mean_ca_bfactor_from_pdb(raw)
        return {
            "protein_id": protein["protein_id"],
            "uniprot": accession,
            "alphafold_api_globalMetricValue": protein["structural_order"],
            "pdb_url": pdb_url,
            "pdb_payload_sha256": sha256_hex(raw),
            "pdb_ca_bfactor_mean": round(mean_bfactor, 4),
            "pdb_ca_residue_count": n_ca,
            "absolute_difference": round(abs(mean_bfactor - float(protein["structural_order"])), 4),
        }
    return None


def build_organism(entry: dict[str, str], include_human: bool) -> dict[str, object]:
    print(f"starting {entry['organism']}", file=sys.stderr)
    if entry.get("skip_by_default") and not include_human:
        return {
            "organism": entry["organism"],
            "ncbi_taxid": entry["ncbi_taxid"],
            "status": "skipped",
            "reason": "human target omitted by default to avoid thousands of per-accession AlphaFold API fetches; rerun with --include-human to attempt it",
        }

    joined_payload, protein_ids = load_joined_proteins(DATA_DIR / entry["joined_path"])
    uniprot_url = uniprot_stream_url(entry)
    uniprot_raw = fetch_bytes(uniprot_url)
    uniprot_text = decode_payload(uniprot_raw)
    identifier_to_accession, uniprot_rows = parse_uniprot_tsv(uniprot_text)

    mapped: dict[str, str] = {}
    unmapped: list[str] = []
    for protein_id in protein_ids:
        suffix = suffix_of(protein_id)
        accession = identifier_to_accession.get(suffix) or identifier_to_accession.get(strip_version(suffix))
        if accession:
            mapped[protein_id] = accession
        else:
            unmapped.append(protein_id)

    accessions = sorted(set(mapped.values()))
    print(
        f"{entry['organism']}: mapped {len(mapped)}/{len(protein_ids)} proteins to {len(accessions)} UniProt accessions",
        file=sys.stderr,
    )
    order_by_accession, af_failures, alphafold_raw = fetch_alphafold_for_accessions(accessions)
    proteins: list[dict[str, object]] = []
    skipped_no_order = 0
    for protein_id in protein_ids:
        accession = mapped.get(protein_id)
        if not accession:
            continue
        order = order_by_accession.get(accession)
        if not order:
            skipped_no_order += 1
            continue
        proteins.append(
            {
                "protein_id": protein_id,
                "uniprot": accession,
                "structural_order": round(float(order["structural_order"]), 4),
            }
        )

    hit_rate = len(proteins) / len(protein_ids) if protein_ids else 0.0
    raw_payload = (
        b"UNIPROT_URL\n"
        + uniprot_url.encode("utf-8")
        + b"\nUNIPROT_RAW\n"
        + uniprot_raw
        + b"\nALPHAFOLD_API_RAW\n"
        + alphafold_raw
    )
    sample = sample_verification(proteins, order_by_accession) if proteins else None
    source_url = f"{uniprot_url} ; {ALPHAFOLD_API_BASE}{{uniprot}}"
    output = {
        "organism": entry["organism"],
        "organism_label": entry["organism_label"],
        "ncbi_taxid": entry["ncbi_taxid"],
        "source_kind": "alphafold_db_global_metric_value",
        "source_url": source_url,
        "payload_sha256": sha256_hex(raw_payload),
        "readout_kind": "mean_plddt",
        "id_mapping_method": entry["id_mapping_method"],
        "n_joined_proteins": len(protein_ids),
        "n_uniprot_reviewed_proteome_rows": uniprot_rows,
        "n_joined_proteins_mapped_to_uniprot": len(mapped),
        "n_unique_uniprot_accessions_mapped": len(accessions),
        "n_unique_uniprot_accessions_with_alphafold_order": len(order_by_accession),
        "n_proteins_with_order": len(proteins),
        "join_hit_rate": round(hit_rate, 6),
        "payload_components": {
            "uniprot_tsv_url": uniprot_url,
            "uniprot_tsv_payload_sha256": sha256_hex(uniprot_raw),
            "alphafold_api_base_url": ALPHAFOLD_API_BASE + "{uniprot}",
            "alphafold_api_concatenated_payload_sha256": sha256_hex(alphafold_raw),
            "alphafold_api_payload_count": len(order_by_accession) + len(af_failures),
        },
        "failure_accounting": {
            "n_joined_proteins_unmapped_to_uniprot": len(unmapped),
            "n_mapped_proteins_without_alphafold_order": skipped_no_order,
            "n_unique_uniprot_accessions_without_alphafold_order": len(af_failures),
            "example_unmapped_protein_ids": unmapped[:20],
            "example_alphafold_failures": [
                {"uniprot": accession, "reason": reason}
                for accession, reason in list(sorted(af_failures.items()))[:20]
            ],
        },
        "sample_source_verification": sample,
        "cannot_claim": [
            "structure-based order proxy; 非 measured function/phenotype; mean pLDDT 是 predicted confidence 非实验有序度",
            "AlphaFold globalMetricValue is treated as mean pLDDT after one PDB CA B-factor mean cross-check; proteins without fetched AlphaFold API payload are skipped",
            "ID mapping uses UniProt reviewed reference proteome identifiers and may miss valid proteins absent from those gene-name/cross-reference fields",
        ],
        "derivation_boundary": "not_bedc_kernel_content",
        "fetched_at": now_utc(),
        "proteins": proteins,
    }
    out_path = DATA_DIR / f"structural_order_{entry['organism']}.json"
    with out_path.open("w", encoding="utf-8") as handle:
        json.dump(output, handle, ensure_ascii=False, indent=2, sort_keys=True)
        handle.write("\n")
    return {
        "organism": entry["organism"],
        "ncbi_taxid": entry["ncbi_taxid"],
        "status": "success" if proteins else "no_joined_order",
        "output_path": out_path.name,
        "source_kind": output["source_kind"],
        "readout_kind": output["readout_kind"],
        "n_proteins_with_order": len(proteins),
        "join_hit_rate": output["join_hit_rate"],
        "payload_sha256": output["payload_sha256"],
    }


def write_manifest(entries: list[dict[str, object]]) -> None:
    successes = [entry for entry in entries if entry.get("status") == "success"]
    manifest = {
        "campaign": "structural_order_layer",
        "source_priority": "AlphaFold DB globalMetricValue mean-pLDDT proxy",
        "fetched_at": now_utc(),
        "organisms": entries,
        "available_organisms": [entry["organism"] for entry in successes],
        "n_available_organisms": len(successes),
        "cannot_claim": [
            "structure-based order proxy; 非 measured function/phenotype; mean pLDDT 是 predicted confidence 非实验有序度",
            "coverage is reported as join_hit_rate and missing proteins are not imputed",
        ],
        "derivation_boundary": "not_bedc_kernel_content",
    }
    with (DATA_DIR / "structural_order_campaign_manifest.json").open("w", encoding="utf-8") as handle:
        json.dump(manifest, handle, ensure_ascii=False, indent=2, sort_keys=True)
        handle.write("\n")


def main(argv: list[str]) -> int:
    include_human = "--include-human" in argv
    results: list[dict[str, object]] = []
    for entry in ORGANISMS:
        try:
            result = build_organism(entry, include_human=include_human)
        except Exception as exc:
            result = {
                "organism": entry["organism"],
                "ncbi_taxid": entry["ncbi_taxid"],
                "status": "failed",
                "reason": str(exc),
            }
        print(json.dumps(result, ensure_ascii=False, sort_keys=True), file=sys.stderr)
        results.append(result)
    write_manifest(results)
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
