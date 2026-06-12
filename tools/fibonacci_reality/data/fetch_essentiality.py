#!/usr/bin/env python3
import datetime as _dt
import gzip
import hashlib
import json
import re
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path
from urllib.error import HTTPError, URLError
from urllib.parse import quote
from urllib.request import Request, urlopen


DATA_DIR = Path(__file__).resolve().parent
USER_AGENT = "FibonacciReality-essentiality-fetch/1.0"
PEC_URL = "https://shigen.nig.ac.jp/ecoli/pec/download/files/PECData.dat"
SGD_URL_TEMPLATE = "https://www.yeastgenome.org/backend/locus/{gene_key}/phenotype_details"
SGD_PHENOTYPE_URLS = {
    "inviable": "https://www.yeastgenome.org/backend/phenotype/inviable/locus_details",
    "viable": "https://www.yeastgenome.org/backend/phenotype/viable/locus_details",
}
CANNOT_CLAIM = [
    "essentiality 是 lab-condition knockout phenotype, 非 codon 因果; 与表达强混杂"
]
DERIVATION_BOUNDARY = "not_bedc_kernel_content"


def utc_now():
    return _dt.datetime.now(_dt.timezone.utc).replace(microsecond=0).isoformat()


def fetch_bytes(url, timeout=60):
    request = Request(url, headers={"User-Agent": USER_AGENT})
    with urlopen(request, timeout=timeout) as response:
        raw = response.read()
        encoding = response.headers.get("content-encoding", "").lower()
        if encoding == "gzip":
            return gzip.decompress(raw)
        return raw


def sha256_hex(raw):
    return hashlib.sha256(raw).hexdigest()


def load_joined(org_slug):
    path = DATA_DIR / f"cds_codon_abundance_{org_slug}.json"
    with path.open() as handle:
        payload = json.load(handle)
    return payload, payload.get("joined", [])


def write_json(path, payload):
    with path.open("w") as handle:
        json.dump(payload, handle, indent=2, sort_keys=True)
        handle.write("\n")


def ratio(numer, denom):
    if denom == 0:
        return 0.0
    return round(numer / denom, 6)


def ecoli_gene_key(row):
    protein_id = row.get("protein_id", "")
    if "." not in protein_id:
        return None
    key = protein_id.split(".", 1)[1]
    if re.fullmatch(r"b\d{4}", key):
        return key
    return None


def parse_pec(raw):
    text = raw.decode("cp932", "replace")
    labels = {}
    for line in text.splitlines():
        if not line.strip() or line.startswith("Orf ID\t"):
            continue
        fields = line.split("\t")
        if len(fields) < 10:
            continue
        feature_type = fields[1].strip()
        aliases = [part.strip() for part in fields[3].split(",") if part.strip()]
        class_code = fields[9].strip()
        if feature_type != "1":
            continue
        essential = None
        if class_code == "1":
            essential = 1
        elif class_code == "2":
            essential = 0
        else:
            continue
        for alias in aliases:
            if re.fullmatch(r"b\d{4}", alias):
                labels[alias] = essential
    return labels


def build_ecoli():
    org_slug = "escherichia_coli_k12_mg1655"
    source_payload = fetch_bytes(PEC_URL)
    source_sha = sha256_hex(source_payload)
    source_labels = parse_pec(source_payload)
    org_payload, joined = load_joined(org_slug)
    genes = []
    for row in joined:
        protein_id = row.get("protein_id")
        key = ecoli_gene_key(row)
        if not protein_id or not key or key not in source_labels:
            continue
        genes.append(
            {
                "essential": source_labels[key],
                "gene_key": key,
                "protein_id": protein_id,
            }
        )
    return make_output(
        organism=org_slug,
        ncbi_taxid=str(org_payload.get("ncbi_taxid")),
        source_kind="PEC whole-gene deletion classification table",
        source_url=PEC_URL,
        payload_sha256=source_sha,
        id_mapping_method="Exact b-number match: joined[].protein_id suffix 511145.bNNNN to PECData.dat Alternative name bNNNN; PEC class 1=essential, class 2=non-essential, class 3 skipped.",
        genes=genes,
        join_denominator=len(joined),
    )


def yeast_gene_key(row):
    protein_id = row.get("protein_id", "")
    if "." not in protein_id:
        return None
    key = protein_id.split(".", 1)[1]
    if re.fullmatch(r"Y[A-P][LR]\d{3}[CW](?:-[A-Z])?", key):
        return key
    return None


def classify_sgd_records(records):
    has_inviable = False
    has_viable = False
    for record in records:
        mutant_type = str(record.get("mutant_type") or "").strip().lower()
        if mutant_type != "null":
            continue
        phenotype = record.get("phenotype") or {}
        display = str(phenotype.get("display_name") or "").strip().lower()
        link = str(phenotype.get("link") or "").strip().lower()
        if display == "inviable" or link.endswith("/phenotype/inviable"):
            has_inviable = True
        elif display == "viable" or link.endswith("/phenotype/viable"):
            has_viable = True
    if has_inviable:
        return 1
    if has_viable:
        return 0
    return None


def fetch_one_sgd_phenotype(key):
    url = SGD_URL_TEMPLATE.format(gene_key=quote(key, safe=""))
    raw = fetch_bytes(url, timeout=45)
    records = json.loads(raw.decode("utf-8"))
    label = classify_sgd_records(records)
    return key, url, raw, label


def fetch_sgd_phenotypes(gene_keys):
    responses = {}
    labels = {}
    failures = []
    with ThreadPoolExecutor(max_workers=24) as executor:
        future_to_key = {executor.submit(fetch_one_sgd_phenotype, key): key for key in gene_keys}
        for index, future in enumerate(as_completed(future_to_key), start=1):
            key = future_to_key[future]
            try:
                result_key, url, raw, label = future.result()
                responses[result_key] = (url, raw)
                if label is not None:
                    labels[result_key] = label
            except (HTTPError, URLError, TimeoutError, json.JSONDecodeError) as exc:
                failures.append({"gene_key": key, "error": type(exc).__name__, "message": str(exc)})
            if index % 500 == 0:
                time.sleep(0.2)
    raw_parts = []
    for key in gene_keys:
        if key not in responses:
            continue
        url, raw = responses[key]
        raw_parts.append(
            b"\n---SGD-PHENOTYPE-RESPONSE "
            + key.encode("ascii")
            + b" "
            + url.encode("ascii")
            + b"---\n"
            + raw
        )
    return b"".join(raw_parts), labels, failures


def parse_sgd_locus_details(raw, essential):
    records = json.loads(raw.decode("utf-8"))
    labels = {}
    for record in records:
        mutant_type = str(record.get("mutant_type") or "").strip().lower()
        if mutant_type != "null":
            continue
        locus = record.get("locus") or {}
        key = str(locus.get("format_name") or "").strip()
        if re.fullmatch(r"Y[A-P][LR]\d{3}[CW](?:-[A-Z])?", key):
            labels[key] = essential
    return labels


def build_yeast():
    org_slug = "saccharomyces_cerevisiae"
    org_payload, joined = load_joined(org_slug)
    rows_by_key = {}
    for row in joined:
        key = yeast_gene_key(row)
        if key:
            rows_by_key[key] = row
    raw_parts = []
    source_labels = {}
    for label_name in ("viable", "inviable"):
        url = SGD_PHENOTYPE_URLS[label_name]
        raw = fetch_bytes(url, timeout=90)
        raw_parts.append(
            b"\n---SGD-PHENOTYPE-LOCUS-DETAILS "
            + label_name.encode("ascii")
            + b" "
            + url.encode("ascii")
            + b"---\n"
            + raw
        )
        essential = 1 if label_name == "inviable" else 0
        source_labels.update(parse_sgd_locus_details(raw, essential))
    raw_payload = b"".join(raw_parts)
    genes = []
    for key in rows_by_key:
        row = rows_by_key[key]
        protein_id = row.get("protein_id")
        if protein_id and key in source_labels:
            genes.append(
                {
                    "essential": source_labels[key],
                    "gene_key": key,
                    "protein_id": protein_id,
                }
            )
    output = make_output(
        organism=org_slug,
        ncbi_taxid=str(org_payload.get("ncbi_taxid")),
        source_kind="SGD phenotype locus_details JSON",
        source_url="; ".join(SGD_PHENOTYPE_URLS.values()),
        payload_sha256=sha256_hex(raw_payload),
        id_mapping_method="Exact systematic ORF match: joined[].protein_id suffix 4932.Y... to SGD /backend/phenotype/{inviable,viable}/locus_details locus.format_name; null mutant phenotype inviable=essential, null mutant phenotype viable=non-essential, other records skipped; inviable overrides viable if both are present.",
        genes=genes,
        join_denominator=len(joined),
    )
    output["source_request_count"] = len(SGD_PHENOTYPE_URLS)
    output["source_fetch_failure_count"] = 0
    output["source_fetch_failures"] = []
    return output


def make_output(
    organism,
    ncbi_taxid,
    source_kind,
    source_url,
    payload_sha256,
    id_mapping_method,
    genes,
    join_denominator,
):
    n_essential = sum(1 for gene in genes if gene["essential"] == 1)
    n_nonessential = sum(1 for gene in genes if gene["essential"] == 0)
    return {
        "cannot_claim": CANNOT_CLAIM,
        "derivation_boundary": DERIVATION_BOUNDARY,
        "genes": sorted(genes, key=lambda item: item["protein_id"]),
        "id_mapping_method": id_mapping_method,
        "join_hit_rate": ratio(len(genes), join_denominator),
        "n_essential": n_essential,
        "n_genes_with_label": len(genes),
        "n_nonessential": n_nonessential,
        "ncbi_taxid": ncbi_taxid,
        "organism": organism,
        "payload_sha256": payload_sha256,
        "source_kind": source_kind,
        "source_url": source_url,
    }


def validate_output(payload):
    genes = payload["genes"]
    assert payload["n_genes_with_label"] == len(genes)
    assert payload["n_essential"] + payload["n_nonessential"] == payload["n_genes_with_label"]
    assert all(gene["essential"] in (0, 1) for gene in genes)
    assert len({gene["protein_id"] for gene in genes}) == len(genes)


def manifest(outputs):
    successes = []
    for payload in outputs:
        successes.append(
            {
                "file": f"gene_essentiality_{payload['organism']}.json",
                "join_hit_rate": payload["join_hit_rate"],
                "n_essential": payload["n_essential"],
                "n_genes_with_label": payload["n_genes_with_label"],
                "n_nonessential": payload["n_nonessential"],
                "ncbi_taxid": payload["ncbi_taxid"],
                "organism": payload["organism"],
                "payload_sha256": payload["payload_sha256"],
                "source_kind": payload["source_kind"],
                "source_url": payload["source_url"],
            }
        )
    return {
        "campaign": "gene_essentiality_function_phenotype_layer",
        "cannot_claim": CANNOT_CLAIM,
        "derivation_boundary": DERIVATION_BOUNDARY,
        "fetched_at": utc_now(),
        "fetched_by": "tools/fibonacci_reality/data/fetch_essentiality.py",
        "raw_payload_policy": "Only HTTP-fetched raw payloads are used. Each organism output records the sha256 of the fetched source payload used for labels; genes without explicit essential/non-essential evidence are skipped.",
        "schema_version": 1,
        "success_count": len(successes),
        "successes": successes,
    }


def main():
    outputs = []
    failures = []
    for builder in (build_ecoli, build_yeast):
        try:
            payload = builder()
            validate_output(payload)
            output_path = DATA_DIR / f"gene_essentiality_{payload['organism']}.json"
            write_json(output_path, payload)
            outputs.append(payload)
        except Exception as exc:
            failures.append(
                {
                    "builder": builder.__name__,
                    "error": type(exc).__name__,
                    "message": str(exc),
                }
            )
    manifest_payload = manifest(outputs)
    manifest_payload["failure_count"] = len(failures)
    manifest_payload["failures"] = failures
    write_json(DATA_DIR / "gene_essentiality_campaign_manifest.json", manifest_payload)
    for payload in outputs:
        print(
            payload["organism"],
            payload["n_genes_with_label"],
            payload["n_essential"],
            payload["n_nonessential"],
            payload["join_hit_rate"],
            payload["payload_sha256"],
        )
    if failures:
        print("failures", json.dumps(failures, sort_keys=True))


if __name__ == "__main__":
    main()
