#!/usr/bin/env python3
"""Cross-branch concordance and anti-numerology triage for the bridge.

The bridge reads live branch surfaces as intake only. This script does not
certify any Window6<->biology result; it builds a deterministic ledger that
shows duplicate programs, homeless math stubs, and any item that would need
separate derivation work before reopening.
"""

from __future__ import annotations

import ast
import fnmatch
import hashlib
import json
import re
import subprocess
import sys
from collections import Counter, defaultdict
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[2]
OUT_DIR = REPO_ROOT / "papers" / "window_codon_bridge"
OUT_JSON = OUT_DIR / "cross_branch_concordance.json"
OUT_MD = OUT_DIR / "cross_branch_concordance.md"

FIB_BRANCH = "origin/feat/fibonacci_reality-deepening"
BIO_BRANCH = "origin/feat/bio-reality-deepening"

FIB_BSTAR_PATTERN = "tools/fibonacci_reality/experiments/run_b_star_q6_*.py"
FIB_TRACK_A_PATTERN = "tools/fibonacci_reality/experiments/run_track_a_*.py"
FIB_NAMECERT_PATTERN = "papers/fibonacci_reality/parts/namecerts/*.tex"
BIO_CLAIMS = "tools/bio_reality/registries/claims.json"
BIO_EXPERIMENTS = "tools/bio_reality/registries/experiments.json"

TOKEN_DROP = {
    "run",
    "b",
    "star",
    "bstar",
    "b_star",
    "q6",
    "bq6",
    "powered",
    "modeled",
    "tai",
    "validation",
    "validate",
    "claim",
    "h3",
    "cross",
    "layer",
    "relation",
    "codon",
    "usage",
    "topology",
    "translation",
    "survival",
    "window",
}

ORGANISM_TOKENS = {
    "human",
    "yeast",
    "ecoli",
    "e",
    "coli",
    "saccharomyces",
    "cerevisiae",
    "danio",
    "fungi",
    "crossdomain",
    "organism",
    "organisms",
    "species",
    "tissue",
    "condition",
}

PARAM_TOKENS = {
    "human",
    "yeast",
    "ecoli",
    "crossdomain",
    "tissue",
    "condition",
    "measured",
    "modeled",
    "dynamic",
    "ortholog",
    "ramp",
    "positional",
    "prime",
    "editor",
    "chen2017",
    "chen2026",
    "nieuwkoop",
    "yang",
    "shen",
}


def run_git(args: list[str]) -> str:
    proc = subprocess.run(
        ["git", "-C", str(REPO_ROOT), *args],
        capture_output=True,
        text=True,
    )
    if proc.returncode != 0:
        detail = (proc.stderr or proc.stdout).strip()
        raise RuntimeError(f"git {' '.join(args)} failed: {detail}")
    return proc.stdout


def glob_prefix(pattern: str) -> str:
    positions = [pos for token in "*?[" if (pos := pattern.find(token)) >= 0]
    if not positions:
        return pattern
    prefix = pattern[: min(positions)]
    return prefix.rsplit("/", 1)[0] if "/" in prefix else "."


def ls_matching(branch: str, pattern: str) -> list[str]:
    prefix = glob_prefix(pattern)
    out = run_git(["ls-tree", "-r", "--name-only", branch, "--", prefix])
    return sorted(path for path in out.splitlines() if path and fnmatch.fnmatch(path, pattern))


def git_show(branch: str, path: str) -> str:
    return run_git(["show", f"{branch}:{path}"])


def sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def literal_string_assign(text: str, name: str) -> str | None:
    pattern = re.compile(rf"^\s*{re.escape(name)}\s*=\s*([\"'])(.*?)\1\s*$", re.M)
    match = pattern.search(text)
    return match.group(2) if match else None


def module_docstring(text: str) -> str:
    try:
        tree = ast.parse(text)
    except SyntaxError:
        return ""
    doc = ast.get_docstring(tree) or ""
    return " ".join(doc.split())


def head(text: str, limit: int = 120) -> str:
    value = " ".join(str(text or "").split())
    return value[:limit]


def normalize_tokens(value: str, drop_organisms: bool = True) -> list[str]:
    value = value.replace("B*_Q6", "b_star_q6").replace("B_window", "b_star_window")
    value = re.sub(r"([a-z])([A-Z])", r"\1_\2", value)
    raw = re.split(r"[^A-Za-z0-9]+", value.lower())
    tokens: list[str] = []
    for token in raw:
        if not token or token in TOKEN_DROP:
            continue
        if drop_organisms and token in ORGANISM_TOKENS:
            continue
        tokens.append(token)
    return tokens


def topic_key(*values: str) -> str:
    tokens: list[str] = []
    for value in values:
        tokens.extend(normalize_tokens(value))
    deduped = sorted(set(tokens))
    return "_".join(deduped) if deduped else "unspecified"


def experiment_topic_key(experiment_id: str, claim_id: str = "") -> str:
    primary = topic_key(experiment_id)
    if primary != "unspecified":
        return primary
    return topic_key(claim_id)


def param_key(*values: str) -> str:
    tokens: list[str] = []
    for value in values:
        for token in normalize_tokens(value, drop_organisms=False):
            if token in PARAM_TOKENS or re.search(r"\d", token):
                tokens.append(token)
    return "_".join(sorted(set(tokens)))


def contains_any(text: str, patterns: list[str]) -> bool:
    low = text.lower()
    return any(pattern in low for pattern in patterns)


def gate_columns(text: str) -> dict[str, bool]:
    low = text.lower()
    carrier = (
        ("window6" in low or "window six" in low or "forced-window" in low)
        and ("codon" in low or "genetic code" in low)
        and contains_any(low, ["carrier", "map", "intertwiner", "functor", "embedding", "projection"])
    )
    necessity = contains_any(low, ["necessity", "necessary", "forced", "forcing", "must", "unique", "impossible", "obstruction"])
    matched_null = contains_any(low, ["matched null", "matched-q", "matched_q", "matched-bin", "matched bin", "permutation null", "synonymous-recoding", "null95"])
    phenotype = contains_any(
        low,
        [
            "phenotype",
            "fitness",
            "essentiality",
            "abundance",
            "protein",
            "turnover",
            "half-life",
            "localization",
            "structural",
            "growth",
            "mrna",
        ],
    )
    return {
        "carrier_map_present": carrier,
        "necessity_present": necessity,
        "matched_null_present": matched_null,
        "phenotype_present": phenotype,
    }


def bridge_class(kind: str, gates: dict[str, bool], empty_stub: bool, relation: str) -> str:
    if kind == "track_a":
        return "bio_only"
    if kind == "namecert" and empty_stub:
        return "math_stub"
    if gates["carrier_map_present"] and gates["necessity_present"] and gates["matched_null_present"]:
        return "reopening_candidate"
    if relation in {"duplicate", "path_fork", "param_divergence"}:
        return "duplicate_bio_program"
    if kind == "bio_bstarq6":
        return "bio_only"
    if kind == "fib_bstarq6":
        return "duplicate_bio_program" if relation != "fibonacci_only" else "bio_only"
    return "needs_derivation"


def is_bstar_item(item: dict[str, Any]) -> bool:
    blob = json.dumps(item, ensure_ascii=False).lower()
    return "b*_q6" in blob or "b_star_q6" in blob or "b_star_window" in blob


def extract_fibonacci_scripts() -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for path in ls_matching(FIB_BRANCH, FIB_BSTAR_PATTERN):
        text = git_show(FIB_BRANCH, path)
        experiment_id = literal_string_assign(text, "EXPERIMENT_ID") or Path(path).stem.removeprefix("run_")
        claim_id = literal_string_assign(text, "CLAIM_ID") or ""
        doc = module_docstring(text)
        rows.append(
            {
                "source": "fibonacci",
                "kind": "fib_bstarq6",
                "path": path,
                "experiment_id": experiment_id,
                "claim_id": claim_id,
                "docstring": doc,
                "statement_head": head(doc),
                "topic_key": experiment_topic_key(experiment_id, claim_id),
                "param_key": param_key(experiment_id, claim_id, doc),
                "content_sha256": sha256_text(text),
                "raw_text_for_gates": "\n".join([experiment_id, claim_id, doc, text[:5000]]),
            }
        )
    return sorted(rows, key=lambda row: row["path"])


def extract_track_a_scripts() -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for path in ls_matching(FIB_BRANCH, FIB_TRACK_A_PATTERN):
        text = git_show(FIB_BRANCH, path)
        experiment_id = literal_string_assign(text, "EXPERIMENT_ID") or Path(path).stem.removeprefix("run_")
        claim_id = literal_string_assign(text, "CLAIM_ID") or ""
        doc = module_docstring(text)
        rows.append(
            {
                "source": "fibonacci",
                "kind": "track_a",
                "path": path,
                "experiment_id": experiment_id,
                "claim_id": claim_id,
                "docstring": doc,
                "statement_head": head(doc),
                "topic_key": experiment_topic_key(experiment_id, claim_id),
                "param_key": param_key(experiment_id, claim_id, doc),
                "content_sha256": sha256_text(text),
                "raw_text_for_gates": "\n".join([experiment_id, claim_id, doc, text[:5000]]),
            }
        )
    return sorted(rows, key=lambda row: row["path"])


def namecert_claim_id(text: str, path: str) -> str:
    match = re.search(r"\\subsection\{NameCert:\s*([^}]+)\}", text)
    if match:
        return match.group(1).strip()
    return Path(path).stem


def is_empty_author_stub(text: str) -> bool:
    low = text.lower()
    return (
        "intentionally empty" in low
        or "no self-contained mathematical packet has passed" in low
        or "carrier is required before" in low
        or "no exact count has been certified" in low
    )


def has_real_carrier_or_count(text: str) -> bool:
    low = text.lower()
    if is_empty_author_stub(text):
        return False
    return (
        "\\paragraph{carrier}" in low
        and not contains_any(low, ["carrier is required before", "intentionally empty"])
        and contains_any(low, ["\\paragraph{counts", "exact count", "identity", "witness"])
    )


def extract_namecerts() -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for path in ls_matching(FIB_BRANCH, FIB_NAMECERT_PATTERN):
        text = git_show(FIB_BRANCH, path)
        claim_id = namecert_claim_id(text, path)
        empty = is_empty_author_stub(text)
        real = has_real_carrier_or_count(text)
        kind = "track_a" if "track_a" in Path(path).stem else "namecert"
        rows.append(
            {
                "source": "fibonacci",
                "kind": kind,
                "path": path,
                "experiment_id": "",
                "claim_id": claim_id,
                "statement_head": head(text),
                "topic_key": topic_key(claim_id, Path(path).stem),
                "param_key": param_key(claim_id, Path(path).stem),
                "empty_author_stub": empty,
                "has_real_carrier_or_count": real,
                "content_sha256": sha256_text(text),
                "raw_text_for_gates": text[:5000],
            }
        )
    return sorted(rows, key=lambda row: row["path"])


def extract_bio_bstarq6() -> list[dict[str, Any]]:
    claims = json.loads(git_show(BIO_BRANCH, BIO_CLAIMS)).get("claims", [])
    experiments = json.loads(git_show(BIO_BRANCH, BIO_EXPERIMENTS)).get("experiments", [])
    exp_by_claim = {str(item.get("claim_id", "")): item for item in experiments if item.get("claim_id")}
    exp_by_id = {str(item.get("experiment_id", "")): item for item in experiments if item.get("experiment_id")}
    rows: list[dict[str, Any]] = []
    for claim in claims:
        if not is_bstar_item(claim):
            continue
        claim_id = str(claim.get("claim_id", ""))
        experiment_id = str(claim.get("experiment_id", ""))
        exp = exp_by_claim.get(claim_id) or exp_by_id.get(experiment_id) or {}
        statement = str(claim.get("statement") or exp.get("statement") or "")
        script_path = str(exp.get("script_path") or "")
        script_text = ""
        script_sha = ""
        if script_path:
            try:
                script_text = git_show(BIO_BRANCH, script_path)
                script_sha = sha256_text(script_text)
            except RuntimeError:
                script_text = ""
                script_sha = ""
        raw_for_gates = "\n".join(
            [
                claim_id,
                experiment_id,
                statement,
                str(exp.get("acceptance") or ""),
                str(exp.get("required_data") or ""),
                script_text[:5000],
            ]
        )
        rows.append(
            {
                "source": "bio",
                "kind": "bio_bstarq6",
                "path": script_path,
                "experiment_id": experiment_id,
                "claim_id": claim_id,
                "status": str(claim.get("status") or ""),
                "statement_head": head(statement),
                "topic_key": experiment_topic_key(experiment_id, claim_id),
                "param_key": param_key(experiment_id, claim_id, statement),
                "content_sha256": script_sha,
                "raw_text_for_gates": raw_for_gates,
            }
        )
    return sorted(rows, key=lambda row: (row["experiment_id"], row["claim_id"]))


def relation_for(fib: dict[str, Any], bio_matches: list[dict[str, Any]]) -> str:
    if not bio_matches:
        return "fibonacci_only"
    fib_params = str(fib.get("param_key", ""))
    bio_params = {str(bio.get("param_key", "")) for bio in bio_matches}
    if len(bio_matches) > 1 or any(param != fib_params for param in bio_params):
        return "param_divergence"
    fib_sha = str(fib.get("content_sha256", ""))
    for bio in bio_matches:
        if fib_sha and fib_sha == str(bio.get("content_sha256", "")) and fib.get("path") != bio.get("path"):
            return "path_fork"
    return "duplicate"


def public_row(row: dict[str, Any], relation: str, matches: list[dict[str, Any]]) -> dict[str, Any]:
    gates = gate_columns(str(row.get("raw_text_for_gates", "")))
    empty = bool(row.get("empty_author_stub", False))
    bclass = bridge_class(str(row.get("kind", "")), gates, empty, relation)
    out = {
        "source": row.get("source", ""),
        "kind": row.get("kind", ""),
        "path": row.get("path", ""),
        "experiment_id": row.get("experiment_id", ""),
        "claim_id": row.get("claim_id", ""),
        "status": row.get("status", ""),
        "statement_head": row.get("statement_head", ""),
        "topic_key": row.get("topic_key", ""),
        "param_key": row.get("param_key", ""),
        "crosswalk_relation": relation,
        "matched_items": [
            {
                "source": match.get("source", ""),
                "path": match.get("path", ""),
                "experiment_id": match.get("experiment_id", ""),
                "claim_id": match.get("claim_id", ""),
            }
            for match in matches
        ],
        "carrier_map_present": gates["carrier_map_present"],
        "necessity_present": gates["necessity_present"],
        "matched_null_present": gates["matched_null_present"],
        "phenotype_present": gates["phenotype_present"],
        "bridge_class": bclass,
        "certified_from_intake": False,
    }
    if "empty_author_stub" in row:
        out["empty_author_stub"] = row["empty_author_stub"]
    if "has_real_carrier_or_count" in row:
        out["has_real_carrier_or_count"] = row["has_real_carrier_or_count"]
    if "content_sha256" in row:
        out["content_sha256"] = row["content_sha256"]
    if "docstring" in row:
        out["docstring"] = row["docstring"]
    return out


def build_concordance() -> dict[str, Any]:
    fib_bstar = extract_fibonacci_scripts()
    fib_track = extract_track_a_scripts()
    namecerts = extract_namecerts()
    bio_bstar = extract_bio_bstarq6()

    bio_by_topic: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for row in bio_bstar:
        bio_by_topic[str(row["topic_key"])].append(row)

    fib_by_topic: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for row in fib_bstar:
        fib_by_topic[str(row["topic_key"])].append(row)

    rows: list[dict[str, Any]] = []
    used_bio: set[tuple[str, str]] = set()

    for fib in fib_bstar:
        matches = bio_by_topic.get(str(fib["topic_key"]), [])
        relation = relation_for(fib, matches)
        for bio in matches:
            used_bio.add((str(bio.get("experiment_id", "")), str(bio.get("claim_id", ""))))
        rows.append(public_row(fib, relation, matches))

    for bio in bio_bstar:
        identity = (str(bio.get("experiment_id", "")), str(bio.get("claim_id", "")))
        if identity in used_bio:
            continue
        matches = fib_by_topic.get(str(bio["topic_key"]), [])
        relation = "bio_only" if not matches else "param_divergence"
        rows.append(public_row(bio, relation, matches))

    for row in fib_track:
        rows.append(public_row(row, "track_a_homeless", []))

    for row in namecerts:
        relation = "track_a_homeless" if row["kind"] == "track_a" else "namecert_watchlist"
        rows.append(public_row(row, relation, []))

    rows = sorted(
        rows,
        key=lambda row: (
            str(row["bridge_class"]),
            str(row["source"]),
            str(row["kind"]),
            str(row["topic_key"]),
            str(row["path"]),
            str(row["claim_id"]),
        ),
    )

    relation_counts = Counter(str(row["crosswalk_relation"]) for row in rows)
    class_counts = Counter(str(row["bridge_class"]) for row in rows)
    duplicate_count = sum(relation_counts[key] for key in ("duplicate", "path_fork", "param_divergence"))
    homeless = [
        row
        for row in rows
        if row["bridge_class"] in {"bio_only", "math_stub", "needs_derivation"}
        and row["crosswalk_relation"] in {"track_a_homeless", "namecert_watchlist", "fibonacci_only", "bio_only"}
    ]
    reopening = [row for row in rows if row["bridge_class"] == "reopening_candidate"]

    return {
        "schema": "window-codon-bridge-cross-branch-concordance",
        "branches": {
            "fibonacci": FIB_BRANCH,
            "bio": BIO_BRANCH,
        },
        "disclaimer": "Intake ledger only; no Window6<->biology result is certified from this concordance.",
        "counts": {
            "n_fibonacci_bstarq6": len(fib_bstar),
            "n_bio_bstarq6": len(bio_bstar),
            "n_track_a_scripts": len(fib_track),
            "n_namecerts": len(namecerts),
            "n_rows": len(rows),
            "n_duplicate": duplicate_count,
            "n_reopening_candidate": len(reopening),
            "n_homeless": len(homeless),
            "by_bridge_class": dict(sorted(class_counts.items())),
            "by_crosswalk_relation": dict(sorted(relation_counts.items())),
        },
        "rows": rows,
    }


def md_table(rows: list[dict[str, Any]], columns: list[str]) -> list[str]:
    out = ["| " + " | ".join(columns) + " |", "| " + " | ".join(["---"] * len(columns)) + " |"]
    for row in rows:
        vals = []
        for col in columns:
            value = row.get(col, "")
            if isinstance(value, bool):
                text = "yes" if value else "no"
            else:
                text = str(value)
            text = text.replace("|", "\\|").replace("\n", " ")
            vals.append(text[:180])
        out.append("| " + " | ".join(vals) + " |")
    return out


def write_markdown(payload: dict[str, Any]) -> None:
    counts = payload["counts"]
    rows = payload["rows"]
    reopening = [row for row in rows if row["bridge_class"] == "reopening_candidate"]
    homeless = [
        row
        for row in rows
        if row["bridge_class"] in {"bio_only", "math_stub", "needs_derivation"}
        and row["crosswalk_relation"] in {"track_a_homeless", "namecert_watchlist", "fibonacci_only", "bio_only"}
    ]
    dup_rows = [row for row in rows if row["crosswalk_relation"] in {"duplicate", "path_fork", "param_divergence"}]

    lines = [
        "# Cross-Branch Concordance",
        "",
        "This is a bridge-owned triage ledger for live branch intake. It does not certify any Window6-to-biology result.",
        "",
        "## Counts by bridge_class",
        "",
    ]
    for key, value in counts["by_bridge_class"].items():
        lines.append(f"- {key}: {value}")
    lines.extend(
        [
            "",
            "## B*_Q6 crosswalk summary",
            "",
            f"- fibonacci B*_Q6 scripts: {counts['n_fibonacci_bstarq6']}",
            f"- bio B*_Q6 registered claims: {counts['n_bio_bstarq6']}",
            f"- duplicate/path-fork/parameter-divergence rows: {counts['n_duplicate']}",
        ]
    )
    for key, value in counts["by_crosswalk_relation"].items():
        lines.append(f"- {key}: {value}")
    lines.extend(["", "### Duplicate/fork/divergence rows", ""])
    if dup_rows:
        lines.extend(
            md_table(
                dup_rows,
                ["source", "kind", "crosswalk_relation", "experiment_id", "claim_id", "bridge_class", "carrier_map_present", "necessity_present", "matched_null_present"],
            )
        )
    else:
        lines.append("No duplicate/path-fork/parameter-divergence rows were detected.")

    lines.extend(["", "## Reopening candidates", ""])
    if reopening:
        lines.extend(md_table(reopening, ["source", "kind", "experiment_id", "claim_id", "statement_head"]))
    else:
        lines.append("None. No intake item passed carrier-map, necessity, and matched-null gates together.")

    lines.extend(["", "## Homeless items", ""])
    if homeless:
        lines.extend(
            md_table(
                homeless,
                ["source", "kind", "crosswalk_relation", "path", "claim_id", "bridge_class", "statement_head"],
            )
        )
    else:
        lines.append("None.")

    lines.extend(
        [
            "",
            "## Gate policy",
            "",
            "A row can only become `reopening_candidate` when `carrier_map_present`, `necessity_present`, and `matched_null_present` are all true. Track-A intake remains `bio_only`; empty number-theory namecerts remain `math_stub`; duplicated B*_Q6 work remains `duplicate_bio_program` unless the full anti-numerology gate is met.",
            "",
        ]
    )
    OUT_MD.write_text("\n".join(lines), encoding="utf-8")


def main() -> int:
    payload = build_concordance()
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    OUT_JSON.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    write_markdown(payload)
    counts = payload["counts"]
    summary = {
        "status": "generated",
        "n_fibonacci_bstarq6": counts["n_fibonacci_bstarq6"],
        "n_bio_bstarq6": counts["n_bio_bstarq6"],
        "n_duplicate": counts["n_duplicate"],
        "n_reopening_candidate": counts["n_reopening_candidate"],
        "n_homeless": counts["n_homeless"],
    }
    print(json.dumps(summary, sort_keys=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
