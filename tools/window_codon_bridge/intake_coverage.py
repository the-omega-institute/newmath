#!/usr/bin/env python3
"""Deterministic intake coverage report for the Window6<->codon bridge."""

from __future__ import annotations

import json
from collections import Counter
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[2]
SYNCED_DIR = REPO_ROOT / "tools" / "window_codon_bridge" / "synced"
OUT_DIR = REPO_ROOT / "papers" / "window_codon_bridge"
OUT_JSON = OUT_DIR / "intake_coverage.json"
OUT_MD = OUT_DIR / "intake_coverage.md"


SURFACES: dict[str, dict[str, str]] = {
    "bio": {
        "claims": "bio/registries/claims.json",
        "experiments": "bio/registries/experiments.json",
        "experiment_inventory": "bio/experiment_inventory.json",
        "namecert_inventory": "bio/namecert_inventory.json",
        "data_inventory": "bio/data_inventory.json",
    },
    "fibonacci": {
        "claims": "fibonacci/registries/claims.json",
        "experiments": "fibonacci/registries/experiments.json",
        "experiment_inventory": "fibonacci/experiment_inventory.json",
        "namecert_inventory": "fibonacci/namecert_inventory.json",
        "data_inventory": "fibonacci/data_inventory.json",
        "forced_window_structure_inventory": "fibonacci/forced_window_structure_inventory.json",
    },
}


def read_json(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def write_json(path: Path, obj: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(obj, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def inventory_paths(path: Path) -> list[str]:
    doc = read_json(path)
    paths = doc.get("paths", []) if isinstance(doc, dict) else []
    return sorted(str(item) for item in paths if isinstance(item, str))


def claims_from(path: Path) -> list[dict[str, Any]]:
    doc = read_json(path)
    claims = doc.get("claims", []) if isinstance(doc, dict) else []
    return [claim for claim in claims if isinstance(claim, dict)]


def experiments_from(path: Path) -> list[dict[str, Any]]:
    doc = read_json(path)
    experiments = doc.get("experiments", []) if isinstance(doc, dict) else []
    return [exp for exp in experiments if isinstance(exp, dict)]


def claim_id(claim: dict[str, Any]) -> str:
    return str(claim.get("claim_id") or "").strip()


def experiment_id(exp: dict[str, Any]) -> str:
    return str(exp.get("experiment_id") or "").strip()


def experiment_script_path(exp: dict[str, Any]) -> str:
    return str(exp.get("script_path") or "").strip()


def topic_prefix(value: str) -> str:
    parts = [part for part in value.split(".") if part]
    if not parts:
        return "unspecified"
    if len(parts) >= 4 and parts[:2] == ["h3", "cross_layer_relation"]:
        return ".".join(parts[:3])
    if len(parts) >= 2:
        return ".".join(parts[:2])
    return parts[0]


def source_topic(claim: dict[str, Any]) -> str:
    cid = claim_id(claim)
    if cid:
        return topic_prefix(cid)
    linked = str(claim.get("linked_conjecture_id") or "").strip()
    if linked:
        return topic_prefix(linked)
    return "unspecified"


def claim_coverage(claims: list[dict[str, Any]], registry_present: bool) -> dict[str, Any]:
    total = len(claims)
    intaken_ids = sorted(claim_id(claim) for claim in claims if claim_id(claim)) if registry_present else []
    omitted = [] if registry_present else sorted(claim_id(claim) for claim in claims if claim_id(claim))
    by_domain: Counter[str] = Counter(source_topic(claim) for claim in claims)
    omitted_by_domain: Counter[str] = Counter()
    if not registry_present:
        omitted_by_domain.update(source_topic(claim) for claim in claims)
    return {
        "total": total,
        "intaken": len(intaken_ids),
        "omitted": len(omitted),
        "by_domain": dict(sorted(by_domain.items())),
        "omitted_by_domain": dict(sorted(omitted_by_domain.items())),
    }


def experiment_coverage(experiments: list[dict[str, Any]], inventoried_paths: list[str]) -> dict[str, Any]:
    declared = {
        experiment_script_path(exp): experiment_id(exp)
        for exp in experiments
        if experiment_script_path(exp)
    }
    declared_paths = set(declared)
    path_set = set(inventoried_paths)
    intaken_paths = sorted(declared_paths & path_set)
    missing_paths = sorted(declared_paths - path_set)
    extra_scripts = sorted(path_set - declared_paths)
    return {
        "registry_total": len(declared),
        "script_inventory_total": len(inventoried_paths),
        "intaken": len(intaken_paths),
        "omitted": len(missing_paths),
        "missing_script_paths": missing_paths,
        "extra_script_paths": extra_scripts,
    }


def path_coverage(paths: list[str]) -> dict[str, Any]:
    return {
        "total": len(paths),
        "intaken": len(paths),
        "omitted": 0,
    }


def required_paths(branch: str) -> list[Path]:
    return [SYNCED_DIR / rel for rel in SURFACES[branch].values()]


def build_branch(branch: str) -> dict[str, Any]:
    surface = SURFACES[branch]
    paths = {key: SYNCED_DIR / rel for key, rel in surface.items()}
    missing = sorted(rel for rel in surface.values() if not (SYNCED_DIR / rel).exists())
    if missing:
        raise FileNotFoundError(f"{branch} missing synced surface(s): {', '.join(missing)}")

    claims = claims_from(paths["claims"])
    experiments = experiments_from(paths["experiments"])
    experiment_paths = inventory_paths(paths["experiment_inventory"])
    namecert_paths = inventory_paths(paths["namecert_inventory"])
    data_paths = inventory_paths(paths["data_inventory"])

    payload: dict[str, Any] = {
        "claims": claim_coverage(claims, registry_present=True),
        "experiments": experiment_coverage(experiments, experiment_paths),
        "namecerts": path_coverage(namecert_paths),
        "data_files": path_coverage(data_paths),
        "surface_paths": dict(sorted(surface.items())),
    }
    if branch == "fibonacci":
        forced_paths = inventory_paths(paths["forced_window_structure_inventory"])
        payload["forced_window_structure"] = path_coverage(forced_paths)
    return payload


def compact_branch_summary(branch_payload: dict[str, Any]) -> dict[str, Any]:
    claims = branch_payload.get("claims", {})
    return {
        "claims_total": claims.get("total", 0),
        "intaken": claims.get("intaken", 0),
        "omitted": claims.get("omitted", 0),
        "domains": claims.get("omitted_by_domain", {}),
    }


def build_report() -> dict[str, Any]:
    branches = {name: build_branch(name) for name in sorted(SURFACES)}
    return {
        "schema": "window-codon-bridge-intake-coverage",
        "branches": branches,
        "summary": {
            name: compact_branch_summary(branches[name])
            for name in sorted(branches)
        },
    }


def render_md(report: dict[str, Any]) -> str:
    lines = [
        "# Intake Coverage",
        "",
        "Deterministic per-cycle report for the compact bridge intake surface.",
        "",
        "| Branch | Claims intaken/total | Experiments intaken/registered | Namecerts intaken/total | Data files intaken/total |",
        "| --- | ---: | ---: | ---: | ---: |",
    ]
    branches = report.get("branches", {})
    for branch in sorted(branches):
        item = branches[branch]
        claims = item["claims"]
        experiments = item["experiments"]
        namecerts = item["namecerts"]
        data_files = item["data_files"]
        lines.append(
            "| {branch} | {ci}/{ct} | {ei}/{et} | {ni}/{nt} | {di}/{dt} |".format(
                branch=branch,
                ci=claims["intaken"],
                ct=claims["total"],
                ei=experiments["intaken"],
                et=experiments["registry_total"],
                ni=namecerts["intaken"],
                nt=namecerts["total"],
                di=data_files["intaken"],
                dt=data_files["total"],
            )
        )

    lines.extend(["", "## Omitted Claims By Domain", ""])
    for branch in sorted(branches):
        omitted = branches[branch]["claims"]["omitted_by_domain"]
        if omitted:
            rendered = ", ".join(f"`{key}`: {omitted[key]}" for key in sorted(omitted))
        else:
            rendered = "none"
        lines.append(f"- `{branch}`: {rendered}")

    lines.extend(["", "## Claim Domains", ""])
    for branch in sorted(branches):
        domains = branches[branch]["claims"]["by_domain"]
        rendered = ", ".join(f"`{key}`: {domains[key]}" for key in sorted(domains))
        lines.append(f"- `{branch}`: {rendered or 'none'}")

    lines.append("")
    return "\n".join(lines)


def generate() -> dict[str, Any]:
    report = build_report()
    write_json(OUT_JSON, report)
    OUT_MD.write_text(render_md(report), encoding="utf-8")
    summary = {
        "status": "generated",
        "bio": report["summary"]["bio"],
        "fibonacci": report["summary"]["fibonacci"],
    }
    print(json.dumps(summary, sort_keys=True), flush=True)
    return summary


def main() -> int:
    generate()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
