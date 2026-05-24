#!/usr/bin/env python3
"""P/G/A lane helpers for BioReality automation."""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
import tempfile
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

try:
    import agent_bus
    import bio_reality_loop
    from experiments import runner as experiment_runner
    import signal_assimilator
    import vision_intake
    from store import BioRealityPaths, BioRealityStore, append_jsonl, read_jsonl, write_jsonl
except ModuleNotFoundError:  # pragma: no cover
    sys.path.insert(0, str(Path(__file__).resolve().parent))
    import agent_bus
    import bio_reality_loop
    from experiments import runner as experiment_runner
    import signal_assimilator
    import vision_intake
    from store import BioRealityPaths, BioRealityStore, append_jsonl, read_jsonl, write_jsonl


SCRIPT_DIR = Path(__file__).resolve().parent
DOMAIN_PROFILE = SCRIPT_DIR / "dna_to_protein_ladder.json"


def now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def _packet_target(packet_kind: str, packet_id: str, lane: str, reason: str, priority: int) -> dict[str, Any]:
    return {
        "packet_kind": packet_kind,
        "packet_id": packet_id,
        "lane": lane,
        "priority": priority,
        "reason": reason,
        "created_at": now_iso(),
        "allowed_write": "runtime_packet_only",
    }


def _dedup_targets(targets: list[dict[str, Any]]) -> list[dict[str, Any]]:
    seen: set[tuple[str, str, str, str]] = set()
    out: list[dict[str, Any]] = []
    for target in targets:
        key = (
            str(target.get("packet_kind") or ""),
            str(target.get("packet_id") or ""),
            str(target.get("lane") or ""),
            str(target.get("reason") or ""),
        )
        if key in seen:
            continue
        seen.add(key)
        out.append(target)
    out.sort(key=lambda item: (-int(item.get("priority") or 0), str(item.get("packet_kind") or ""), str(item.get("packet_id") or "")))
    return out


def _load_domain_profile() -> dict[str, Any]:
    try:
        data = json.loads(DOMAIN_PROFILE.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return {}
    return data if isinstance(data, dict) else {}


def run_vision_lane(store: BioRealityStore) -> dict[str, Any]:
    return vision_intake.run_vision_lane(store)


def bootstrap_research_memory(store: BioRealityStore) -> dict[str, Any]:
    """Create the first self-generated BioReality packets when memory is empty."""
    if any((store.load_conjectures(), store.load_contacts(), store.load_probes(), store.load_mismatches())):
        return {"bootstrapped": False}
    profile = _load_domain_profile()
    profile_id = str(profile.get("profile_id") or "dna_to_protein_realization")
    contacts = [
        {
            "contact_id": "curated.standard.code.table",
            "source_kind": "genetic_code_table",
            "source_ref": "curated standard genetic-code bridge",
            "source_snapshot": profile_id,
            "observed_fact": "A curated standard-code table assigns codons to amino-acid or stop labels.",
            "resolution": "codon label readback",
            "known_noise_or_bias": "The table is a reality bridge for code labels, not a mechanism or universality proof.",
            "can_test": ["code_read", "local codon tile label split"],
            "cannot_test": ["translation realization", "structural order", "physical admissibility", "function realization"],
            "null_reason": "",
        }
    ]
    conjectures = [
        {
            "conjecture_id": "codon.window6.local.tile.boundary",
            "biological_object": "standard-code codon table",
            "informal_statement": (
                "Window-six codon coordinates may expose local boundary-tile structure, "
                "but curated code labels remain external reality contacts."
            ),
            "bedc_minimal_form": {
                "carrier": "codon cube Q6",
                "distinctions": ["six-bit codon display", "local tile face", "singleton label corner", "three-point label class"],
                "readback": "standard-code label table",
                "internal_structure": ["coordinate", "closure", "spectrum", "relation"],
            },
            "claimed_layer": "code_read",
            "evidence_basis": ["external_reality", "bedc_coordinate", "derived_probe"],
            "reality_contact_refs": ["curated.standard.code.table"],
            "probe_refs": ["codon.local.tile.no.global.law"],
            "forbidden_claims": [
                "A local codon tile is not a global biological law.",
                "Window-six geometry alone is not translation, structure, physical admissibility, or function.",
            ],
            "null_reason": "",
        }
    ]
    probes = [
        {
            "probe_id": "codon.local.tile.no.global.law",
            "conjecture_ref": "codon.window6.local.tile.boundary",
            "probe_kind": "boundary_mismatch",
            "derived_from": ["bedc_coordinate", "bedc_closure", "external_reality_hint"],
            "test_statement": "A local codon-tile pattern must stay at code_read unless a separate higher-layer contact is supplied.",
            "support_condition": "The curated code table supports only codon-label readback and local split checks.",
            "break_condition": "The pipeline promotes the local tile to translation, structure, physical admissibility, function, or universal mechanism.",
            "required_contacts": ["curated.standard.code.table"],
            "forbidden_interpretations": [
                "Do not infer that DNA obeys BEDC geometry as biological necessity.",
                "Do not infer protein function from a codon-tile split.",
            ],
            "null_reason": "",
        }
    ]
    mismatches = [
        {
            "mismatch_id": "codon.local.tile.scope.boundary",
            "probe_ref": "codon.local.tile.no.global.law",
            "contact_ref": "curated.standard.code.table",
            "status": "aligned",
            "mismatch_kind": "none",
            "observed_delta": "The contact supports code-layer readback and blocks higher-layer promotion.",
            "refinement_pressure": "Next cycles should search for separate reality contacts before crossing the translation or function boundary.",
            "blocked_claims": ["protein realization", "folded structure", "physical admissibility", "biological function", "universal mechanism"],
            "null_reason": "",
        }
    ]
    store.write_contacts(contacts)
    store.write_conjectures(conjectures)
    store.write_probes(probes)
    store.write_mismatches(mismatches)
    return {
        "bootstrapped": True,
        "profile_id": profile_id,
        "conjectures": len(conjectures),
        "contacts": len(contacts),
        "probes": len(probes),
        "mismatches": len(mismatches),
    }


def _profile_layers(profile: dict[str, Any]) -> list[str]:
    layers = profile.get("layers", [])
    if not isinstance(layers, list):
        return []
    out: list[str] = []
    for layer in layers:
        if isinstance(layer, str) and layer:
            out.append(layer)
        elif isinstance(layer, dict) and isinstance(layer.get("layer"), str) and layer.get("layer"):
            out.append(str(layer["layer"]))
    return out


def promote_next_layer(store: BioRealityStore) -> dict[str, Any]:
    """When all conjectures at the current depth are aligned, seed the next layer."""
    profile = _load_domain_profile()
    layers = _profile_layers(profile)
    if not layers:
        return {"promoted": False, "reason": "no layer ladder"}
    layer_descriptions = profile.get("layer_descriptions", {})
    if not isinstance(layer_descriptions, dict):
        layer_descriptions = {}

    conjectures = store.load_conjectures()
    mismatches = store.load_mismatches()
    for index, layer in enumerate(layers[:-1]):
        layer_conjectures = [
            conjecture
            for conjecture in conjectures
            if str(conjecture.get("claimed_layer") or "") == layer
        ]
        if not layer_conjectures:
            continue
        layer_probe_refs = {
            str(probe_ref)
            for conjecture in layer_conjectures
            for probe_ref in conjecture.get("probe_refs", [])
            if isinstance(probe_ref, str)
        }
        related_mismatches = [
            mismatch
            for mismatch in mismatches
            if str(mismatch.get("probe_ref") or "") in layer_probe_refs
        ]
        mismatch_probe_refs = {
            str(mismatch.get("probe_ref") or "")
            for mismatch in related_mismatches
        }
        if not all(
            any(probe_ref in mismatch_probe_refs for probe_ref in conjecture.get("probe_refs", []) if isinstance(probe_ref, str))
            for conjecture in layer_conjectures
        ):
            continue
        if not all(str(mismatch.get("status") or "") in {"aligned", "blocked_null"} for mismatch in related_mismatches):
            continue

        next_layer = layers[index + 1]
        if any(str(conjecture.get("claimed_layer") or "") == next_layer for conjecture in conjectures):
            return {"promoted": False, "reason": "next layer already seeded"}
        new_conjecture_id = f"{next_layer}.seed.boundary"
        conjectures.append(
            {
                "conjecture_id": new_conjecture_id,
                "biological_object": str(layer_descriptions.get(next_layer, next_layer)),
                "informal_statement": (
                    f"Seed packet for layer {next_layer}. Awaits a separate reality contact before any claim can be made."
                ),
                "bedc_minimal_form": {
                    "carrier": "awaiting reality contact",
                    "distinctions": ["awaiting reality contact"],
                    "readback": "awaiting reality contact",
                    "internal_structure": ["none"],
                },
                "claimed_layer": next_layer,
                "evidence_basis": ["bedc_coordinate"],
                "reality_contact_refs": [],
                "probe_refs": [],
                "forbidden_claims": [
                    f"Layer {next_layer} cannot be promoted to higher layers without a separate reality contact.",
                    f"BEDC coordinate alone does not realize layer {next_layer}.",
                ],
                "null_reason": "",
            }
        )
        store.write_conjectures(conjectures)
        return {
            "promoted": True,
            "new_conjecture_id": new_conjecture_id,
            "from_layer": layer,
            "to_layer": next_layer,
        }
    return {"promoted": False, "reason": "no aligned-closed layer"}


def run_packet_lane(store: BioRealityStore) -> dict[str, Any]:
    bootstrap = bootstrap_research_memory(store)
    promotion = promote_next_layer(store)
    conjectures = store.load_conjectures()
    contacts = store.load_contacts()
    probes = store.load_probes()
    mismatches = store.load_mismatches()
    contact_ids = {str(item.get("contact_id") or "") for item in contacts}
    probe_ids = {str(item.get("probe_id") or "") for item in probes}
    mismatch_probe_ids = {str(item.get("probe_ref") or "") for item in mismatches}
    targets: list[dict[str, Any]] = []

    for conjecture in conjectures:
        conjecture_id = str(conjecture.get("conjecture_id") or "")
        if not conjecture_id:
            continue
        probe_refs = [str(item) for item in conjecture.get("probe_refs", []) if isinstance(item, str)]
        contact_refs = [str(item) for item in conjecture.get("reality_contact_refs", []) if isinstance(item, str)]
        evidence = set(str(item) for item in conjecture.get("evidence_basis", []) if isinstance(item, str))
        if not probe_refs:
            targets.append(_packet_target("conjecture", conjecture_id, "bio-P", "derive falsifiable probe from BEDC minimal form", 90))
        if "external_reality" in evidence and not contact_refs:
            targets.append(_packet_target("conjecture", conjecture_id, "bio-P", "attach curated reality contact without promoting mechanism", 95))
        for contact_ref in contact_refs:
            if contact_ref not in contact_ids:
                targets.append(_packet_target("conjecture", conjecture_id, "bio-P", f"resolve missing reality contact {contact_ref}", 95))
        for probe_ref in probe_refs:
            if probe_ref not in probe_ids:
                targets.append(_packet_target("conjecture", conjecture_id, "bio-P", f"resolve missing probe {probe_ref}", 88))

    for probe in probes:
        probe_id = str(probe.get("probe_id") or "")
        if not probe_id:
            continue
        required_contacts = [str(item) for item in probe.get("required_contacts", []) if isinstance(item, str)]
        if not required_contacts:
            targets.append(_packet_target("probe", probe_id, "bio-P", "name at least one reality contact required by the probe", 82))
        for contact_ref in required_contacts:
            if contact_ref not in contact_ids:
                targets.append(_packet_target("probe", probe_id, "bio-P", f"resolve missing required contact {contact_ref}", 92))
        if required_contacts and probe_id not in mismatch_probe_ids:
            targets.append(_packet_target("probe", probe_id, "bio-P", "record mismatch or alignment ledger for contact chain", 78))

    for mismatch in mismatches:
        mismatch_id = str(mismatch.get("mismatch_id") or "")
        status = str(mismatch.get("status") or "")
        if mismatch_id and status in {"mismatch", "partially_aligned", "underdetermined"}:
            targets.append(_packet_target("mismatch", mismatch_id, "bio-P", f"refine conjecture after {status} contact", 97))

    targets = _dedup_targets(targets)
    store.write_packet_targets(targets)
    render_lane_dashboard(store.paths, targets)
    return {
        "lane": "bio-P",
        **bootstrap,
        "promotion": promotion,
        "conjectures": len(conjectures),
        "contacts": len(contacts),
        "probes": len(probes),
        "mismatches": len(mismatches),
        "packet_targets": len(targets),
    }


def run_gate_lane(store: BioRealityStore) -> dict[str, Any]:
    summary = bio_reality_loop.run_once(store)
    return {"lane": "bio-G", **summary}


def _load_claims_document(path: Path) -> dict[str, Any]:
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return {"version": "bio-reality-claims-v1", "claims": []}
    if not isinstance(data, dict):
        return {"version": "bio-reality-claims-v1", "claims": []}
    claims = data.get("claims")
    if not isinstance(claims, list):
        data["claims"] = []
    return data


def _load_experiments_document(path: Path) -> dict[str, Any]:
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return {"version": "bio-reality-experiments-v1", "experiments": []}
    if not isinstance(data, dict):
        return {"version": "bio-reality-experiments-v1", "experiments": []}
    experiments = data.get("experiments")
    if not isinstance(experiments, list):
        data["experiments"] = []
    return data


def _history_entry(status: str, reason: str, **extra: Any) -> dict[str, Any]:
    entry = {"ts": now_iso(), "status": status, "reason": reason}
    entry.update(extra)
    return entry


def _claim_state_counts(claims: list[dict[str, Any]]) -> dict[str, int]:
    counts: dict[str, int] = {}
    for claim in claims:
        status = str(claim.get("status") or "open")
        counts[status] = counts.get(status, 0) + 1
    return dict(sorted(counts.items()))


def _run_id(result: dict[str, Any]) -> str:
    material = json.dumps(result, sort_keys=True, ensure_ascii=True)
    return hashlib.sha256(material.encode("utf-8")).hexdigest()[:12]


def _check_summary(checks: Any) -> dict[str, int]:
    if not isinstance(checks, list):
        return {"total": 0, "passed": 0, "failed": 0}
    total = sum(1 for item in checks if isinstance(item, dict))
    passed = sum(1 for item in checks if isinstance(item, dict) and item.get("passed") is True)
    return {"total": total, "passed": passed, "failed": total - passed}


def _missing_required_data(repo_root: Path, experiment: dict[str, Any]) -> list[str]:
    required = experiment.get("required_data")
    if not isinstance(required, list):
        return []
    missing: list[str] = []
    for item in required:
        if not isinstance(item, str) or not item:
            continue
        path = Path(item)
        if path.is_absolute() or not (repo_root / path).exists():
            missing.append(item)
    return missing


def _write_claims_document(path: Path, document: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(document, indent=2, ensure_ascii=False, sort_keys=False) + "\n", encoding="utf-8")


def run_execute_lane(store: BioRealityStore) -> dict[str, Any]:
    claims_document = _load_claims_document(store.paths.claims_registry)
    experiments_document = _load_experiments_document(store.paths.experiments_registry)
    claims = [item for item in claims_document.get("claims", []) if isinstance(item, dict)]
    experiments = [item for item in experiments_document.get("experiments", []) if isinstance(item, dict)]
    experiment_by_id = {
        str(experiment.get("experiment_id") or ""): experiment
        for experiment in experiments
        if experiment.get("experiment_id")
    }
    claim_by_id = {
        str(claim.get("claim_id") or ""): claim
        for claim in claims
        if claim.get("claim_id")
    }
    repo_root = SCRIPT_DIR.parent.parent
    summary = {
        "lane": "bio-X",
        "executed": 0,
        "passed_this_cycle": 0,
        "failed_this_cycle": 0,
        "needs_data_this_cycle": 0,
        "error_this_cycle": 0,
        "skipped_unmet_dep": 0,
        "claim_states": {},
    }

    for claim in claims:
        status = str(claim.get("status") or "open")
        if status not in {"open", "needs_rerun"}:
            continue
        experiment_id = str(claim.get("experiment_id") or "")
        experiment = experiment_by_id.get(experiment_id)
        if experiment is None:
            continue
        dependencies = [str(item) for item in claim.get("depends_on", []) if isinstance(item, str)]
        unmet = [dep for dep in dependencies if str(claim_by_id.get(dep, {}).get("status") or "") != "passed"]
        if unmet:
            history = claim.setdefault("history", [])
            if isinstance(history, list):
                history.append(_history_entry("skipped", "skipped due to unmet dependency", unmet_dependencies=unmet))
            summary["skipped_unmet_dep"] += 1
            continue
        missing_data = _missing_required_data(repo_root, experiment)
        if missing_data:
            claim["status"] = "needs_data"
            history = claim.setdefault("history", [])
            if isinstance(history, list):
                history.append(_history_entry("needs_data", "missing required_data", missing_data=missing_data))
            result = {
                "experiment_id": experiment_id,
                "claim_id": str(claim.get("claim_id") or ""),
                "started_at": now_iso(),
                "completed_at": now_iso(),
                "status": "needs_data",
                "checks": [],
                "result": {"missing_data": missing_data},
                "stdout_tail": "",
                "stderr_tail": "",
                "returncode": None,
            }
            result["experiment_run_id"] = _run_id(result)
            append_jsonl(store.paths.experiment_runs, [result])
            summary["needs_data_this_cycle"] += 1
            continue
        timeout = int(experiment.get("timeout_seconds") or 300)
        result = experiment_runner.run_experiment(experiment, timeout_seconds=timeout, repo_root=repo_root)
        result["experiment_run_id"] = _run_id(result)
        append_jsonl(store.paths.experiment_runs, [result])
        summary["executed"] += 1
        result_status = str(result.get("status") or "error")
        if result_status == "passed":
            claim["status"] = "passed"
            summary["passed_this_cycle"] += 1
        elif result_status == "failed":
            claim["status"] = "failed"
            summary["failed_this_cycle"] += 1
        elif result_status == "needs_data":
            claim["status"] = "needs_data"
            summary["needs_data_this_cycle"] += 1
        else:
            claim["status"] = "error"
            summary["error_this_cycle"] += 1
        history = claim.setdefault("history", [])
        if isinstance(history, list):
            history.append(
                _history_entry(
                    str(claim.get("status") or "error"),
                    "experiment result",
                    experiment_run_id=result["experiment_run_id"],
                    checks=_check_summary(result.get("checks")),
                )
            )

    claims_document["claims"] = claims
    _write_claims_document(store.paths.claims_registry, claims_document)
    summary["claim_states"] = _claim_state_counts(claims)
    return summary


def run_agent_lane(store: BioRealityStore, *, execute_codex: bool = True, max_dispatch: int = 1) -> dict[str, Any]:
    return agent_bus.run_agent_lane(store, execute_codex=execute_codex, max_dispatch=max_dispatch)


def run_quality_lane(store: BioRealityStore) -> dict[str, Any]:
    return agent_bus.run_quality_lane(store)


def run_assimilation_lane(paths: BioRealityPaths) -> dict[str, Any]:
    signals = signal_assimilator.summarize(paths)
    targets = read_jsonl(paths.packet_targets)
    events = read_jsonl(paths.events)
    agent_tasks = read_jsonl(paths.agent_tasks)
    dispatch_results = read_jsonl(paths.dispatch_results)
    hardening_targets = read_jsonl(paths.hardening_targets)
    vision_rows = read_jsonl(paths.vision_ledger)
    signals["packet_targets"] = len(targets)
    signals["events"] = len(events)
    signals["agent_tasks"] = len(agent_tasks)
    signals["dispatch_results"] = len(dispatch_results)
    signals["dispatch_planned_only"] = sum(1 for item in dispatch_results if item.get("dispatch_status") == "planned_only")
    signals["hardening_targets"] = len(hardening_targets)
    signals["vision_rows"] = len(vision_rows)
    signals["lane"] = "bio-A"
    signal_assimilator.write_summary(signals)
    render_lane_dashboard(paths, targets, signals)
    return signals


def _tex_escape(value: Any) -> str:
    text = str(value)
    replacements = {
        "\\": r"\textbackslash{}",
        "&": r"\&",
        "%": r"\%",
        "$": r"\$",
        "#": r"\#",
        "_": r"\_",
        "{": r"\{",
        "}": r"\}",
        "~": r"\textasciitilde{}",
        "^": r"\textasciicircum{}",
    }
    return "".join(replacements.get(char, char) for char in text)


def _sentence_list(items: Any) -> str:
    if not isinstance(items, list) or not items:
        return "none recorded"
    return "; ".join(_tex_escape(item) for item in items if isinstance(item, str) and item.strip()) or "none recorded"


def _by_id(records: list[dict[str, Any]], key: str) -> dict[str, dict[str, Any]]:
    return {str(record.get(key) or ""): record for record in records if record.get(key)}


def _passed_conjectures(store: BioRealityStore) -> list[dict[str, Any]]:
    conjectures = store.load_conjectures()
    contacts = store.load_contacts()
    probes = store.load_probes()
    mismatches = store.load_mismatches()
    results = bio_reality_loop.gate_all(conjectures, contacts, probes, mismatches)
    passed = {
        str(result.get("packet_id") or "")
        for result in results
        if result.get("packet_kind") == "conjecture" and result.get("gate_status") == "gate_passed"
    }
    return [record for record in conjectures if str(record.get("conjecture_id") or "") in passed]


def _temp_paths(base: Path) -> BioRealityPaths:
    return BioRealityPaths(
        root=SCRIPT_DIR,
        conjectures=base / "conjectures.jsonl",
        contacts=base / "reality_contacts.jsonl",
        probes=base / "probes.jsonl",
        mismatches=base / "mismatches.jsonl",
        gate_results=base / "gate_results.jsonl",
        deepening_tasks=base / "deepening_tasks.jsonl",
        review_queue=base / "review_queue.jsonl",
        packet_targets=base / "packet_targets.jsonl",
        events=base / "events.jsonl",
        agent_tasks=base / "agent_tasks.jsonl",
        agent_reviews=base / "agent_reviews.jsonl",
        dispatch_results=base / "dispatch_results.jsonl",
        hardening_targets=base / "hardening_targets.jsonl",
        lane_dashboard=base / "lane_dashboard.md",
        claims_registry=base / "claims.json",
        experiments_registry=base / "experiments.json",
        experiment_runs=base / "experiment_runs.jsonl",
        experiments_dir=base / "experiments",
        data_dir=base / "data",
        vision_dir=base / "vision",
        vision_ledger=base / "vision" / "ledger" / "intake_evaluations.jsonl",
        paper_main=base / "paper" / "main.tex",
        paper_part=base / "paper" / "parts" / "codon_window_reality_boundary.tex",
    )


def _render_paper_main(paths: BioRealityPaths) -> str:
    return "\n".join(
        [
            r"\documentclass[11pt]{article}",
            r"\usepackage[margin=1in]{geometry}",
            r"\usepackage[T1]{fontenc}",
            r"\usepackage{lmodern}",
            r"\usepackage{microtype}",
            r"\usepackage{hyperref}",
            "",
            r"\title{BioReality: Reality-Bound Biological Deepening}",
            r"\author{The Omega Institute}",
            r"\date{}",
            "",
            r"\begin{document}",
            r"\maketitle",
            "",
            r"\section{Scope}",
            "BioReality records biological conjecture deepening under explicit provenance boundaries. "
            "External curated biology is recorded as reality input; newmath and BEDC-style structure is recorded as internal derivation; every cross-layer biological claim remains blocked until a separate reality contact supports that layer.",
            "",
            r"\input{parts/codon_window_reality_boundary}",
            "",
            r"\end{document}",
            "",
        ]
    )


def _render_conjecture_section(
    conjecture: dict[str, Any],
    contacts_by_id: dict[str, dict[str, Any]],
    probes_by_id: dict[str, dict[str, Any]],
    mismatches_by_probe: dict[str, list[dict[str, Any]]],
) -> list[str]:
    conjecture_id = str(conjecture.get("conjecture_id") or "unnamed")
    form = conjecture.get("bedc_minimal_form") if isinstance(conjecture.get("bedc_minimal_form"), dict) else {}
    contact_refs = [str(item) for item in conjecture.get("reality_contact_refs", []) if isinstance(item, str)]
    probe_refs = [str(item) for item in conjecture.get("probe_refs", []) if isinstance(item, str)]
    lines = [
        rf"\subsection{{{_tex_escape(conjecture_id)}}}",
        "",
        rf"\paragraph{{Biological object.}} {_tex_escape(conjecture.get('biological_object', ''))}",
        "",
        rf"\paragraph{{Current claim.}} {_tex_escape(conjecture.get('informal_statement', ''))}",
        "",
        rf"\paragraph{{External reality input.}}",
    ]
    if contact_refs:
        for contact_ref in contact_refs:
            contact = contacts_by_id.get(contact_ref, {})
            lines.extend(
                [
                    rf"\textbf{{{_tex_escape(contact_ref)}}}. {_tex_escape(contact.get('observed_fact', 'missing contact record'))}",
                    "",
                    rf"Can test: {_sentence_list(contact.get('can_test'))}. Cannot test: {_sentence_list(contact.get('cannot_test'))}.",
                    "",
                ]
            )
    else:
        lines.extend(["No external contact is attached.", ""])
    lines.extend(
        [
            rf"\paragraph{{Internal newmath/BEDC derivation.}} Carrier: {_tex_escape(form.get('carrier', ''))}. "
            rf"Distinctions: {_sentence_list(form.get('distinctions'))}. "
            rf"Readback: {_tex_escape(form.get('readback', ''))}. "
            rf"Internal structure: {_sentence_list(form.get('internal_structure'))}.",
            "",
            rf"\paragraph{{Falsifiable probes.}}",
        ]
    )
    if probe_refs:
        for probe_ref in probe_refs:
            probe = probes_by_id.get(probe_ref, {})
            lines.extend(
                [
                    rf"\textbf{{{_tex_escape(probe_ref)}}}. {_tex_escape(probe.get('test_statement', 'missing probe record'))}",
                    "",
                    rf"Support condition: {_tex_escape(probe.get('support_condition', ''))}",
                    "",
                    rf"Break condition: {_tex_escape(probe.get('break_condition', ''))}",
                    "",
                ]
            )
    else:
        lines.extend(["No derived probe is attached.", ""])
    lines.append(r"\paragraph{Mismatch ledger.}")
    for probe_ref in probe_refs:
        for mismatch in mismatches_by_probe.get(probe_ref, []):
            lines.extend(
                [
                    rf"\textbf{{{_tex_escape(mismatch.get('mismatch_id', ''))}}}. Status: {_tex_escape(mismatch.get('status', ''))}. "
                    rf"Delta: {_tex_escape(mismatch.get('observed_delta', ''))}",
                    "",
                    rf"Refinement pressure: {_tex_escape(mismatch.get('refinement_pressure', ''))}",
                    "",
                ]
            )
    lines.extend(
        [
            rf"\paragraph{{Cannot-claim boundary.}} {_sentence_list(conjecture.get('forbidden_claims'))}",
            "",
        ]
    )
    return lines


def run_writeback_lane(store: BioRealityStore) -> dict[str, Any]:
    conjectures = _passed_conjectures(store)
    contacts = store.load_contacts()
    probes = store.load_probes()
    mismatches = store.load_mismatches()
    contacts_by_id = _by_id(contacts, "contact_id")
    probes_by_id = _by_id(probes, "probe_id")
    mismatches_by_probe: dict[str, list[dict[str, Any]]] = {}
    for mismatch in mismatches:
        probe_ref = str(mismatch.get("probe_ref") or "")
        if probe_ref:
            mismatches_by_probe.setdefault(probe_ref, []).append(mismatch)

    part_lines = [
        r"\section{Codon Window Reality Boundary}",
        r"\label{sec:codon-window-reality-boundary}",
        "",
        "This section records gate-passed BioReality research memory. "
        "Its statements separate curated biological reality contacts from internal coordinate, closure, spectrum, and relation readings.",
        "",
    ]
    for conjecture in conjectures:
        part_lines.extend(_render_conjecture_section(conjecture, contacts_by_id, probes_by_id, mismatches_by_probe))
    if not conjectures:
        part_lines.extend(["No conjecture has passed the BioReality gates.", ""])

    paths = store.paths
    paths.paper_main.parent.mkdir(parents=True, exist_ok=True)
    paths.paper_part.parent.mkdir(parents=True, exist_ok=True)
    paths.paper_main.write_text(_render_paper_main(paths), encoding="utf-8")
    paths.paper_part.write_text("\n".join(part_lines), encoding="utf-8")
    return {
        "lane": "bio-W",
        "paper_main": str(paths.paper_main),
        "paper_part": str(paths.paper_part),
        "written_conjectures": len(conjectures),
    }


def render_lane_dashboard(paths: BioRealityPaths, targets: list[dict[str, Any]], signals: dict[str, Any] | None = None) -> None:
    lines = [
        "# BioReality lane dashboard",
        "",
        f"- checked_at: {now_iso()}",
        f"- packet_targets: {len(targets)}",
    ]
    if signals:
        lines.extend(
            [
                f"- gate_results: {signals.get('gate_results', 0)}",
                f"- blocked: {signals.get('blocked', 0)}",
                f"- deepening_tasks: {signals.get('deepening_tasks', 0)}",
                f"- review_ready: {signals.get('review_ready', 0)}",
                f"- events: {signals.get('events', 0)}",
                f"- agent_tasks: {signals.get('agent_tasks', 0)}",
                f"- dispatch_results: {signals.get('dispatch_results', 0)}",
                f"- dispatch_planned_only: {signals.get('dispatch_planned_only', 0)}",
                f"- hardening_targets: {signals.get('hardening_targets', 0)}",
                f"- vision_rows: {signals.get('vision_rows', 0)}",
            ]
        )
    lines.extend(
        [
            "",
            "V lane scans user-authored vision files. P lane writes runtime packet targets only. G lane runs boundary gates.",
            "R lane plans Codex agent tasks from events. W lane writes only the",
            "standalone BioReality paper. Q lane converts review outcomes into",
            "hardening targets. A lane summarizes failures and scheduling pressure.",
            "No lane writes BEDC paper, Lean, remote refs, or un-gated biological conclusions.",
            "",
            "## Packet targets",
            "",
        ]
    )
    for target in targets[:40]:
        lines.append(
            f"- {target.get('lane')} {target.get('packet_kind')}:{target.get('packet_id')} "
            f"priority={target.get('priority')} - {target.get('reason')}"
        )
    lines.append("")
    paths.lane_dashboard.parent.mkdir(parents=True, exist_ok=True)
    paths.lane_dashboard.write_text("\n".join(lines), encoding="utf-8")


def self_test() -> int:
    with tempfile.TemporaryDirectory(prefix="bio-reality-lanes-") as tmp:
        base = Path(tmp)
        paths = _temp_paths(base)
        paths.vision_dir.mkdir(parents=True)
        (paths.vision_dir / "dna-to-protein-boundary.md").write_text(
            "\n".join(
                [
                    "---",
                    "slug: dna-to-protein-boundary",
                    'title: "Separate code readback from protein realization"',
                    "target_paper_section:",
                    "  - papers/bio_reality/parts/codon_window_reality_boundary.tex",
                    "required_reality_contacts:",
                    "  - curated.standard.code.table",
                    "required_gates:",
                    "forbidden_claims_to_check:",
                    "  - local_tile_as_global_biological_law",
                    "ripeness: ready",
                    "---",
                    "",
                    "Keep code-layer reality separate from protein realization.",
                ]
            ),
            encoding="utf-8",
        )
        store = BioRealityStore(paths)
        vision_summary = run_vision_lane(store)
        packet_summary = run_packet_lane(store)
        gate_summary = run_gate_lane(store)
        agent_summary = run_agent_lane(store, execute_codex=False)
        writeback_summary = run_writeback_lane(store)
        quality_summary = run_quality_lane(store)
        signals = run_assimilation_lane(paths)
        targets = read_jsonl(paths.packet_targets)
        if not packet_summary.get("bootstrapped") or packet_summary["conjectures"] != 2:
            print(json.dumps(packet_summary, indent=2), file=sys.stderr)
            return 1
        if packet_summary["promotion"].get("to_layer") != "orf_eligibility":
            print(json.dumps(packet_summary, indent=2), file=sys.stderr)
            return 1
        if vision_summary["visions"] != 1 or vision_summary["ready"] != 0:
            print(json.dumps(vision_summary, indent=2), file=sys.stderr)
            return 1
        if gate_summary["blocked"] != 1 or gate_summary["review_items"] == 0:
            print(json.dumps(gate_summary, indent=2), file=sys.stderr)
            return 1
        if signals["packet_targets"] != len(targets):
            print(json.dumps({"gate": gate_summary, "signals": signals}, indent=2), file=sys.stderr)
            return 1
        if writeback_summary["written_conjectures"] != 1 or not paths.paper_part.exists():
            print(json.dumps(writeback_summary, indent=2), file=sys.stderr)
            return 1
        if agent_summary["events"] == 0 or agent_summary["agent_tasks"] == 0:
            print(json.dumps(agent_summary, indent=2), file=sys.stderr)
            return 1
        if quality_summary["agent_reviews"] == 0:
            print(json.dumps(quality_summary, indent=2), file=sys.stderr)
            return 1

        promote_paths = _temp_paths(base / "promote")
        promote_store = BioRealityStore(promote_paths)
        promote_store.write_conjectures(
            [
                {
                    "conjecture_id": "codon.window6.local.tile.boundary",
                    "biological_object": "standard-code codon table",
                    "informal_statement": (
                        "Window-six codon coordinates may expose local boundary-tile structure, "
                        "but curated code labels remain external reality contacts."
                    ),
                    "bedc_minimal_form": {
                        "carrier": "codon cube Q6",
                        "distinctions": ["six-bit codon display", "local tile face", "singleton label corner", "three-point label class"],
                        "readback": "standard-code label table",
                        "internal_structure": ["coordinate", "closure", "spectrum", "relation"],
                    },
                    "claimed_layer": "code_read",
                    "evidence_basis": ["external_reality", "bedc_coordinate", "derived_probe"],
                    "reality_contact_refs": ["curated.standard.code.table"],
                    "probe_refs": ["codon.local.tile.no.global.law"],
                    "forbidden_claims": [
                        "A local codon tile is not a global biological law.",
                        "Window-six geometry alone is not translation, structure, physical admissibility, or function.",
                    ],
                    "null_reason": "",
                }
            ]
        )
        promote_store.write_contacts(
            [
                {
                    "contact_id": "curated.standard.code.table",
                    "source_kind": "genetic_code_table",
                    "source_ref": "curated standard genetic-code bridge",
                    "source_snapshot": "dna_to_protein_realization",
                    "observed_fact": "A curated standard-code table assigns codons to amino-acid or stop labels.",
                    "resolution": "codon label readback",
                    "known_noise_or_bias": "The table is a reality bridge for code labels, not a mechanism or universality proof.",
                    "can_test": ["code_read", "local codon tile label split"],
                    "cannot_test": ["translation realization", "structural order", "physical admissibility", "function realization"],
                    "null_reason": "",
                }
            ]
        )
        promote_store.write_probes(
            [
                {
                    "probe_id": "codon.local.tile.no.global.law",
                    "conjecture_ref": "codon.window6.local.tile.boundary",
                    "probe_kind": "boundary_mismatch",
                    "derived_from": ["bedc_coordinate", "bedc_closure", "external_reality_hint"],
                    "test_statement": "A local codon-tile pattern must stay at code_read unless a separate higher-layer contact is supplied.",
                    "support_condition": "The curated code table supports only codon-label readback and local split checks.",
                    "break_condition": "The pipeline promotes the local tile to translation, structure, physical admissibility, function, or universal mechanism.",
                    "required_contacts": ["curated.standard.code.table"],
                    "forbidden_interpretations": [
                        "Do not infer that DNA obeys BEDC geometry as biological necessity.",
                        "Do not infer protein function from a codon-tile split.",
                    ],
                    "null_reason": "",
                }
            ]
        )
        promote_store.write_mismatches(
            [
                {
                    "mismatch_id": "codon.local.tile.scope.boundary",
                    "probe_ref": "codon.local.tile.no.global.law",
                    "contact_ref": "curated.standard.code.table",
                    "status": "aligned",
                    "mismatch_kind": "none",
                    "observed_delta": "The contact supports code-layer readback and blocks higher-layer promotion.",
                    "refinement_pressure": "Next cycles should search for separate reality contacts before crossing the translation or function boundary.",
                    "blocked_claims": ["protein realization", "folded structure", "physical admissibility", "biological function", "universal mechanism"],
                    "null_reason": "",
                }
            ]
        )
        promote_summary = run_packet_lane(promote_store)
        promoted_conjectures = promote_store.load_conjectures()
        new_conjecture = next(
            item for item in promoted_conjectures if item.get("conjecture_id") == "orf_eligibility.seed.boundary"
        )
        if promote_summary["promotion"].get("promoted") is not True:
            print(json.dumps(promote_summary, indent=2), file=sys.stderr)
            return 1
        if promote_summary["promotion"].get("to_layer") != "orf_eligibility":
            print(json.dumps(promote_summary, indent=2), file=sys.stderr)
            return 1
        if len(promoted_conjectures) != 2:
            print(json.dumps(promoted_conjectures, indent=2), file=sys.stderr)
            return 1
        if new_conjecture.get("evidence_basis") != ["bedc_coordinate"] or new_conjecture.get("reality_contact_refs") != []:
            print(json.dumps(new_conjecture, indent=2), file=sys.stderr)
            return 1

        execute_paths = _temp_paths(base / "execute")
        execute_paths.claims_registry.parent.mkdir(parents=True, exist_ok=True)
        execute_paths.experiments_registry.parent.mkdir(parents=True, exist_ok=True)
        execute_paths.claims_registry.write_text(
            json.dumps(
                {
                    "version": "bio-reality-claims-v1",
                    "claims": [
                        {
                            "claim_id": "self.claim",
                            "hypothesis_level": "H0",
                            "phase": 1,
                            "statement": "self test claim",
                            "depends_on": [],
                            "status": "open",
                            "experiment_id": "self_missing_script",
                            "history": [],
                        }
                    ],
                },
                indent=2,
            ),
            encoding="utf-8",
        )
        execute_paths.experiments_registry.write_text(
            json.dumps(
                {
                    "version": "bio-reality-experiments-v1",
                    "experiments": [
                        {
                            "experiment_id": "self_missing_script",
                            "script_path": "tools/bio_reality/experiments/run_self_missing_script.py",
                            "claim_id": "self.claim",
                            "required_data": [],
                            "timeout_seconds": 5,
                            "acceptance": {"required_checks": []},
                        }
                    ],
                },
                indent=2,
            ),
            encoding="utf-8",
        )
        execute_store = BioRealityStore(execute_paths)
        execute_summary = run_execute_lane(execute_store)
        updated_claims = json.loads(execute_paths.claims_registry.read_text(encoding="utf-8"))["claims"]
        if execute_summary["error_this_cycle"] != 1 or updated_claims[0].get("status") != "error":
            print(json.dumps({"summary": execute_summary, "claims": updated_claims}, indent=2), file=sys.stderr)
            return 1
    print("[bio-reality-lanes] self-test ok")
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Run BioReality V/P/G/X/R/W/Q/A lanes")
    parser.add_argument("--lane", choices=["vision", "packet", "gate", "execute", "agent", "writeback", "quality", "assimilate", "all"], default="all")
    parser.add_argument("--plan-only", action="store_true")
    parser.add_argument("--max-dispatch", type=int, default=1)
    parser.add_argument("--conjectures", default=str(BioRealityPaths.conjectures))
    parser.add_argument("--contacts", default=str(BioRealityPaths.contacts))
    parser.add_argument("--probes", default=str(BioRealityPaths.probes))
    parser.add_argument("--mismatches", default=str(BioRealityPaths.mismatches))
    parser.add_argument("--gate-results", default=str(BioRealityPaths.gate_results))
    parser.add_argument("--deepening-tasks", default=str(BioRealityPaths.deepening_tasks))
    parser.add_argument("--review-queue", default=str(BioRealityPaths.review_queue))
    parser.add_argument("--packet-targets", default=str(BioRealityPaths.packet_targets))
    parser.add_argument("--events", default=str(BioRealityPaths.events))
    parser.add_argument("--agent-tasks", default=str(BioRealityPaths.agent_tasks))
    parser.add_argument("--agent-reviews", default=str(BioRealityPaths.agent_reviews))
    parser.add_argument("--dispatch-results", default=str(BioRealityPaths.dispatch_results))
    parser.add_argument("--hardening-targets", default=str(BioRealityPaths.hardening_targets))
    parser.add_argument("--lane-dashboard", default=str(BioRealityPaths.lane_dashboard))
    parser.add_argument("--vision-dir", default=str(BioRealityPaths.vision_dir))
    parser.add_argument("--vision-ledger", default=str(BioRealityPaths.vision_ledger))
    parser.add_argument("--paper-main", default=str(BioRealityPaths.paper_main))
    parser.add_argument("--paper-part", default=str(BioRealityPaths.paper_part))
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args(argv)
    if args.self_test:
        return self_test()
    paths = BioRealityPaths(
        root=SCRIPT_DIR,
        conjectures=Path(args.conjectures),
        contacts=Path(args.contacts),
        probes=Path(args.probes),
        mismatches=Path(args.mismatches),
        gate_results=Path(args.gate_results),
        deepening_tasks=Path(args.deepening_tasks),
        review_queue=Path(args.review_queue),
        packet_targets=Path(args.packet_targets),
        events=Path(args.events),
        agent_tasks=Path(args.agent_tasks),
        agent_reviews=Path(args.agent_reviews),
        dispatch_results=Path(args.dispatch_results),
        hardening_targets=Path(args.hardening_targets),
        lane_dashboard=Path(args.lane_dashboard),
        vision_dir=Path(args.vision_dir),
        vision_ledger=Path(args.vision_ledger),
        paper_main=Path(args.paper_main),
        paper_part=Path(args.paper_part),
    )
    store = BioRealityStore(paths)
    summaries: list[dict[str, Any]] = []
    if args.lane in {"vision", "all"}:
        summaries.append(run_vision_lane(store))
    if args.lane in {"packet", "all"}:
        summaries.append(run_packet_lane(store))
    if args.lane in {"gate", "all"}:
        summaries.append(run_gate_lane(store))
    if args.lane in {"execute", "all"}:
        summaries.append(run_execute_lane(store))
    if args.lane in {"agent", "all"}:
        summaries.append(run_agent_lane(store, execute_codex=not args.plan_only, max_dispatch=max(0, args.max_dispatch)))
    if args.lane in {"writeback", "all"}:
        summaries.append(run_writeback_lane(store))
    if args.lane in {"quality", "all"}:
        summaries.append(run_quality_lane(store))
    if args.lane in {"assimilate", "all"}:
        summaries.append(run_assimilation_lane(paths))
    print(json.dumps(summaries, ensure_ascii=False, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
