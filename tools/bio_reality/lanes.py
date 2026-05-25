#!/usr/bin/env python3
"""P/G/A lane helpers for BioReality automation."""

from __future__ import annotations

import argparse
import fnmatch
import hashlib
import json
import subprocess
import sys
import tempfile
import time
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
PIPELINE_CONFIG = SCRIPT_DIR / "pipeline_config.json"


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


def _open_event_keys(events: list[dict[str, Any]]) -> set[tuple[str, str]]:
    return {
        (str(event.get("event_kind") or ""), str(event.get("subject_id") or ""))
        for event in events
        if str(event.get("status") or "open") == "open"
    }


def _failed_check_name(run: dict[str, Any]) -> str:
    checks = run.get("checks")
    if not isinstance(checks, list):
        return ""
    for check in checks:
        if not isinstance(check, dict):
            continue
        if check.get("passed") is False:
            name = str(check.get("name") or "")
            if name:
                return name
    return ""


def _brief_run(record: dict[str, Any]) -> dict[str, Any]:
    return {
        "experiment_run_id": record.get("experiment_run_id"),
        "completed_at": record.get("completed_at"),
        "status": record.get("status"),
        "failed_check": _failed_check_name(record),
    }


def _experiment_claim_index(claims: list[dict[str, Any]], experiments: list[dict[str, Any]]) -> dict[str, str]:
    claim_by_experiment = {
        str(claim.get("experiment_id") or ""): str(claim.get("claim_id") or "")
        for claim in claims
        if claim.get("experiment_id") and claim.get("claim_id")
    }
    for experiment in experiments:
        experiment_id = str(experiment.get("experiment_id") or "")
        claim_id = str(experiment.get("claim_id") or "")
        if experiment_id and claim_id:
            claim_by_experiment[experiment_id] = claim_id
    return claim_by_experiment


def run_plan_lane(store: BioRealityStore) -> dict[str, Any]:
    """Detect phase-advance and stuck-claim signals, emit events for bio-R."""
    claims_document = _load_claims_document(store.paths.claims_registry)
    experiments_document = _load_experiments_document(store.paths.experiments_registry)
    claims = [
        item
        for item in claims_document.get("claims", [])
        if isinstance(item, dict) and str(item.get("hypothesis_level") or "") != "meta"
    ]
    experiments = [item for item in experiments_document.get("experiments", []) if isinstance(item, dict)]
    existing_events = store.load_events()
    open_event_keys = _open_event_keys(existing_events)
    new_events: list[dict[str, Any]] = []
    phases_passed: list[int] = []

    claims_by_phase: dict[int, list[dict[str, Any]]] = {}
    for claim in claims:
        phase_value = claim.get("phase")
        try:
            phase = int(phase_value)
        except (TypeError, ValueError):
            continue
        claims_by_phase.setdefault(phase, []).append(claim)

    for phase in sorted(claims_by_phase):
        group = claims_by_phase[phase]
        if not group or not all(str(claim.get("status") or "") == "passed" for claim in group):
            continue
        phases_passed.append(phase)
        if ("phase_advance_proposed", str(phase)) in open_event_keys:
            continue
        new_events.append(
            agent_bus._event(
                "phase_advance_proposed",
                "bio-Plan",
                "phase",
                str(phase),
                f"all {len(group)} claim(s) at phase {phase} passed; propose next phase",
                {"phase": phase, "passed_claims": [str(claim.get("claim_id") or "") for claim in group]},
            )
        )
        open_event_keys.add(("phase_advance_proposed", str(phase)))

    claim_by_id = {
        str(claim.get("claim_id") or ""): claim
        for claim in claims
        if claim.get("claim_id")
    }
    claim_id_by_experiment = _experiment_claim_index(claims, experiments)
    runs_by_experiment: dict[str, list[dict[str, Any]]] = {}
    for run in read_jsonl(store.paths.experiment_runs):
        experiment_id = str(run.get("experiment_id") or "")
        if experiment_id:
            runs_by_experiment.setdefault(experiment_id, []).append(run)

    stuck_statuses = {"failed", "error", "timeout"}
    for experiment_id in sorted(runs_by_experiment):
        runs = sorted(
            runs_by_experiment[experiment_id],
            key=lambda record: str(record.get("completed_at") or record.get("started_at") or ""),
            reverse=True,
        )
        recent = runs[:3]
        if len(recent) < 3:
            continue
        statuses = {str(run.get("status") or "") for run in recent}
        if not statuses <= stuck_statuses:
            continue
        claim_id = claim_id_by_experiment.get(experiment_id) or str(recent[0].get("claim_id") or "")
        claim = claim_by_id.get(claim_id, {})
        if not claim_id or str(claim.get("status") or "") == "passed":
            continue
        if ("claim_redesign_proposed", experiment_id) in open_event_keys:
            continue
        failed_checks = [_failed_check_name(run) for run in recent if _failed_check_name(run)]
        check_name = failed_checks[0] if failed_checks else ""
        distinct_checks = sorted(set(failed_checks))
        reason = (
            f"experiment {experiment_id} status failed in last 3 runs; "
            f"failed checks observed: {', '.join(distinct_checks) or 'unspecified'}"
        )
        new_events.append(
            agent_bus._event(
                "claim_redesign_proposed",
                "bio-Plan",
                "experiment",
                experiment_id,
                reason,
                {
                    "experiment_id": experiment_id,
                    "claim_id": claim_id,
                    "failed_check": check_name,
                    "failed_checks_distinct": distinct_checks,
                    "recent_runs": [_brief_run(run) for run in recent],
                },
            )
        )
        open_event_keys.add(("claim_redesign_proposed", experiment_id))

    phase_advance_events = sum(1 for event in new_events if event.get("event_kind") == "phase_advance_proposed")
    stuck_redesign_events = sum(1 for event in new_events if event.get("event_kind") == "claim_redesign_proposed")
    merged = agent_bus._dedup(existing_events + new_events, "event_id")
    store.write_events(merged)
    return {
        "lane": "bio-Plan",
        "phase_advance_events": phase_advance_events,
        "stuck_redesign_events": stuck_redesign_events,
        "phases_passed": phases_passed,
    }


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


def _experiment_changed_since_last_history(
    claim: dict[str, Any],
    experiment: dict[str, Any],
    repo_root: Path,
    experiments_registry: Path,
) -> bool:
    """Return True if the experiment script or its registry entry has been
    modified after the most recent claim.history timestamp. Used to promote
    a failed/error claim back to needs_rerun when bio-planner reshapes the
    experiment."""
    from datetime import datetime
    history = claim.get("history")
    if not isinstance(history, list) or not history:
        return False
    last = history[-1] if isinstance(history[-1], dict) else None
    if not last:
        return False
    last_ts_text = str(last.get("ts") or "")
    if not last_ts_text:
        return False
    try:
        last_ts = datetime.fromisoformat(last_ts_text).timestamp()
    except ValueError:
        return False
    script_path = experiment.get("script_path")
    candidates: list[Path] = []
    if isinstance(script_path, str) and script_path:
        candidates.append(repo_root / script_path)
    if experiments_registry.exists():
        candidates.append(experiments_registry)
    for path in candidates:
        try:
            mtime = path.stat().st_mtime
        except OSError:
            continue
        if mtime > last_ts + 0.5:
            return True
    return False


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
        experiment_id = str(claim.get("experiment_id") or "")
        experiment = experiment_by_id.get(experiment_id)
        if status not in {"open", "needs_rerun"}:
            if status in {"failed", "error"} and experiment is not None and _experiment_changed_since_last_history(claim, experiment, repo_root, store.paths.experiments_registry):
                claim["status"] = "needs_rerun"
                status = "needs_rerun"
                history = claim.setdefault("history", [])
                if isinstance(history, list):
                    history.append(_history_entry("needs_rerun", "experiment script or acceptance changed since last run"))
            else:
                continue
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


def _load_keep_lane_config() -> dict[str, Any]:
    data = json.loads(PIPELINE_CONFIG.read_text(encoding="utf-8"))
    if not isinstance(data, dict):
        return {}
    config = data.get("keep_lane")
    return config if isinstance(config, dict) else {}


def _load_sync_lane_config() -> dict[str, Any]:
    data = json.loads(PIPELINE_CONFIG.read_text(encoding="utf-8"))
    if not isinstance(data, dict):
        return {}
    config = data.get("sync_lane")
    return config if isinstance(config, dict) else {}


def _run_command(repo_root: Path, cmd: list[str], *, timeout: float = 60.0) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        cmd,
        cwd=repo_root,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        timeout=timeout,
        check=False,
    )


def _append_sync_log(store: BioRealityStore, event: str, details: dict[str, Any]) -> None:
    record = {"ts": now_iso(), "event": event, "details": details}
    try:
        store.paths.sync_lane_log.parent.mkdir(parents=True, exist_ok=True)
        with store.paths.sync_lane_log.open("a", encoding="utf-8") as handle:
            handle.write(json.dumps(record, ensure_ascii=False, sort_keys=True) + "\n")
    except OSError:
        return


def _append_keep_log(store: BioRealityStore, event: str, details: dict[str, Any]) -> None:
    record = {"ts": now_iso(), "event": event, "details": details}
    try:
        store.paths.keep_lane_log.parent.mkdir(parents=True, exist_ok=True)
        with store.paths.keep_lane_log.open("a", encoding="utf-8") as handle:
            handle.write(json.dumps(record, ensure_ascii=False, sort_keys=True) + "\n")
    except OSError:
        return


def _write_sync_state(store: BioRealityStore, state: dict[str, Any]) -> None:
    store.paths.sync_lane_state.parent.mkdir(parents=True, exist_ok=True)
    store.paths.sync_lane_state.write_text(json.dumps(state, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _sync_commit_range(last_synced_sha: str, remote: str, branch: str) -> str:
    compare_ref = f"{remote}/{branch}"
    return f"{last_synced_sha}..{compare_ref}" if last_synced_sha else f"HEAD..{compare_ref}"


def _parse_sync_git_log(output: str) -> list[dict[str, Any]]:
    commits: list[dict[str, Any]] = []
    current: dict[str, Any] | None = None
    for raw_line in output.splitlines():
        line = raw_line.strip()
        if not line:
            continue
        maybe_sha, sep, subject = line.partition("|")
        if sep and len(maybe_sha) == 40 and all(char in "0123456789abcdefABCDEF" for char in maybe_sha):
            current = {"sha": maybe_sha, "subject": subject, "files": []}
            commits.append(current)
            continue
        if current is not None:
            files = current.setdefault("files", [])
            if isinstance(files, list):
                files.append(line)
    return commits


def _sync_match_commit(
    commit: dict[str, Any],
    keywords: list[str],
    path_prefixes: list[str],
) -> dict[str, Any] | None:
    files = [str(item) for item in commit.get("files", []) if isinstance(item, str)]
    lowered_keywords = [(keyword, keyword.lower()) for keyword in keywords if keyword]
    matched_keywords: list[str] = []
    matched_paths: list[str] = []
    for path in files:
        path_lower = path.lower()
        for original, lowered in lowered_keywords:
            if lowered in path_lower and original not in matched_keywords:
                matched_keywords.append(original)
        for prefix in path_prefixes:
            if path.startswith(prefix) or fnmatch.fnmatch(path, f"{prefix}*"):
                if prefix not in matched_paths:
                    matched_paths.append(prefix)
    if not matched_keywords and not matched_paths:
        return None
    return {
        "ts": now_iso(),
        "loning_commit_sha": str(commit.get("sha") or ""),
        "subject": str(commit.get("subject") or ""),
        "files_changed": files,
        "matched_keywords": matched_keywords,
        "matched_paths": matched_paths,
    }


def _sync_intelligence_records(
    commits: list[dict[str, Any]],
    keywords: list[str],
    path_prefixes: list[str],
) -> list[dict[str, Any]]:
    records: list[dict[str, Any]] = []
    for commit in commits:
        record = _sync_match_commit(commit, keywords, path_prefixes)
        if record is not None:
            records.append(record)
    return records


def _git_status_porcelain(repo_root: Path) -> list[tuple[str, str]]:
    result = _run_command(repo_root, ["git", "status", "--porcelain"])
    if result.returncode != 0:
        raise RuntimeError((result.stderr or result.stdout or "git status failed").strip())
    changed: list[tuple[str, str]] = []
    for line in result.stdout.splitlines():
        if len(line) < 4:
            continue
        status_code = line[:2]
        path = line[3:]
        if " -> " in path:
            path = path.rsplit(" -> ", 1)[1]
        if path:
            changed.append((status_code, path))
    return changed


def _filter_paths(
    changed: list[tuple[str, str]],
    include_paths: list[str],
    exclude_paths: list[str],
) -> tuple[list[str], list[str]]:
    selected: list[str] = []
    dropped: list[str] = []
    seen: set[str] = set()
    for _status_code, path in changed:
        included = any(fnmatch.fnmatch(path, pattern) for pattern in include_paths)
        excluded = any(fnmatch.fnmatch(path, pattern) for pattern in exclude_paths)
        if included and not excluded:
            if path not in seen:
                selected.append(path)
                seen.add(path)
        else:
            dropped.append(path)
    return selected, dropped


def _read_json_object(path: Path) -> dict[str, Any]:
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return {}
    return data if isinstance(data, dict) else {}


def _rev_list_ahead_behind(repo_root: Path, compare_ref: str) -> tuple[int, int]:
    counts = _run_command(repo_root, ["git", "rev-list", "--left-right", "--count", f"HEAD...{compare_ref}"], timeout=60.0)
    if counts.returncode != 0:
        raise RuntimeError((counts.stderr or counts.stdout or "git rev-list failed").strip())
    parts = counts.stdout.strip().split()
    if len(parts) != 2:
        raise RuntimeError(f"unexpected rev-list output: {counts.stdout.strip()}")
    return int(parts[0]), int(parts[1])


def run_sync_lane(store: BioRealityStore) -> dict[str, Any]:
    """Fetch origin/auto-dev, extract Loning's recent biology-related work, attempt fast-forward / no-ff merge."""
    try:
        config = _load_sync_lane_config()
    except (OSError, json.JSONDecodeError) as exc:
        _append_sync_log(store, "config_error", {"error": str(exc)})
        return {"lane": "bio-S", "error": "config_error"}
    if not config.get("enabled"):
        return {"lane": "bio-S", "skipped": "disabled"}

    state = _read_json_object(store.paths.sync_lane_state)
    now_ts = time.time()
    min_seconds = float(config.get("min_seconds_between_syncs") or 0.0)
    last_fetch_ts = float(state.get("last_fetch_ts") or 0.0)
    if last_fetch_ts and now_ts - last_fetch_ts < min_seconds:
        return {"lane": "bio-S", "skipped": "throttled", "age_seconds": round(now_ts - last_fetch_ts, 3)}

    repo_root = SCRIPT_DIR.parent.parent
    remote = str(config.get("remote") or "origin")
    branch = str(config.get("upstream_branch") or "auto-dev")
    compare_ref = f"{remote}/{branch}"
    fetch_timeout = float(config.get("fetch_timeout_seconds") or 60.0)
    max_commits = max(1, int(config.get("max_commits_per_sync") or 50))
    last_synced_sha = str(state.get("last_synced_sha") or "")

    try:
        fetch = _run_command(repo_root, ["git", "fetch", remote, branch], timeout=fetch_timeout)
    except (OSError, subprocess.TimeoutExpired) as exc:
        _append_sync_log(store, "fetch_failed", {"remote": remote, "branch": branch, "error": str(exc)})
        return {"lane": "bio-S", "error": "fetch_failed", "detail": str(exc)}
    if fetch.returncode != 0:
        detail = (fetch.stderr or fetch.stdout or "git fetch failed").strip()
        _append_sync_log(store, "fetch_failed", {"remote": remote, "branch": branch, "returncode": fetch.returncode, "detail": detail[-2000:]})
        return {"lane": "bio-S", "error": "fetch_failed", "detail": detail[-500:]}

    try:
        rev_parse = _run_command(repo_root, ["git", "rev-parse", compare_ref], timeout=30.0)
    except (OSError, subprocess.TimeoutExpired) as exc:
        _append_sync_log(store, "rev_parse_failed", {"ref": compare_ref, "error": str(exc)})
        return {"lane": "bio-S", "error": "rev_parse_failed", "detail": str(exc)}
    if rev_parse.returncode != 0:
        detail = (rev_parse.stderr or rev_parse.stdout or "git rev-parse failed").strip()
        _append_sync_log(store, "rev_parse_failed", {"ref": compare_ref, "returncode": rev_parse.returncode, "detail": detail[-2000:]})
        return {"lane": "bio-S", "error": "rev_parse_failed", "detail": detail[-500:]}
    upstream_sha = rev_parse.stdout.strip()

    working_tree_clean = False
    try:
        working_tree_clean = not _git_status_porcelain(repo_root)
    except (OSError, RuntimeError) as exc:
        _append_sync_log(store, "git_status_error", {"error": str(exc)})

    if upstream_sha == last_synced_sha and working_tree_clean:
        new_state = dict(state)
        new_state.update({"last_fetch_ts": now_ts, "last_synced_sha": upstream_sha, "last_intelligence_count": 0})
        try:
            _write_sync_state(store, new_state)
        except OSError as exc:
            _append_sync_log(store, "state_write_failed", {"error": str(exc), "upstream_sha": upstream_sha})
        return {"lane": "bio-S", "skipped": "already current", "last_synced_sha": upstream_sha}

    ahead_before_sync = 0
    behind_before_sync = 0
    try:
        ahead_before_sync, behind_before_sync = _rev_list_ahead_behind(repo_root, compare_ref)
    except (OSError, RuntimeError, ValueError) as exc:
        _append_sync_log(store, "rev_list_failed", {"ref": compare_ref, "error": str(exc)})

    commit_range = _sync_commit_range(last_synced_sha, remote, branch)
    try:
        log_result = _run_command(
            repo_root,
            ["git", "log", f"-n{max_commits}", "--name-only", "--format=%H|%s", commit_range],
            timeout=60.0,
        )
    except (OSError, subprocess.TimeoutExpired) as exc:
        _append_sync_log(store, "git_log_failed", {"range": commit_range, "error": str(exc)})
        commits: list[dict[str, Any]] = []
    else:
        if log_result.returncode == 0:
            commits = _parse_sync_git_log(log_result.stdout)
        else:
            detail = (log_result.stderr or log_result.stdout or "git log failed").strip()
            _append_sync_log(store, "git_log_failed", {"range": commit_range, "returncode": log_result.returncode, "detail": detail[-2000:]})
            commits = []

    keywords = [str(item) for item in config.get("intelligence_keywords", []) if isinstance(item, str)]
    path_prefixes = [str(item) for item in config.get("intelligence_paths", []) if isinstance(item, str)]
    records = _sync_intelligence_records(commits, keywords, path_prefixes)
    try:
        append_jsonl(store.paths.loning_intelligence, records)
    except OSError as exc:
        _append_sync_log(store, "intelligence_write_failed", {"error": str(exc), "records": len(records)})
        records = []

    merge_attempted = False
    merge_status = "skipped"
    merge_sha = ""
    if behind_before_sync > 0:
        merge_attempted = True
        try:
            merge = _run_command(repo_root, ["git", "merge", "--no-ff", "-m", f"Sync auto-dev {upstream_sha[:12]}", compare_ref], timeout=300.0)
        except (OSError, subprocess.TimeoutExpired) as exc:
            merge_status = "conflict_aborted"
            _append_sync_log(store, "merge_error", {"ref": compare_ref, "error": str(exc)})
            try:
                _run_command(repo_root, ["git", "merge", "--abort"], timeout=60.0)
            except (OSError, subprocess.TimeoutExpired) as abort_exc:
                _append_sync_log(store, "merge_abort_failed", {"error": str(abort_exc)})
        else:
            if merge.returncode == 0:
                merge_status = "ok"
                try:
                    head = _run_command(repo_root, ["git", "rev-parse", "HEAD"], timeout=30.0)
                    merge_sha = head.stdout.strip() if head.returncode == 0 else ""
                except (OSError, subprocess.TimeoutExpired):
                    merge_sha = ""
                _append_sync_log(store, "merge_ok", {"ref": compare_ref, "merge_sha": merge_sha, "upstream_sha": upstream_sha})
            else:
                merge_status = "conflict_aborted"
                detail = (merge.stderr or merge.stdout or "git merge failed").strip()
                _append_sync_log(store, "merge_conflict_aborted", {"ref": compare_ref, "returncode": merge.returncode, "detail": detail[-2000:]})
                abort = _run_command(repo_root, ["git", "merge", "--abort"], timeout=60.0)
                if abort.returncode != 0:
                    abort_detail = (abort.stderr or abort.stdout or "git merge --abort failed").strip()
                    _append_sync_log(store, "merge_abort_failed", {"returncode": abort.returncode, "detail": abort_detail[-2000:]})

    new_state = dict(state)
    new_state.update(
        {
            "last_fetch_ts": now_ts,
            "last_synced_sha": upstream_sha,
            "last_intelligence_count": len(records),
        }
    )
    if merge_sha:
        new_state["last_merge_sha"] = merge_sha
    try:
        _write_sync_state(store, new_state)
    except OSError as exc:
        _append_sync_log(store, "state_write_failed", {"error": str(exc), "upstream_sha": upstream_sha})

    return {
        "lane": "bio-S",
        "fetched": True,
        "behind_before_sync": behind_before_sync,
        "ahead_before_sync": ahead_before_sync,
        "interesting_commits": len(records),
        "intelligence_records_appended": len(records),
        "merge_attempted": merge_attempted,
        "merge_status": merge_status,
        "merge_sha": merge_sha,
        "last_synced_sha": upstream_sha,
    }


def _keep_lane_recently_pushed(store: BioRealityStore, min_seconds: float) -> tuple[bool, float]:
    state = _read_json_object(store.paths.keep_lane_state)
    last_push_ts = float(state.get("last_push_ts") or 0.0)
    age = time.time() - last_push_ts if last_push_ts else min_seconds + 1.0
    return last_push_ts > 0 and age < min_seconds, age


def _run_keep_gates(store: BioRealityStore, repo_root: Path, gates: list[Any]) -> tuple[bool, list[str] | None]:
    for gate in gates:
        if not isinstance(gate, list) or not all(isinstance(item, str) for item in gate):
            _append_keep_log(store, "gate_invalid", {"gate": gate})
            return False, [str(gate)]
        try:
            result = _run_command(repo_root, gate, timeout=60.0)
        except (OSError, subprocess.TimeoutExpired) as exc:
            _append_keep_log(store, "gate_error", {"gate": gate, "error": str(exc)})
            return False, gate
        if result.returncode != 0:
            _append_keep_log(
                store,
                "gate_failure",
                {
                    "gate": gate,
                    "returncode": result.returncode,
                    "stdout_tail": result.stdout[-2000:],
                    "stderr_tail": result.stderr[-2000:],
                },
            )
            return False, gate
    return True, None


def _remote_behind_count(repo_root: Path, remote: str, branch: str) -> int:
    fetch = _run_command(repo_root, ["git", "fetch", remote, branch], timeout=60.0)
    if fetch.returncode != 0:
        raise RuntimeError((fetch.stderr or fetch.stdout or "git fetch failed").strip())
    compare_ref = f"{remote}/{branch}"
    counts = _run_command(repo_root, ["git", "rev-list", "--left-right", "--count", f"HEAD...{compare_ref}"], timeout=60.0)
    if counts.returncode != 0:
        raise RuntimeError((counts.stderr or counts.stdout or "git rev-list failed").strip())
    parts = counts.stdout.strip().split()
    if len(parts) != 2:
        raise RuntimeError(f"unexpected rev-list output: {counts.stdout.strip()}")
    return int(parts[1])


def _keep_lane_commit_message(store: BioRealityStore, selected: list[str]) -> str:
    loop_state = _read_json_object(store.paths.root / "state" / "loop_state.json")
    loops = loop_state.get("loops") if isinstance(loop_state.get("loops"), dict) else {}
    bio_x = loops.get("bio_X_execute_experiments", {}) if isinstance(loops, dict) else {}
    bio_x_summary = bio_x.get("last_summary") if isinstance(bio_x, dict) and isinstance(bio_x.get("last_summary"), dict) else {}
    claims = _load_claims_document(store.paths.claims_registry).get("claims", [])
    claim_states = _claim_state_counts([item for item in claims if isinstance(item, dict)]) if isinstance(claims, list) else {}
    title = f"BioReality cycle {now_iso()}: {len(selected)} file(s)"
    body = [
        "",
        "Selected files:",
        *[f"- {path}" for path in selected],
        "",
        f"loop_last_attempt_ts: {bio_x.get('last_attempt_ts') if isinstance(bio_x, dict) else ''}",
        f"claim_states: {json.dumps(claim_states, sort_keys=True)}",
        "bio_X: "
        + json.dumps(
            {
                "executed": bio_x_summary.get("executed", 0),
                "passed_this_cycle": bio_x_summary.get("passed_this_cycle", 0),
                "failed_this_cycle": bio_x_summary.get("failed_this_cycle", 0),
            },
            sort_keys=True,
        ),
    ]
    return title + "\n" + "\n".join(body)


def run_keep_lane(store: BioRealityStore) -> dict[str, Any]:
    try:
        config = _load_keep_lane_config()
    except (OSError, json.JSONDecodeError) as exc:
        _append_keep_log(store, "config_error", {"error": str(exc)})
        return {"lane": "bio-K", "error": "config error"}
    if not config.get("enabled"):
        return {"lane": "bio-K", "skipped": "disabled"}

    repo_root = store.paths.root.parent.parent
    try:
        changed = _git_status_porcelain(repo_root)
    except (OSError, RuntimeError) as exc:
        _append_keep_log(store, "git_status_error", {"error": str(exc)})
        return {"lane": "bio-K", "error": "git status failed"}
    if not changed:
        return {"lane": "bio-K", "skipped": "no changes"}

    include_paths = [str(item) for item in config.get("include_paths", []) if isinstance(item, str)]
    exclude_paths = [str(item) for item in config.get("exclude_paths", []) if isinstance(item, str)]
    selected, dropped = _filter_paths(changed, include_paths, exclude_paths)
    if not selected:
        return {"lane": "bio-K", "skipped": "no useful changes", "dropped": len(dropped)}

    min_seconds = float(config.get("min_seconds_between_pushes") or 0.0)
    try:
        too_soon, age = _keep_lane_recently_pushed(store, min_seconds)
    except (OSError, ValueError) as exc:
        _append_keep_log(store, "state_read_error", {"error": str(exc)})
        return {"lane": "bio-K", "error": "state read failed"}
    if too_soon:
        return {"lane": "bio-K", "skipped": "recent push", "age_seconds": round(age, 3), "files": len(selected), "dropped": len(dropped)}

    gates = config.get("pre_commit_gates", [])
    ok, failed_gate = _run_keep_gates(store, repo_root, gates if isinstance(gates, list) else [])
    if not ok:
        return {"lane": "bio-K", "skipped": "gate failure", "failed_gate": failed_gate, "files": len(selected), "dropped": len(dropped)}

    remote = str(config.get("remote") or "origin")
    branch = str(config.get("branch") or "feat/bio-reality-deepening")
    try:
        behind = _remote_behind_count(repo_root, remote, branch)
    except (OSError, RuntimeError, ValueError) as exc:
        _append_keep_log(store, "remote_check_error", {"remote": remote, "branch": branch, "error": str(exc)})
        return {"lane": "bio-K", "error": "remote check failed", "files": len(selected), "dropped": len(dropped)}
    if behind > 0:
        _append_keep_log(store, "behind_remote", {"remote": remote, "branch": branch, "behind": behind, "selected": selected})
        return {"lane": "bio-K", "skipped": "behind remote", "behind": behind, "files": len(selected), "dropped": len(dropped)}

    try:
        add = _run_command(repo_root, ["git", "add", "--", *selected], timeout=60.0)
    except (OSError, subprocess.TimeoutExpired) as exc:
        _append_keep_log(store, "git_add_error", {"error": str(exc), "selected": selected})
        return {"lane": "bio-K", "error": "git add failed", "files": len(selected), "dropped": len(dropped)}
    if add.returncode != 0:
        _append_keep_log(store, "git_add_failure", {"returncode": add.returncode, "stderr": add.stderr[-2000:], "selected": selected})
        return {"lane": "bio-K", "error": "git add failed", "files": len(selected), "dropped": len(dropped)}

    message = _keep_lane_commit_message(store, selected)
    try:
        commit = _run_command(repo_root, ["git", "commit", "-m", message], timeout=60.0)
    except (OSError, subprocess.TimeoutExpired) as exc:
        _append_keep_log(store, "git_commit_error", {"error": str(exc), "selected": selected})
        return {"lane": "bio-K", "error": "git commit failed", "files": len(selected), "dropped": len(dropped)}
    if commit.returncode != 0:
        _append_keep_log(store, "git_commit_failure", {"returncode": commit.returncode, "stdout": commit.stdout[-2000:], "stderr": commit.stderr[-2000:]})
        return {"lane": "bio-K", "error": "git commit failed", "files": len(selected), "dropped": len(dropped)}

    try:
        sha_result = _run_command(repo_root, ["git", "rev-parse", "HEAD"], timeout=60.0)
        commit_sha = sha_result.stdout.strip() if sha_result.returncode == 0 else ""
    except (OSError, subprocess.TimeoutExpired):
        commit_sha = ""
    retries = int(config.get("max_push_retries") or 0)
    push_ok = False
    last_push_error = ""
    for attempt in range(retries + 1):
        try:
            push = _run_command(repo_root, ["git", "push", remote, f"HEAD:{branch}"], timeout=60.0)
        except (OSError, subprocess.TimeoutExpired) as exc:
            last_push_error = str(exc)
            push = None
        if push is None:
            if attempt < retries:
                time.sleep(float(2 ** attempt))
            continue
        if push.returncode == 0:
            push_ok = True
            break
        last_push_error = (push.stderr or push.stdout or "git push failed").strip()
        if attempt < retries:
            time.sleep(float(2 ** attempt))
    if not push_ok:
        _append_keep_log(store, "git_push_failure", {"remote": remote, "branch": branch, "error": last_push_error[-2000:], "commit_sha": commit_sha})
        return {"lane": "bio-K", "error": "git push failed", "files": len(selected), "dropped": len(dropped), "commit_sha": commit_sha}

    state = {"last_push_ts": time.time(), "last_commit_sha": commit_sha, "last_pushed_files": selected}
    try:
        store.paths.keep_lane_state.parent.mkdir(parents=True, exist_ok=True)
        store.paths.keep_lane_state.write_text(json.dumps(state, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    except OSError as exc:
        _append_keep_log(store, "state_write_error", {"error": str(exc), "commit_sha": commit_sha})
        return {"lane": "bio-K", "error": "state write failed", "files": len(selected), "dropped": len(dropped), "commit_sha": commit_sha, "pushed": True}
    return {"lane": "bio-K", "committed": True, "files": len(selected), "dropped": len(dropped), "commit_sha": commit_sha, "pushed": True}


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
        sync_lane_state=base / "sync_lane.json",
        sync_lane_log=base / "sync_lane.log",
        loning_intelligence=base / "loning_intelligence.jsonl",
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
        disabled_config_path = base / "disabled_pipeline_config.json"
        disabled_config_path.write_text(json.dumps({"sync_lane": {"enabled": False}}, indent=2), encoding="utf-8")
        original_pipeline_config = PIPELINE_CONFIG
        globals()["PIPELINE_CONFIG"] = disabled_config_path
        try:
            disabled_summary = run_sync_lane(BioRealityStore(paths))
        finally:
            globals()["PIPELINE_CONFIG"] = original_pipeline_config
        if disabled_summary != {"lane": "bio-S", "skipped": "disabled"}:
            print(json.dumps(disabled_summary, indent=2), file=sys.stderr)
            return 1

        log_output = "\n".join(
            [
                "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa|Add codon science note",
                "papers/bedc/parts/visions/philosophy/science/codon_window.tex",
                "lean4/BEDC/Derived/Genetic/StopCodon.lean",
                "",
                "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb|Adjust unrelated prose",
                "docs/roadmap.txt",
                "",
                "cccccccccccccccccccccccccccccccccccccccc|Protein path only",
                "papers/bedc/parts/concrete_instances/protein/namecert_construction.tex",
            ]
        )
        parsed_commits = _parse_sync_git_log(log_output)
        if len(parsed_commits) != 3 or parsed_commits[0]["files"] != [
            "papers/bedc/parts/visions/philosophy/science/codon_window.tex",
            "lean4/BEDC/Derived/Genetic/StopCodon.lean",
        ]:
            print(json.dumps(parsed_commits, indent=2), file=sys.stderr)
            return 1
        records = _sync_intelligence_records(
            parsed_commits,
            ["codon", "genetic", "amino", "bio", "protein", "dna", "rna", "translation", "ribosom", "nucleotide", "tRNA"],
            [
                "papers/bedc/parts/visions/philosophy/science/",
                "papers/bedc/parts/concrete_instances/",
                "lean4/BEDC/Derived/",
            ],
        )
        if len(records) != 2:
            print(json.dumps(records, indent=2), file=sys.stderr)
            return 1
        first_record = records[0]
        if first_record["loning_commit_sha"] != "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa":
            print(json.dumps(first_record, indent=2), file=sys.stderr)
            return 1
        if "codon" not in first_record["matched_keywords"] or "genetic" not in first_record["matched_keywords"]:
            print(json.dumps(first_record, indent=2), file=sys.stderr)
            return 1
        if "papers/bedc/parts/visions/philosophy/science/" not in first_record["matched_paths"]:
            print(json.dumps(first_record, indent=2), file=sys.stderr)
            return 1

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
        keep_config = _load_keep_lane_config()
        if keep_config.get("enabled") is not True:
            print(json.dumps(keep_config, indent=2), file=sys.stderr)
            return 1
        keep_selected, keep_dropped = _filter_paths(
            [
                (" M", "tools/bio_reality/state/foo.jsonl"),
                (" M", "tools/bio_reality/experiments/run_X.py"),
                ("??", "tools/bio_reality/vision/index.md"),
            ],
            [str(item) for item in keep_config.get("include_paths", []) if isinstance(item, str)],
            [str(item) for item in keep_config.get("exclude_paths", []) if isinstance(item, str)],
        )
        if keep_selected != ["tools/bio_reality/experiments/run_X.py"]:
            print(json.dumps({"selected": keep_selected, "dropped": keep_dropped}, indent=2), file=sys.stderr)
            return 1
        if "tools/bio_reality/state/foo.jsonl" not in keep_dropped:
            print(json.dumps({"selected": keep_selected, "dropped": keep_dropped}, indent=2), file=sys.stderr)
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

        plan_phase_paths = _temp_paths(base / "plan_phase")
        plan_phase_paths.claims_registry.parent.mkdir(parents=True, exist_ok=True)
        plan_phase_paths.claims_registry.write_text(
            json.dumps(
                {
                    "version": "bio-reality-claims-v1",
                    "claims": [
                        {"claim_id": "phase.one.a", "hypothesis_level": "H0", "phase": 1, "status": "passed"},
                        {"claim_id": "phase.one.b", "hypothesis_level": "H1", "phase": 1, "status": "passed"},
                        {"claim_id": "phase.one.c", "hypothesis_level": "H2", "phase": 1, "status": "passed"},
                        {"claim_id": "self.claim", "hypothesis_level": "meta", "phase": 1, "status": "open"},
                    ],
                },
                indent=2,
            ),
            encoding="utf-8",
        )
        plan_phase_paths.experiments_registry.parent.mkdir(parents=True, exist_ok=True)
        plan_phase_paths.experiments_registry.write_text(
            json.dumps({"version": "bio-reality-experiments-v1", "experiments": []}, indent=2),
            encoding="utf-8",
        )
        plan_phase_store = BioRealityStore(plan_phase_paths)
        plan_phase_summary = run_plan_lane(plan_phase_store)
        plan_phase_events = plan_phase_store.load_events()
        if plan_phase_summary["phase_advance_events"] != 1:
            print(json.dumps({"summary": plan_phase_summary, "events": plan_phase_events}, indent=2), file=sys.stderr)
            return 1
        if not any(event.get("event_kind") == "phase_advance_proposed" and event.get("subject_id") == "1" for event in plan_phase_events):
            print(json.dumps(plan_phase_events, indent=2), file=sys.stderr)
            return 1
        plan_phase_repeat = run_plan_lane(plan_phase_store)
        if plan_phase_repeat["phase_advance_events"] != 0:
            print(json.dumps({"summary": plan_phase_repeat, "events": plan_phase_store.load_events()}, indent=2), file=sys.stderr)
            return 1

        stuck_paths = _temp_paths(base / "plan_stuck")
        stuck_paths.claims_registry.parent.mkdir(parents=True, exist_ok=True)
        stuck_paths.claims_registry.write_text(
            json.dumps(
                {
                    "version": "bio-reality-claims-v1",
                    "claims": [
                        {
                            "claim_id": "stuck.claim",
                            "hypothesis_level": "H1",
                            "phase": 1,
                            "status": "failed",
                            "experiment_id": "x",
                        }
                    ],
                },
                indent=2,
            ),
            encoding="utf-8",
        )
        stuck_paths.experiments_registry.parent.mkdir(parents=True, exist_ok=True)
        stuck_paths.experiments_registry.write_text(
            json.dumps(
                {
                    "version": "bio-reality-experiments-v1",
                    "experiments": [{"experiment_id": "x", "claim_id": "stuck.claim"}],
                },
                indent=2,
            ),
            encoding="utf-8",
        )
        write_jsonl(
            stuck_paths.experiment_runs,
            [
                {
                    "experiment_id": "x",
                    "claim_id": "stuck.claim",
                    "status": "failed",
                    "checks": [{"name": "check_y", "passed": False}],
                    "completed_at": "2026-05-25T00:00:01+00:00",
                },
                {
                    "experiment_id": "x",
                    "claim_id": "stuck.claim",
                    "status": "failed",
                    "checks": [{"name": "check_y", "passed": False}],
                    "completed_at": "2026-05-25T00:00:02+00:00",
                },
                {
                    "experiment_id": "x",
                    "claim_id": "stuck.claim",
                    "status": "failed",
                    "checks": [{"name": "check_y", "passed": False}],
                    "completed_at": "2026-05-25T00:00:03+00:00",
                },
            ],
        )
        stuck_store = BioRealityStore(stuck_paths)
        stuck_summary = run_plan_lane(stuck_store)
        stuck_events = stuck_store.load_events()
        if stuck_summary["stuck_redesign_events"] != 1:
            print(json.dumps({"summary": stuck_summary, "events": stuck_events}, indent=2), file=sys.stderr)
            return 1
        if not any(event.get("event_kind") == "claim_redesign_proposed" and event.get("subject_id") == "x" for event in stuck_events):
            print(json.dumps(stuck_events, indent=2), file=sys.stderr)
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
