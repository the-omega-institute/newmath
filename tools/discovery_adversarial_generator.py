#!/usr/bin/env python3
"""Red-team the positive discovery gate with sound reconstruction pseudos."""

from __future__ import annotations

import argparse
import contextlib
import fcntl
import importlib.util
import json
import os
import sys
import time
from datetime import datetime
from pathlib import Path
from typing import Any

REPO_ROOT = Path(__file__).resolve().parent.parent
BEDC_CI_PATH = REPO_ROOT / "lean4" / "scripts" / "bedc_ci.py"
LOG_DIR = REPO_ROOT / "tools" / "logs"
DEFAULT_OUTPUT = LOG_DIR / "proven_pseudos.jsonl"
DEFAULT_LOG = LOG_DIR / "discovery_adversarial_generator.log"
PID_LOCK_PATH = Path("/tmp/.bedc_discovery_adversarial_generator.pid")
DEFAULT_INTERVAL = 21600
DEFAULT_MAX_NEW_PER_BUCKET = 1
DEFAULT_MAX_RECORDS_PER_CYCLE = 50
REGISTRY_NEAR_CAP_FRACTION = 0.95

_BEDC_CI = None


class FailClosed(RuntimeError):
    pass


def bedc_ci_module():
    global _BEDC_CI
    if _BEDC_CI is None:
        spec = importlib.util.spec_from_file_location("bedc_ci_for_adversarial_generator", BEDC_CI_PATH)
        if spec is None or spec.loader is None:
            raise RuntimeError(f"cannot load {BEDC_CI_PATH}")
        module = importlib.util.module_from_spec(spec)
        sys.modules[spec.name] = module
        spec.loader.exec_module(module)
        _BEDC_CI = module
    return _BEDC_CI


def now_iso() -> str:
    return datetime.now().isoformat(timespec="seconds")


def append_log(message: str, *, log_path: Path = DEFAULT_LOG) -> None:
    log_path.parent.mkdir(parents=True, exist_ok=True)
    with log_path.open("a", encoding="utf-8") as handle:
        handle.write(f"{now_iso()} {message}\n")


@contextlib.contextmanager
def pid_lock():
    pid_fd = os.open(PID_LOCK_PATH, os.O_RDWR | os.O_CREAT, 0o644)
    try:
        try:
            fcntl.flock(pid_fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            sys.stderr.write(f"discovery adversarial generator already running ({PID_LOCK_PATH})\n")
            sys.exit(1)
        os.ftruncate(pid_fd, 0)
        os.write(pid_fd, f"{os.getpid()}\n".encode())
        os.fsync(pid_fd)
        yield
    finally:
        try:
            fcntl.flock(pid_fd, fcntl.LOCK_UN)
        except Exception:
            pass
        os.close(pid_fd)


def load_jsonl(path: Path) -> list[dict[str, Any]]:
    if not path.exists():
        return []
    records: list[dict[str, Any]] = []
    for raw in path.read_text(encoding="utf-8").splitlines():
        raw = raw.strip()
        if not raw:
            continue
        try:
            item = json.loads(raw)
        except json.JSONDecodeError:
            continue
        if isinstance(item, dict):
            records.append(item)
    return records


def pseudo_key(record: dict[str, Any]) -> tuple[str, str, str]:
    pattern = record.get("pattern") if isinstance(record.get("pattern"), dict) else {}
    target = str(pattern.get("target") or record.get("candidate") or record.get("target") or "").strip()
    prior = str(pattern.get("prior") or record.get("prior") or "").strip()
    canonical_payload = str(
        pattern.get("canonical_payload")
        or record.get("canonical_payload")
        or record.get("candidate_canonical_payload")
        or ""
    ).strip()
    return target, prior, canonical_payload


def load_registry_keys() -> tuple[set[tuple[str, str]], int, int]:
    ci = bedc_ci_module()
    witnesses, diagnostics = ci.load_discovery_gate_witnesses()
    if diagnostics:
        raise RuntimeError(
            "discovery gate witness registry diagnostics are blocking for generator: "
            + json.dumps(diagnostics[:5], ensure_ascii=False, sort_keys=True)
        )
    keys: set[tuple[str, str]] = set()
    for witness in witnesses:
        pattern = witness.get("pattern") if isinstance(witness.get("pattern"), dict) else {}
        prior = str(pattern.get("prior") or "").strip()
        payload = str(pattern.get("canonical_payload") or "").strip()
        if prior and payload:
            keys.add((prior, payload))
    cap = int(getattr(ci, "DISCOVERY_GATE_WITNESS_MAX_ENTRIES"))
    return keys, len(witnesses), cap


def positive_discovery_assertion_target(lean_scan: Any) -> tuple[str, list[str]]:
    ci = bedc_ci_module()
    symbol_kinds = ci._symbol_kind_map(lean_scan.declarations)
    candidates: list[tuple[str, int, str]] = []
    for target, header in lean_scan.declaration_headers.items():
        evidence_kind = ci._positive_discovery_evidence_kind(target, symbol_kinds, lean_scan.declaration_headers)
        if not evidence_kind:
            continue
        supports = [
            support
            for support in ci._disagreement_support_declarations(
                target,
                lean_scan.declaration_headers,
                lean_scan.declaration_bodies,
            )
            if ci._support_disagreement_assignment_reaches_target(
                support,
                target,
                lean_scan.declaration_headers,
                lean_scan.declaration_bodies,
            )
        ]
        candidates.append((target, len(supports), supports[0] if supports else ""))
    candidates.sort(key=lambda item: (-item[1], item[0]))
    for target, _support_count, support in candidates:
        if support:
            return target, [support]
    return "", []


def classifier_payload_buckets(lean_scan: Any, cap: int) -> list[dict[str, Any]]:
    ci = bedc_ci_module()
    classifier_names = ci._classifier_endpoint_names(lean_scan.declaration_headers)[:cap]
    expr_fps = ci._run_structural_dna_expr_fingerprints(classifier_names) if classifier_names else {}
    buckets: dict[str, list[str]] = {}
    reduced_fps: dict[str, str] = {}
    for name in classifier_names:
        payload = ci._discovery_endpoint_canonical_payload(name, expr_fps)
        if not payload:
            continue
        buckets.setdefault(payload, []).append(name)
        reduced_fps[name] = ci._discovery_endpoint_reduced_fp(name, expr_fps)
    out: list[dict[str, Any]] = []
    for payload, names in sorted(buckets.items(), key=lambda item: (item[0], item[1])):
        if len(names) < 2:
            continue
        ordered = sorted(names)
        out.append({
            "canonical_payload": payload,
            "names": ordered,
            "reduced_fps": {name: reduced_fps.get(name, "") for name in ordered},
        })
    return out


def synthetic_block(assertion_target: str) -> dict[str, Any]:
    return {
        "file": "tools/logs/discovery_adversarial_generator.synthetic",
        "line": 1,
        "region": "DiscoveryAdversarialGenerator",
        "theory_closure": "scopedClosure",
        "formal_status": "theoremCheckedV",
        "lean_target": assertion_target,
        "bridge_status": "none",
        "origin": "ai",
        "scopeclosed": "synthetic in-memory red-team assertion over a real BEDC declaration",
        "raw_body": "",
        "open_fields": {
            "closureclaimkind": "positiveDiscovery",
            "closuregate": assertion_target,
            "closureclassifierincrement": "1",
            "closureweightprofile": "synthetic red-team weight profile",
            "closureparents": "synthetic red-team parent",
        },
        "has_scope": True,
        "has_notclaimed": True,
        "has_upgradepath": True,
        "has_constructive_story": True,
    }


def synthetic_integrity(
    block: dict[str, Any],
    *,
    candidate: str,
    prior: str,
    canonical_payload: str,
    candidate_reduced_fp: str,
    prior_reduced_fp: str,
) -> dict[str, Any]:
    provenance = {
        "candidate": candidate,
        "prior": prior,
        "relation": "reconstruction",
        "prior_scope": "adversarial_generator_canonical_payload_bucket",
        "candidate_reduced_fp": candidate_reduced_fp,
        "reduced_fp": prior_reduced_fp,
        "candidate_canonical_payload": canonical_payload,
        "prior_canonical_payload": canonical_payload,
        "canonical_payload": canonical_payload,
        "evidence": "canonical_payload_equal",
        "kernel_grounded": True,
        "soundness": "canonical_payload_equal",
    }
    site = {
        "file": block["file"],
        "line": block["line"],
        "region": f"{block['region']}Up",
        "chapter_key": "discovery_adversarial_generator",
        "claim_kind": "positiveDiscovery",
        "sources": ["adversarial_generator.synthetic_positiveDiscovery"],
        "ledger": "",
        "shift_refs": [],
        "before_classifiers": [prior],
        "declared_new_classifiers": [candidate],
        "parse_notes": [],
        "resolution_status": "resolved",
        "semantics": "synthetic in-memory adversarial site; no paper corpus write",
        "provenance": [provenance],
    }
    return {
        "schema": "bedc.discovery_integrity.structural_reconstruction",
        "semantics": "synthetic in-memory adversarial site; soundness from canonical payload equality",
        "gate": "blocking_for_declared_discovery_reconstruction",
        "declared_discovery_chapter_count": 1,
        "explicit_discovery_chapter_count": 1,
        "informational_discovery_chapter_count": 0,
        "checked_chapter_count": 1,
        "classifier_endpoint_count": 2,
        "fingerprint_count": 2,
        "unavailable_count": 0,
        "relation_diagnostics_count": 0,
        "unresolved_count": 0,
        "violation_count": 0,
        "violations": [],
        "sites": [site],
    }


def synthetic_sieve(
    block: dict[str, Any],
    *,
    assertion_target: str,
    support_targets: list[str],
) -> dict[str, Any]:
    return {
        "schema": "bedc.discovery_sieve",
        "targets": [{
            "target": assertion_target,
            "file": block["file"],
            "line": block["line"],
            "region": f"{block['region']}Up",
            "sources": ["adversarial_generator.synthetic_positiveDiscovery"],
            "grade": "certified_prime",
            "sieve_profile": {
                "reason_tags": [],
                "semantic_anchors": ["observable_endpoint"],
                "support_anchors": ["DisagreementSupport"],
                "support_targets": support_targets,
                "adversarial_input_targets": support_targets,
                "support_result_types": {},
                "support_reachable": support_targets,
                "public_semantic_endpoint": True,
                "suspicious_count": 0,
            },
            "negative_witnesses": [],
            "adversarial_witnesses": [],
            "adversarial_resistance_score": 1.0,
        }],
    }


def true_gate_passed(
    lean_scan: Any,
    *,
    assertion_target: str,
    support_targets: list[str],
    candidate: str,
    prior: str,
    canonical_payload: str,
    candidate_reduced_fp: str,
    prior_reduced_fp: str,
) -> tuple[bool, dict[str, Any]]:
    ci = bedc_ci_module()
    block = synthetic_block(assertion_target)
    payload = ci.discovery_assert_gate_payload(
        [block],
        lean_scan,
        synthetic_integrity(
            block,
            candidate=candidate,
            prior=prior,
            canonical_payload=canonical_payload,
            candidate_reduced_fp=candidate_reduced_fp,
            prior_reduced_fp=prior_reduced_fp,
        ),
        sieve_payload=synthetic_sieve(
            block,
            assertion_target=assertion_target,
            support_targets=support_targets,
        ),
    )
    sites = [site for site in payload.get("asserted_sites", []) if isinstance(site, dict)]
    passed = bool(sites and sites[0].get("status") == "PASS")
    return passed, payload


def grounded_canonical_refutation(
    *,
    candidate: str,
    prior: str,
    canonical_payload: str,
    reduced_fp: str,
) -> tuple[bool, dict[str, Any]]:
    ci = bedc_ci_module()
    witness = {
        "id": "adversarial-generator-probe",
        "kind": "reconstruction",
        "pattern": {
            "target": candidate,
            "prior": prior,
            "canonical_payload": canonical_payload,
            "reduced_fp": reduced_fp,
        },
        "soundness": "canonical_payload_equal",
    }
    return ci.discovery_gate_witness_kernel_grounding(witness)


def write_record(path: Path, record: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("a", encoding="utf-8") as handle:
        handle.write(json.dumps(record, ensure_ascii=False, sort_keys=True) + "\n")


def run_once(args: argparse.Namespace) -> int:
    ci = bedc_ci_module()
    covered_buckets, witness_count, witness_cap = load_registry_keys()
    if witness_count >= int(witness_cap * REGISTRY_NEAR_CAP_FRACTION):
        raise FailClosed(
            f"discovery gate witness registry near cap: {witness_count}/{witness_cap}; "
            "generator fails closed"
        )

    output = Path(args.output)
    already_emitted = {pseudo_key(record) for record in load_jsonl(output)}
    lean_scan = ci.scan_lean_sources()
    assertion_target, support_targets = positive_discovery_assertion_target(lean_scan)
    if not assertion_target or not support_targets:
        append_log("[heartbeat] no real PositiveDiscovery declaration with checked support target; emitted=0")
        return 0

    buckets = classifier_payload_buckets(lean_scan, int(args.classifier_cap))
    emitted = 0
    skipped_covered = 0
    skipped_budget = 0
    per_bucket_new: dict[tuple[str, str], int] = {}
    for bucket in buckets:
        canonical_payload = str(bucket["canonical_payload"])
        names = list(bucket["names"])
        prior = names[0]
        reduced_fps = bucket["reduced_fps"]
        for candidate in names[1:]:
            bucket_key = (prior, canonical_payload)
            if bucket_key in covered_buckets:
                skipped_covered += 1
                continue
            if per_bucket_new.get(bucket_key, 0) >= int(args.max_new_per_bucket):
                skipped_budget += 1
                continue
            record_key = (candidate, prior, canonical_payload)
            if record_key in already_emitted:
                continue
            if not canonical_payload:
                continue
            candidate_fp = str(reduced_fps.get(candidate) or "")
            prior_fp = str(reduced_fps.get(prior) or "")
            grounded, grounding = grounded_canonical_refutation(
                candidate=candidate,
                prior=prior,
                canonical_payload=canonical_payload,
                reduced_fp=candidate_fp if candidate_fp == prior_fp else "",
            )
            if not grounded:
                continue
            passed, gate_payload = true_gate_passed(
                lean_scan,
                assertion_target=assertion_target,
                support_targets=support_targets,
                candidate=candidate,
                prior=prior,
                canonical_payload=canonical_payload,
                candidate_reduced_fp=candidate_fp,
                prior_reduced_fp=prior_fp,
            )
            if not passed:
                continue
            record = {
                "schema": "bedc.discovery_adversarial_generator.proven_pseudo",
                "kind": "reconstruction",
                "relation": "reconstruction",
                "candidate": candidate,
                "target": candidate,
                "prior": prior,
                "canonical_payload": canonical_payload,
                "candidate_canonical_payload": canonical_payload,
                "prior_canonical_payload": canonical_payload,
                "candidate_reduced_fp": candidate_fp,
                "reduced_fp": prior_fp,
                "evidence": "canonical_payload_equal",
                "soundness": "canonical_payload_equal",
                "true_gate": "discovery_assert_gate_payload",
                "true_gate_status": "PASS",
                "assertion_target": assertion_target,
                "support_targets": support_targets,
                "regression_candidate": assertion_target,
                "pattern": {
                    "target": candidate,
                    "prior": prior,
                    "canonical_payload": canonical_payload,
                    **({"reduced_fp": candidate_fp} if candidate_fp and candidate_fp == prior_fp else {}),
                },
                "kernel_grounding": grounding,
                "refutes_because": (
                    "the real positiveDiscovery gate passed an in-memory assertion, "
                    "but structural-DNA canonical payload equality proves reconstruction"
                ),
                "provenance": {
                    "source": "tools/discovery_adversarial_generator.py",
                    "gate_schema": gate_payload.get("schema"),
                    "gate_rules": gate_payload.get("rules"),
                    "generated_at": now_iso(),
                },
            }
            write_record(output, record)
            already_emitted.add(record_key)
            per_bucket_new[bucket_key] = per_bucket_new.get(bucket_key, 0) + 1
            emitted += 1
            if emitted >= int(args.max_records):
                break
        if emitted >= int(args.max_records):
            break
    append_log(
        "[cycle] emitted="
        f"{emitted} dup_buckets_checked={len(buckets)} "
        f"skipped_covered={skipped_covered} skipped_budget={skipped_budget} "
        f"assertion_target={assertion_target}"
    )
    if emitted == 0:
        append_log("[heartbeat] no proven pseudos; current true gate/canonical payload coverage produced no sound adversarial hit")
    return 0


def parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(description="Generate sound proven pseudos for the discovery gate evolver")
    p.add_argument("--once", action="store_true", help="Run one cycle and exit")
    p.add_argument("--output", default=str(DEFAULT_OUTPUT), help="runtime JSONL output path")
    p.add_argument("--interval", type=int, default=DEFAULT_INTERVAL, help="loop sleep seconds")
    p.add_argument("--classifier-cap", type=int, default=2000, help="max classifier endpoints to fingerprint")
    p.add_argument("--max-new-per-bucket", type=int, default=DEFAULT_MAX_NEW_PER_BUCKET)
    p.add_argument("--max-records", type=int, default=DEFAULT_MAX_RECORDS_PER_CYCLE)
    return p


def main() -> int:
    args = parser().parse_args()
    with pid_lock():
        if args.once:
            try:
                return run_once(args)
            except FailClosed as exc:
                append_log(f"[fail-closed] {exc}")
                return 1
            except Exception as exc:
                append_log(f"[error] cycle failed: {type(exc).__name__}: {exc}")
                return 0
        while True:
            try:
                run_once(args)
            except FailClosed as exc:
                append_log(f"[fail-closed] {exc}")
            except Exception as exc:
                append_log(f"[error] cycle failed: {type(exc).__name__}: {exc}")
            time.sleep(max(1, int(args.interval)))


if __name__ == "__main__":
    raise SystemExit(main())
