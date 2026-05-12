#!/usr/bin/env python3
"""Promote gated Automath-to-NewMath bridge records into BEDC BOARD candidates.

This adapter deliberately reuses `tools/bedc-deep/board_spawn.py` instead of
hand-appending BOARD.md. The bridge only prepares durable review packets and
candidate dicts; BEDC's native fit, novelty, dedup, Claude judge, and atomic
append gates decide whether anything reaches the BOARD.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parent.parent
DEFAULT_GATE_RESULTS = SCRIPT_DIR / "out" / "bridge_gate_results.jsonl"
DEFAULT_PACKET_DIR = SCRIPT_DIR / "review_packets"
BEDC_DEEP_DIR = REPO_ROOT / "tools" / "bedc-deep"
BEDC_INBOX = BEDC_DEEP_DIR / "state" / "candidate_inbox.jsonl"
DEFAULT_LEDGER = REPO_ROOT / "docs" / "bridge" / "automath-board-continuation-ledger.md"
DEFAULT_ACK_LEDGER = REPO_ROOT / "docs" / "bridge" / "automath-newmath-ack.jsonl"
DEFAULT_STATUS_REPORT = REPO_ROOT / "docs" / "bridge" / "automath-newmath-production-status.md"
LEAN_DECL_RE = re.compile(r"^\s*(?:noncomputable\s+)?(?:def|theorem|lemma|abbrev)\s+([A-Za-z0-9_'.]+)", re.M)
LATEX_LABEL_RE = re.compile(r"\\label\{([^}]+)\}")


def _now_iso() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat()


def _read_jsonl(path: Path) -> list[dict[str, Any]]:
    if not path.exists():
        return []
    records: list[dict[str, Any]] = []
    with path.open("r", encoding="utf-8") as handle:
        for line_no, line in enumerate(handle, start=1):
            text = line.strip()
            if not text:
                continue
            data = json.loads(text)
            if not isinstance(data, dict):
                raise ValueError(f"{path}:{line_no}: expected object record")
            records.append(data)
    return records


def _bridge_candidate_history(limit: int = 5000) -> dict[str, dict[str, Any]]:
    """Return latest BEDC inbox event by title.

    BEDC board_spawn may rewrite the source field to `codex`, `both`, or
    `paper_review` after judging. The bridge still needs those final outcomes
    for its own candidate titles, so keep title history independent of source.
    """
    if not BEDC_INBOX.exists():
        return {}
    history: dict[str, dict[str, Any]] = {}
    lines = BEDC_INBOX.read_text(encoding="utf-8", errors="replace").splitlines()
    for line in lines[-limit:]:
        try:
            item = json.loads(line)
        except json.JSONDecodeError:
            continue
        if not isinstance(item, dict):
            continue
        title = str(item.get("title") or "").strip().lower()
        if title:
            history[title] = item
    return history


def _history_skip_reason(title: str, history: dict[str, dict[str, Any]]) -> str:
    item = history.get(title.strip().lower())
    if not item:
        return ""
    event = str(item.get("event") or "")
    reason = str(item.get("reason") or "")
    if event == "promoted_to_board":
        return f"already_promoted:{item.get('target_id')}"
    if event == "rejected" and reason:
        return f"history_rejected:{reason}"
    if event == "pre_gate_reject":
        if reason.startswith("duplicate_title"):
            return f"history_rejected:{reason}"
        if reason in {
            "missing_title",
            "missing_claim",
            "claim_too_short",
            "structural_title",
            "forbidden_axis_or_marker_candidate",
            "missing_local_inputs",
            "hub_only_landing",
            "no_indexed_safe_landing",
        }:
            return f"history_rejected:{reason}"
        if reason.startswith(("non_paper_local_input:", "missing_local_input:", "predicted_line_cap_overflow:", "predicted_label_collision:")):
            return f"history_rejected:{reason}"
    return ""


def _safe_slug(text: str, *, limit: int = 96) -> str:
    cleaned = "".join(ch.lower() if ch.isalnum() else "-" for ch in text)
    cleaned = "-".join(part for part in cleaned.split("-") if part)
    return cleaned[:limit].strip("-") or "bridge-record"


def _short_digest(record: dict[str, Any]) -> str:
    payload = json.dumps(
        {
            "artifact_key": record.get("artifact_key"),
            "source_commit": record.get("source_commit"),
            "source_path": record.get("source_path"),
        },
        sort_keys=True,
    )
    return hashlib.sha1(payload.encode("utf-8")).hexdigest()[:12]


def _packet_path(record: dict[str, Any], packet_dir: Path) -> Path:
    source_path = str(record.get("source_path") or record.get("id") or "bridge-record")
    slug = _safe_slug(source_path)
    return packet_dir / f"{slug}-{_short_digest(record)}.json"


def _write_packet(record: dict[str, Any], packet_dir: Path) -> Path:
    packet_dir.mkdir(parents=True, exist_ok=True)
    path = _packet_path(record, packet_dir)
    source_refs = _source_refs(record)
    mode = _bridge_consumption_mode(record)
    packet = {
        "schema_version": "automath-newmath-bridge-evidence-packet-v2",
        "created_at": _now_iso(),
        "status": "needs_bedc_board_review",
        "bridge_consumption_mode": mode,
        "source_repo": record.get("source_repo"),
        "source_branch_or_ref": record.get("source_branch_or_ref"),
        "source_commit": record.get("source_commit"),
        "source_path": record.get("source_path"),
        "source_artifact_kind": record.get("source_artifact_kind"),
        "source_theorem_names": source_refs["theorem_names"],
        "source_paper_labels": source_refs["paper_labels"],
        "source_paths": [record.get("source_path")],
        "destination_repo": record.get("destination_repo"),
        "destination_branch_or_ref": record.get("destination_branch_or_ref"),
        "destination_path": "tools/bedc-deep/BOARD.md",
        "destination_artifact_kind": "bedc_continuation_target",
        "bridge_direction": "automath_to_newmath",
        "reuse_instruction": _reuse_instruction(mode),
        "expected_newmath_delta": _expected_newmath_delta(record, mode),
        "reject_if": _reject_if(record, mode),
        "operator_review_required": True,
        "taste_gate_required": False,
        "audit_required": True,
        "gate_result": record,
        "non_actions": [
            "no direct BEDC paper write",
            "no direct BEDC Lean write",
            "no direct proposal acceptance",
            "no external publication",
            "no push from this adapter",
        ],
    }
    path.write_text(json.dumps(packet, ensure_ascii=False, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return path


def _source_repo_path(record: dict[str, Any]) -> Path | None:
    repo = str(record.get("source_repo") or "")
    if repo == "the-omega-institute/automath":
        return (REPO_ROOT.parent / "automath").resolve()
    if repo == "the-omega-institute/newmath":
        return REPO_ROOT
    return None


def _source_text(record: dict[str, Any], *, max_chars: int = 120000) -> str:
    repo_path = _source_repo_path(record)
    source_ref = str(record.get("source_branch_or_ref") or "HEAD")
    source_path = str(record.get("source_path") or "")
    if not repo_path or not source_path:
        return ""
    try:
        proc = subprocess.run(
            ["git", "-C", str(repo_path), "show", f"{source_ref}:{source_path}"],
            text=True,
            capture_output=True,
            timeout=30,
        )
    except (OSError, subprocess.TimeoutExpired):
        return ""
    if proc.returncode != 0:
        path = repo_path / source_path
        if path.exists():
            return path.read_text(encoding="utf-8", errors="replace")[:max_chars]
        return ""
    return proc.stdout[:max_chars]


def _source_refs(record: dict[str, Any]) -> dict[str, list[str]]:
    text = _source_text(record)
    theorem_names = LEAN_DECL_RE.findall(text)[:12] if text else []
    paper_labels = LATEX_LABEL_RE.findall(text)[:12] if text else []
    source_path = str(record.get("source_path") or "")
    if source_path.endswith(".lean") and not theorem_names:
        theorem_names = [Path(source_path).stem]
    return {
        "theorem_names": theorem_names,
        "paper_labels": paper_labels,
    }


def _bridge_consumption_mode(record: dict[str, Any]) -> str:
    kind = str(record.get("source_artifact_kind") or "")
    if kind in {"lean_theorem", "paper_claim"} and _specific_board_claim(record):
        return "board_continuation"
    if kind in {"writeback_packet", "candidate_mechanism"}:
        return "proposal_seed_candidate"
    return "evidence_only"


def _reuse_instruction(mode: str) -> str:
    if mode == "board_continuation":
        return (
            "Inspect and consume existing Automath evidence first; do not rediscover "
            "or re-prove the Automath theorem unless BEDC needs a native restatement."
        )
    if mode == "proposal_seed_candidate":
        return (
            "Use the Automath source as a proposal seed only after BEDC-native intake "
            "confirms a concrete carrier, classifier, proof-obligation, or paper-planning fit."
        )
    return "Record the Automath source as prior evidence only; do not create BEDC theorem work automatically."


def _expected_newmath_delta(record: dict[str, Any], mode: str) -> str:
    if mode == "board_continuation":
        return "minimal BEDC wrapper, native restatement, obstruction, or audit/planning task that cites the Automath evidence packet"
    if mode == "proposal_seed_candidate":
        return "proposal seed or BOARD candidate after native review; no direct paper or Lean write"
    return "notes or manifest-consumed status only"


def _reject_if(record: dict[str, Any], mode: str) -> str:
    if mode == "board_continuation":
        return "no BEDC-native carrier, classifier, proof-obligation shortcut, name-certificate, obstruction, or public-invariant fit"
    if mode == "proposal_seed_candidate":
        return "source lacks a concrete BEDC landing object or duplicates existing BOARD/paper coverage"
    return "evidence is contextual only or cannot be cited by a BEDC-native receiving task"


def _title(record: dict[str, Any]) -> str:
    kind = str(record.get("source_artifact_kind") or "artifact").replace("_", " ")
    path = str(record.get("source_path") or record.get("artifact_key") or "Automath artifact")
    stem = Path(path).stem.replace("_", " ").replace("-", " ").strip()
    if len(stem) > 64:
        stem = stem[:61].rstrip() + "..."
    return f"Automath bridge review: {stem} ({kind})"


def _claim(record: dict[str, Any], packet_rel: str) -> str:
    mode = _bridge_consumption_mode(record)
    refs = _source_refs(record)
    specific = _specific_board_claim(record)
    source = f"{record.get('source_repo')}@{record.get('source_branch_or_ref')}:{record.get('source_path')}"
    theorem_text = ", ".join(refs["theorem_names"]) if refs["theorem_names"] else "(none extracted)"
    label_text = ", ".join(refs["paper_labels"]) if refs["paper_labels"] else "(none extracted)"
    if mode == "board_continuation":
        body = specific or "Determine the minimal BEDC-native object that can consume this Automath evidence."
        return (
            "Bridge continuation target. Automath already supplies prior evidence; "
            "do not restart discovery from scratch.\n\n"
            f"Automath source: `{source}`.\n"
            f"Source commit: `{record.get('source_commit')}`.\n"
            f"Evidence packet: `{packet_rel}`.\n"
            f"Source theorem names: {theorem_text}.\n"
            f"Source paper labels: {label_text}.\n\n"
            f"Continuation task: {body}\n\n"
            "Consume this as one of: existing theorem evidence, candidate mechanism, "
            "proof-obligation shortcut, paper planning source, or reject/blocked because "
            "it is not BEDC-fit. The worker should inspect the Automath theorem/paper "
            "evidence first, then write only the minimal BEDC wrapper/proposal/audit "
            "task needed by NewMath."
        )
    if specific:
        return specific
    evidence = record.get("evidence_summary")
    if not isinstance(evidence, list) or not evidence:
        evidence = [record.get("next_action") or "Automath source evidence is ready for NewMath-side review."]
    evidence_text = "; ".join(str(item) for item in evidence if str(item).strip())
    return (
        "Evaluate whether this Automath artifact should become a BEDC research "
        f"target. Source: {source}. Bridge packet: {packet_rel}. Evidence: "
        f"{evidence_text}. The task is to extract a NewMath-native theorem, "
        "obstruction, or planning target without copying Automath runtime state."
    )


def _specific_board_claim(record: dict[str, Any]) -> str:
    source_path = str(record.get("source_path") or "").lower()
    if "killogodelcompressionnotfiniterankhomologizable" in source_path:
        return (
            "Add a BEDC-side S1 bridge-obligation target that states: any attempted "
            "finite-rank host homologization of the S1 bridge ledger must expose a "
            "bounded-rank certificate, and cofinal prime-support evidence rules out "
            "such a certificate. The target should be phrased as a NewMath/BEDC "
            "obstruction over `papers/bedc/parts/concrete_instances/s1/carrier_readbacks.tex`, "
            "not as an import of the Automath theorem."
        )
    if "killogrothendieckcompletionpreservesinjection" in source_path:
        return (
            "Add a BEDC-side S1 bridge prerequisite target for cancellation in a "
            "Grothendieck-style completion: an injective cancellative additive "
            "source map should remain separated after the displayed completion "
            "representative is used by bridge readback. The target should connect "
            "this to the existing S1 carrier/readback transport rows without using "
            "host quotient primitives as BEDC inputs."
        )
    if "killos4burnsidekanirosenprymsquare" in source_path:
        return (
            "Add a BEDC-side S1 adjacent target asking for a finite representation-ledger "
            "obligation surface for a Prym-square style bridge: explicit induced "
            "representation equalities should be recorded only as paper-level "
            "bridge evidence, while the BEDC target checks which carrier/readback "
            "rows would be needed before such a host comparison can be admitted."
        )
    return ""


def _landing_inputs(record: dict[str, Any]) -> list[str]:
    source_path = str(record.get("source_path") or "").lower()
    if "circledimension" in source_path or "s4burnside" in source_path:
        return ["papers/bedc/parts/concrete_instances/s1/carrier_readbacks.tex"]
    if str(record.get("source_artifact_kind") or "") == "paper_claim":
        return ["papers/bedc/parts/acceptance/02_standard_bridge_protocol.tex"]
    return ["papers/bedc/parts/acceptance/02_standard_bridge_protocol.tex"]


def _candidate(record: dict[str, Any], packet_rel: str) -> dict[str, Any]:
    priority = int(record.get("priority") or 50)
    fit = min(10, max(7, priority // 10))
    novelty = min(10, max(6, (priority + 8) // 10))
    mode = _bridge_consumption_mode(record)
    refs = _source_refs(record)
    return {
        "title": _target_title(record),
        "claim": _claim(record, packet_rel),
        "chapter": "concrete_instances",
        "relation": mode,
        "source": "automath_newmath_bridge",
        "local_inputs": _landing_inputs(record),
        "source_repo": record.get("source_repo"),
        "source_branch_or_ref": record.get("source_branch_or_ref"),
        "bridge_direction": record.get("bridge_direction"),
        "bridge_consumption_mode": mode,
        "bridge_evidence_packet": packet_rel,
        "source_theorem_names": refs["theorem_names"],
        "source_paper_labels": refs["paper_labels"],
        "source_commit": record.get("source_commit"),
        "source_paths": [record.get("source_path")],
        "reuse_instruction": _reuse_instruction(mode),
        "expected_newmath_delta": _expected_newmath_delta(record, mode),
        "reject_if": _reject_if(record, mode),
        "rationale": (
            "Automath-to-NewMath bridge gate passed as an evidence-backed continuation "
            "candidate. BEDC board_spawn must still judge fit, novelty, dedup, and "
            "paper coverage before BOARD append. Use Automath source as prior evidence; "
            "do not re-prove it unless BEDC needs a native restatement. "
            f"source_repo={record.get('source_repo')}; "
            f"source_commit={record.get('source_commit')}; "
            f"bridge_direction={record.get('bridge_direction')}; "
            f"bridge_consumption_mode={mode}. "
            f"The bridge evidence packet is {packet_rel}. "
            f"Expected NewMath delta: {_expected_newmath_delta(record, mode)}. "
            f"Reject if: {_reject_if(record, mode)}."
        ),
        "fit_score": fit,
        "novelty": novelty,
    }


def _target_title(record: dict[str, Any]) -> str:
    source_path = str(record.get("source_path") or "").lower()
    if "killogodelcompressionnotfiniterankhomologizable" in source_path:
        return "S1 finite-rank host homologization obstruction"
    if "killogrothendieckcompletionpreservesinjection" in source_path:
        return "S1 completion-readback injectivity prerequisite"
    if "killos4burnsidekanirosenprymsquare" in source_path:
        return "S1 Prym-square representation ledger bridge target"
    return _title(record)


def _existing_board_titles() -> set[str]:
    sys.path.insert(0, str(BEDC_DEEP_DIR))
    import board_archive  # type: ignore

    return board_archive.existing_target_titles(include_archive=True)


def _eligible(record: dict[str, Any]) -> bool:
    return _eligibility_skip_reason(record) == ""


def _eligibility_skip_reason(record: dict[str, Any]) -> str:
    if record.get("bridge_direction") != "automath_to_newmath":
        return "not_automath_to_newmath"
    if record.get("gate_status") != "gate_passed":
        return str(record.get("gate_status") or "gate_not_passed")
    if record.get("readiness") not in {"ready_for_local_packet", "needs_operator_review"}:
        return f"readiness:{record.get('readiness')}"
    if record.get("destination_repo") != "the-omega-institute/newmath":
        return "wrong_destination_repo"
    source_kind = str(record.get("source_artifact_kind") or "")
    if source_kind not in {
        "lean_theorem",
        "paper_claim",
        "writeback_packet",
        "candidate_mechanism",
        "audit_failure",
    }:
        return f"evidence_only:{source_kind or 'unknown_kind'}"
    if source_kind == "paper_claim" and not _specific_board_claim(record):
        return "no_specific_board_claim"
    return ""


def build_candidates(
    records: list[dict[str, Any]],
    *,
    packet_dir: Path,
    limit: int,
    write_packets: bool,
) -> tuple[list[dict[str, Any]], list[dict[str, Any]], list[Path], list[str], list[dict[str, Any]]]:
    candidates: list[dict[str, Any]] = []
    candidate_source_records: list[dict[str, Any]] = []
    packets: list[Path] = []
    skipped_duplicate_titles: list[str] = []
    skipped_ack_records: list[dict[str, Any]] = []
    existing_titles = _existing_board_titles()
    history = _bridge_candidate_history()
    for record in records:
        if len(candidates) >= limit:
            break
        if not _eligible(record):
            continue
        title = _target_title(record)
        if title.strip().lower() in existing_titles:
            skipped_duplicate_titles.append(title)
            skipped_ack_records.append(_ack_record(record, None, status="consumed", reason="duplicate_board_title", target_id=""))
            continue
        history_reason = _history_skip_reason(title, history)
        if history_reason:
            skipped_duplicate_titles.append(f"{title} ({history_reason})")
            status = "consumed" if history_reason.startswith("already_promoted:") else "blocked"
            target_id = history_reason.split(":", 1)[1] if history_reason.startswith("already_promoted:") else ""
            skipped_ack_records.append(_ack_record(record, None, status=status, reason=history_reason, target_id=target_id))
            continue
        packet_path = _write_packet(record, packet_dir) if write_packets else _packet_path(record, packet_dir)
        packet_rel = str(packet_path.relative_to(REPO_ROOT))
        packets.append(packet_path)
        candidates.append(_candidate(record, packet_rel))
        candidate_source_records.append(record)
        existing_titles.add(title.strip().lower())
    return candidates, candidate_source_records, packets, skipped_duplicate_titles, skipped_ack_records


def run_board_spawn(candidates: list[dict[str, Any]], *, fit_threshold: int, novelty_threshold: int) -> Any:
    sys.path.insert(0, str(BEDC_DEEP_DIR))
    import board_spawn  # type: ignore

    return board_spawn.spawn_from_candidates(
        codex_candidates=candidates,
        oracle_candidates=[],
        fit_threshold=fit_threshold,
        novelty_threshold=novelty_threshold,
    )


def _accepted_packet_rels(result: Any) -> set[str]:
    accepted = getattr(result, "accepted", []) or []
    rels: set[str] = set()
    for item in accepted:
        if not isinstance(item, dict):
            continue
        inputs = item.get("local_inputs") or []
        if isinstance(inputs, str):
            inputs = [inputs]
        for rel in inputs:
            text = str(rel).strip()
            if text.startswith("tools/automath_newmath_bridge/review_packets/"):
                rels.add(text)
        packet_rel = str(item.get("bridge_evidence_packet") or "").strip()
        if packet_rel.startswith("tools/automath_newmath_bridge/review_packets/"):
            rels.add(packet_rel)
    return rels


def _render_ledger(summary: dict[str, Any], candidates: list[dict[str, Any]]) -> str:
    lines = [
        "# Automath BOARD Continuation Ledger",
        "",
        "This durable ledger records Automath-to-NewMath bridge candidates that were shaped as evidence-backed BEDC continuation targets.",
        "Runtime inbox, state, logs, and raw gate output remain untracked.",
        "",
        "| Metric | Value |",
        "| --- | --- |",
        f"| Apply | `{summary.get('apply')}` |",
        f"| Eligible candidates | `{summary.get('eligible_candidates')}` |",
        f"| Accepted into BOARD | `{summary.get('accepted_count', 0)}` |",
        f"| Rejected | `{summary.get('rejected_count', 0)}` |",
        f"| Appended ids | `{', '.join(summary.get('appended_ids') or []) or 'none'}` |",
        f"| Judge backend | `{summary.get('judge_backend', '')}` |",
        "",
        "## Candidate Modes",
        "",
        "| Title | Mode | Source commit | Source paths | Evidence packet | Expected NewMath delta |",
        "| --- | --- | --- | --- | --- | --- |",
    ]
    if not candidates:
        lines.append("| _none_ |  |  |  |  |  |")
    for candidate in candidates:
        title = str(candidate.get("title") or "").replace("|", "\\|")
        paths = ", ".join(str(p) for p in candidate.get("source_paths") or [])
        delta = str(candidate.get("expected_newmath_delta") or "").replace("|", "\\|")
        lines.append(
            "| `{}` | `{}` | `{}` | `{}` | `{}` | {} |".format(
                title,
                candidate.get("bridge_consumption_mode", ""),
                candidate.get("source_commit", ""),
                paths,
                candidate.get("bridge_evidence_packet", ""),
                delta,
            )
        )
    lines.extend(
        [
            "",
            "## Policy",
            "",
            "- `evidence_only` records are reference material; they should not create BEDC theorem work automatically.",
            "- `board_continuation` records enter BOARD only as continuation targets with Automath evidence packets.",
            "- `proposal_seed_candidate` records may seed a BEDC-native proposal, but still go through native intake gates.",
            "- BEDC workers should inspect the Automath evidence first and write only the minimal BEDC-native wrapper, proposal, audit task, or rejection reason.",
            f"- Machine-readable ACK/NACK status is appended to `{summary.get('ack_ledger', '')}`.",
        ]
    )
    return "\n".join(lines) + "\n"


def _write_ledger(path: Path, summary: dict[str, Any], candidates: list[dict[str, Any]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(_render_ledger(summary, candidates), encoding="utf-8")


def _ack_record(
    record: dict[str, Any],
    candidate: dict[str, Any] | None,
    *,
    status: str,
    reason: str,
    target_id: str,
) -> dict[str, Any]:
    candidate_paths = (candidate or {}).get("source_paths")
    candidate_path = candidate_paths[0] if isinstance(candidate_paths, list) and candidate_paths else ""
    source_path = str(record.get("source_path") or candidate_path)
    source_commit = str(record.get("source_commit") or (candidate or {}).get("source_commit") or "")
    source_repo = str(record.get("source_repo") or (candidate or {}).get("source_repo") or "the-omega-institute/automath")
    source_ref = str(record.get("source_branch_or_ref") or (candidate or {}).get("source_branch_or_ref") or "")
    bridge_id = hashlib.sha1(f"{source_repo}|{source_ref}|{source_commit}|{source_path}".encode("utf-8")).hexdigest()[:16]
    return {
        "schema_version": "automath-newmath-bridge-ack-v1",
        "created_at": _now_iso(),
        "bridge_id": bridge_id,
        "bridge_direction": "automath_to_newmath",
        "source_repo": source_repo,
        "source_branch_or_ref": source_ref,
        "source_commit": source_commit,
        "source_path": source_path,
        "source_artifact_kind": record.get("source_artifact_kind"),
        "destination_repo": "the-omega-institute/newmath",
        "destination_branch_or_ref": "bedc-claim-packet-pipeline",
        "destination_path": "tools/bedc-deep/BOARD.md",
        "destination_artifact_kind": "open_problem_target",
        "bridge_consumption_mode": (candidate or {}).get("bridge_consumption_mode") or _bridge_consumption_mode(record),
        "status": status,
        "target_id": target_id,
        "evidence_packet": (candidate or {}).get("bridge_evidence_packet", ""),
        "operator_review_required": True,
        "taste_gate_required": False,
        "audit_required": True,
        "reason": reason,
        "notes": "Durable bridge acknowledgement; runtime packets/logs are intentionally not embedded.",
        "next_action": "Automath may mark the source consumed, blocked, or still review-only according to this acknowledgement.",
    }


def _append_ack_ledger(path: Path, records: list[dict[str, Any]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    if not records:
        path.touch(exist_ok=True)
        return
    existing: set[tuple[str, str, str]] = set()
    if path.exists():
        for line in path.read_text(encoding="utf-8", errors="replace").splitlines():
            try:
                item = json.loads(line)
            except json.JSONDecodeError:
                continue
            if isinstance(item, dict):
                existing.add((str(item.get("bridge_id", "")), str(item.get("status", "")), str(item.get("target_id", ""))))
    with path.open("a", encoding="utf-8") as handle:
        for record in records:
            key = (str(record.get("bridge_id", "")), str(record.get("status", "")), str(record.get("target_id", "")))
            if key in existing:
                continue
            handle.write(json.dumps(record, ensure_ascii=False, sort_keys=True) + "\n")
            existing.add(key)


def _screening_ack_records(records: list[dict[str, Any]]) -> list[dict[str, Any]]:
    ack_records: list[dict[str, Any]] = []
    for record in records:
        if record.get("bridge_direction") != "automath_to_newmath":
            continue
        reason = _eligibility_skip_reason(record)
        if not reason:
            continue
        if reason.startswith("evidence_only:"):
            status = "evidence_only"
            next_action = "Retain as bridge evidence only; do not spawn BEDC theorem work automatically."
        else:
            status = "blocked"
            next_action = "Tighten the Automath evidence packet with a concrete BEDC landing object before retry."
        ack_records.append(
            _ack_record(
                record,
                None,
                status=status,
                reason=reason,
                target_id="",
            )
            | {"next_action": next_action}
        )
    return ack_records


def _ack_records_from_result(result: Any, candidates: list[dict[str, Any]], source_records: list[dict[str, Any]]) -> list[dict[str, Any]]:
    by_title = {str(candidate.get("title") or "").strip().lower(): (candidate, source_records[idx]) for idx, candidate in enumerate(candidates)}
    ack_records: list[dict[str, Any]] = []
    for item in getattr(result, "accepted", []) or []:
        if not isinstance(item, dict):
            continue
        title = str(item.get("title") or "").strip().lower()
        candidate, source_record = by_title.get(title, ({}, {}))
        target_ids = item.get("target_id") or item.get("id") or ""
        if not target_ids:
            ids = getattr(result, "appended_ids", []) or []
            target_ids = ",".join(str(value) for value in ids)
        ack_records.append(_ack_record(source_record, candidate, status="consumed", reason="accepted_into_bedc_board", target_id=str(target_ids)))
    for item in getattr(result, "rejected", []) or []:
        if not isinstance(item, dict):
            continue
        title = str(item.get("title") or "").strip().lower()
        candidate, source_record = by_title.get(title, ({}, {}))
        reason = str(item.get("reason") or item.get("verdict_reason") or "bedc_board_rejected")
        ack_records.append(_ack_record(source_record, candidate, status="blocked", reason=reason, target_id=""))
    return ack_records


def _render_status_report(
    summary: dict[str, Any],
    ack_records: list[dict[str, Any]],
) -> str:
    status_counts: dict[str, int] = {}
    reason_counts: dict[str, int] = {}
    source_commits: dict[str, int] = {}
    for record in ack_records:
        status = str(record.get("status") or "unknown")
        reason = str(record.get("reason") or "none")
        source_commit = str(record.get("source_commit") or "unknown")
        status_counts[status] = status_counts.get(status, 0) + 1
        reason_counts[reason] = reason_counts.get(reason, 0) + 1
        source_commits[source_commit] = source_commits.get(source_commit, 0) + 1

    if int(summary.get("eligible_candidates") or 0) > 0:
        production_reason = "candidate_output_available"
    elif int(summary.get("skipped_duplicate_title_count") or 0) > 0:
        production_reason = "all_specific_board_candidates_duplicate_or_history_rejected"
    elif any(str(record.get("reason") or "") == "no_specific_board_claim" for record in ack_records):
        production_reason = "automath_evidence_lacks_specific_bedc_continuation_claim"
    elif ack_records:
        production_reason = "screened_to_ack_or_evidence_only"
    else:
        production_reason = "no_automath_to_newmath_gate_rows"

    lines = [
        "# Automath-NewMath Production Status",
        "",
        "This durable status explains why the bridge did or did not produce new BEDC BOARD continuation output.",
        "Runtime inbox, state, raw gate output, and logs remain untracked.",
        "",
        "| Metric | Value |",
        "| --- | --- |",
        f"| Production reason | `{production_reason}` |",
        f"| Apply BOARD ingest | `{summary.get('apply')}` |",
        f"| Eligible BOARD candidates this pass | `{summary.get('eligible_candidates')}` |",
        f"| Duplicate/history-skipped titles | `{summary.get('skipped_duplicate_title_count', 0)}` |",
        f"| Accepted into BOARD | `{summary.get('accepted_count', 0)}` |",
        f"| Rejected by BOARD | `{summary.get('rejected_count', 0)}` |",
        f"| ACK rows emitted this pass | `{len(ack_records)}` |",
        "",
        "## Status Counts",
        "",
        "| Status | Count |",
        "| --- | ---: |",
    ]
    for status, count in sorted(status_counts.items()):
        lines.append(f"| `{status}` | {count} |")
    lines.extend(["", "## Reason Counts", "", "| Reason | Count |", "| --- | ---: |"])
    for reason, count in sorted(reason_counts.items()):
        lines.append(f"| `{reason}` | {count} |")
    lines.extend(["", "## Source Commits", "", "| Commit | Rows |", "| --- | ---: |"])
    for source_commit, count in sorted(source_commits.items()):
        lines.append(f"| `{source_commit}` | {count} |")
    lines.extend(
        [
            "",
            "## Production Discipline",
            "",
            "- BOARD entries must be evidence-backed continuation targets, not vague requests to research Automath again.",
            "- `evidence_only` rows are acknowledged for Automath feedback but do not spawn BEDC theorem work.",
            "- `blocked` rows tell Automath why a candidate did not become a BEDC continuation target.",
            "- New production requires either a new source commit, a sharper source-specific BEDC landing object, or a BEDC ACK that changes the retry priority.",
            "",
        ]
    )
    return "\n".join(lines)


def _write_status_report(path: Path, summary: dict[str, Any], ack_records: list[dict[str, Any]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(_render_status_report(summary, ack_records), encoding="utf-8")


def _cleanup_unaccepted_packets(packet_paths: list[Path], accepted_rels: set[str]) -> list[str]:
    removed: list[str] = []
    for path in packet_paths:
        try:
            rel = str(path.relative_to(REPO_ROOT))
        except ValueError:
            continue
        if rel in accepted_rels:
            continue
        try:
            path.unlink()
        except FileNotFoundError:
            pass
        else:
            removed.append(rel)
    return removed


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Bridge Automath gate results into BEDC BOARD candidates")
    parser.add_argument("--gate-results", default=str(DEFAULT_GATE_RESULTS))
    parser.add_argument("--packet-dir", default=str(DEFAULT_PACKET_DIR))
    parser.add_argument("--limit", type=int, default=3)
    parser.add_argument("--fit-threshold", type=int, default=7)
    parser.add_argument("--novelty-threshold", type=int, default=6)
    parser.add_argument("--apply", action="store_true", help="Run BEDC board_spawn and allow BOARD append")
    parser.add_argument(
        "--write-packets",
        action="store_true",
        help="Write durable review packet JSON files without applying BOARD ingest",
    )
    parser.add_argument("--ledger", default=str(DEFAULT_LEDGER), help="Durable continuation ledger path")
    parser.add_argument("--ack-ledger", default=str(DEFAULT_ACK_LEDGER), help="Durable ACK/NACK JSONL ledger path")
    parser.add_argument("--status-report", default=str(DEFAULT_STATUS_REPORT), help="Durable production status Markdown path")
    parser.add_argument("--no-ledger", action="store_true", help="Do not write durable continuation ledger")
    parser.add_argument("--no-ack-ledger", action="store_true", help="Do not write durable ACK/NACK JSONL")
    parser.add_argument("--no-status-report", action="store_true", help="Do not write durable production status Markdown")
    args = parser.parse_args(argv)

    records = _read_jsonl(Path(args.gate_results))
    candidates, candidate_source_records, packets, skipped_duplicate_titles, skipped_ack_records = build_candidates(
        records,
        packet_dir=Path(args.packet_dir),
        limit=max(0, args.limit),
        write_packets=bool(args.apply or args.write_packets),
    )
    summary: dict[str, Any] = {
        "eligible_candidates": len(candidates),
        "skipped_duplicate_titles": skipped_duplicate_titles,
        "skipped_duplicate_title_count": len(skipped_duplicate_titles),
        "packet_paths": [str(path.relative_to(REPO_ROOT)) for path in packets],
        "apply": bool(args.apply),
        "ack_ledger": str(Path(args.ack_ledger).relative_to(REPO_ROOT)) if Path(args.ack_ledger).is_relative_to(REPO_ROOT) else str(args.ack_ledger),
    }
    if not candidates:
        ack_records = skipped_ack_records + _screening_ack_records(records)
        summary["ack_count"] = len(ack_records)
        if not args.no_ledger:
            _write_ledger(Path(args.ledger), summary, candidates)
        if not args.no_ack_ledger:
            _append_ack_ledger(Path(args.ack_ledger), ack_records)
        if not args.no_status_report:
            _write_status_report(Path(args.status_report), summary, ack_records)
        print(json.dumps(summary, ensure_ascii=False, indent=2, sort_keys=True))
        return 0
    if args.apply:
        result = run_board_spawn(
            candidates,
            fit_threshold=args.fit_threshold,
            novelty_threshold=args.novelty_threshold,
        )
        summary.update(
            {
                "board_spawn_ok": bool(getattr(result, "ok", False)),
                "appended_ids": list(getattr(result, "appended_ids", []) or []),
                "accepted_count": len(getattr(result, "accepted", []) or []),
                "rejected_count": len(getattr(result, "rejected", []) or []),
                "error": getattr(result, "error", ""),
                "judge_backend": getattr(result, "judge_backend", ""),
                "judge_note": getattr(result, "judge_note", ""),
                "rejection_reasons": [
                    str(item.get("reason") or item.get("verdict_reason") or "")
                    for item in (getattr(result, "rejected", []) or [])
                    if isinstance(item, dict)
                ][:20],
            }
        )
        accepted_rels = _accepted_packet_rels(result)
        summary["removed_unaccepted_packets"] = _cleanup_unaccepted_packets(packets, accepted_rels)
        ack_records = skipped_ack_records + _ack_records_from_result(result, candidates, candidate_source_records) + _screening_ack_records(records)
        summary["ack_count"] = len(ack_records)
        if not args.no_ledger:
            _write_ledger(Path(args.ledger), summary, candidates)
        if not args.no_ack_ledger:
            _append_ack_ledger(Path(args.ack_ledger), ack_records)
        if not args.no_status_report:
            _write_status_report(Path(args.status_report), summary, ack_records)
        print(json.dumps(summary, ensure_ascii=False, indent=2, sort_keys=True))
        return 0 if getattr(result, "ok", False) else 1
    summary["dry_run_candidates"] = candidates
    ack_records = skipped_ack_records + _screening_ack_records(records)
    summary["ack_count"] = len(ack_records)
    if not args.no_ledger:
        _write_ledger(Path(args.ledger), summary, candidates)
    if not args.no_status_report:
        _write_status_report(Path(args.status_report), summary, ack_records)
    print(json.dumps(summary, ensure_ascii=False, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
